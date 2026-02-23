import csv
import re
import json
import os
import time
import calendar as cal
from datetime import datetime, date, timedelta
import tkinter as tk
from tkinter import ttk, colorchooser, messagebox, filedialog, simpledialog


# --- Per-user writable data directory (AppData) ---
from pathlib import Path

def _get_app_data_dir(app_name: str = "ProcApp"):
    """Return per-user writable data directory."""
    if os.name == "nt":
        base = os.environ.get("APPDATA") or str(Path.home() / "AppData" / "Roaming")
        p = Path(base) / app_name
    else:
        p = Path.home() / ".local" / "share" / app_name
    p.mkdir(parents=True, exist_ok=True)
    return p

APP_DATA_DIR = _get_app_data_dir("ProcApp")

APP_TITLE = "Procrastination Checker (Adaptive + Stats, Local)"
LOG_FILE = str(APP_DATA_DIR / "procrastination_log.csv")
STATE_FILE = str(APP_DATA_DIR / "pc_state.json")
NOTES_FILE = str(APP_DATA_DIR / "notes_by_date.json")

DEFAULT_INTERVAL_MIN = 10
MIN_INTERVAL = 3
MAX_INTERVAL = 30
STEP_UP = 2
STEP_DOWN = 3
STREAK_FOR_STEPUP = 2

BEEP_COUNT = 2
BEEP_GAP_MS = 150


def now_iso():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def clamp(v, lo, hi):
    return max(lo, min(hi, v))


def parse_ts(ts: str) -> datetime:
    return datetime.strptime(ts, "%Y-%m-%d %H:%M:%S")


def day_key(dt: datetime) -> str:
    return dt.strftime("%Y-%m-%d")


def safe_int_from_note(note: str, key: str):
    if not note:
        return None
    parts = note.replace(",", " ").split()
    for p in parts:
        if p.startswith(key + "="):
            try:
                return int(p.split("=", 1)[1])
            except Exception:
                return None
    return None


def monday_of(d: date) -> date:
    return d - timedelta(days=d.weekday())


class StatsEngine:
    def __init__(self, log_path: str):
        self.log_path = log_path
        self.events = []

    def load(self):
        self.events = []
        if not os.path.exists(self.log_path):
            return
        with open(self.log_path, "r", encoding="utf-8", newline="") as f:
            r = csv.DictReader(f)
            for row in r:
                ts = row.get("timestamp", "")
                try:
                    dt = parse_ts(ts)
                except Exception:
                    continue
                self.events.append({
                    "dt": dt,
                    "day": day_key(dt),
                    "event": (row.get("event", "") or "").strip(),
                    "task": (row.get("task", "") or "").strip(),
                    "secs": int(row.get("session_seconds", "0") or 0),
                    "note": row.get("note", "") or "",
                    "timestamp": ts,
                })
        self.events.sort(key=lambda e: e["dt"])

    def days_present(self):
        return sorted({e["day"] for e in self.events})

    def events_for_day(self, d: str):
        return [e for e in self.events if e["day"] == d]

    def events_in_range(self, start_day: str, end_day: str):
        return [e for e in self.events if start_day <= e["day"] <= end_day]

    def summary_for_day(self, d: str):
        evs = self.events_for_day(d)
        on_min = off_min = 0
        checkins_on = checkins_off = 0
        pro_count = starts = stops = cancels = completes = breaks = 0

        for e in evs:
            evt = e["event"]
            interval = safe_int_from_note(e["note"] or "", "interval_min")

            if evt == "checkin_on_task":
                checkins_on += 1
                if interval:
                    on_min += interval
            elif evt == "checkin_off_task":
                checkins_off += 1
                if interval:
                    off_min += interval
            elif evt == "procrastination":
                pro_count += 1
                if interval:
                    off_min += interval
            elif evt == "start":
                starts += 1
            elif evt == "stop":
                stops += 1
            elif evt == "cancel":
                cancels += 1
            elif evt == "session_complete":
                completes += 1
                stops += 1  # treat as stop for summary totals
            elif evt == "break":
                breaks += 1

        total = on_min + off_min
        ratio = (on_min / total) if total > 0 else None
        return {
            "day": d,
            "on_min": on_min,
            "off_min": off_min,
            "total_min": total,
            "ratio_on": ratio,
            "checkins_on": checkins_on,
            "checkins_off": checkins_off,
            "procrastinations": pro_count,
            "starts": starts,
            "stops": stops,
            "cancels": cancels,
            "completes": completes,
            "breaks": breaks,
        }

    def week_days(self, anchor: date):
        wk_start = monday_of(anchor)
        return [(wk_start + timedelta(days=i)).strftime("%Y-%m-%d") for i in range(7)]

    def week_summary(self, anchor: date):
        days = self.week_days(anchor)
        per_day = [self.summary_for_day(d) for d in days]
        return days, per_day

    def on_off_by_task_in_range(self, start_day: str, end_day: str):
        on_by = {}
        off_by = {}
        evs = self.events_in_range(start_day, end_day)
        for e in evs:
            evt = e["event"]
            task = (e["task"] or "").strip() or "(no task)"
            interval = safe_int_from_note(e["note"] or "", "interval_min")
            if not interval:
                continue
            if evt == "checkin_on_task":
                on_by[task] = on_by.get(task, 0) + interval
            elif evt in ("checkin_off_task", "procrastination"):
                off_by[task] = off_by.get(task, 0) + interval

        tasks = sorted(set(on_by) | set(off_by))
        rows = []
        for t in tasks:
            onm = on_by.get(t, 0)
            offm = off_by.get(t, 0)
            total = onm + offm
            onp = (onm / total) if total else None
            rows.append((t, onm, offm, total, onp))
        rows.sort(key=lambda r: (r[3], r[1]), reverse=True)
        return rows

    def sessions_by_task_in_range(self, start_day: str, end_day: str):
        """
        Aggregate completed work sessions by task for the given day range.

        IMPORTANT:
        - Count a "session" ONLY when we log a 'stop' (completed / ended session).
        - 'cancel' is tracked separately and does NOT count as a completed session.
        - We ignore 'session_complete' entirely to avoid double counting (older logs may contain it).
        """
        evs = self.events_in_range(start_day, end_day)

        by = {}
        for e in evs:
            evt = e.get("event")
            if evt not in ("stop", "cancel"):
                continue

            task = (e.get("task") or "").strip() or "(no task)"
            rec = by.setdefault(task, {"sessions": 0, "total_secs": 0, "cancels": 0})

            if evt == "stop":
                rec["sessions"] += 1
                try:
                    rec["total_secs"] += int(e.get("secs", 0) or 0)
                except Exception:
                    pass
            elif evt == "cancel":
                rec["cancels"] += 1

        rows = []
        for task, rec in by.items():
            sessions = int(rec.get("sessions", 0) or 0)
            total_secs = int(rec.get("total_secs", 0) or 0)
            avg = (total_secs / sessions) if sessions > 0 else None
            rows.append((task, sessions, total_secs, avg, int(rec.get("cancels", 0) or 0)))
        rows.sort(key=lambda r: (r[2], r[1]), reverse=True)
        return rows

    def session_stats_in_range(self, start_day: str, end_day: str):
        """
        Return (avg_session_secs, cancel_rate, avg_time_to_first_procrastination_secs) in a date range.

        Notes:
        - We treat 'stop' as the only completed session end.
        - We treat 'cancel' as a cancel end.
        - We ignore 'session_complete' to avoid double counting.
        """
        evs = self.events_in_range(start_day, end_day)

        ends = [e for e in evs if e.get("event") in ("stop", "cancel")]

        if ends:
            avg_secs = sum(max(0, e.get("secs", 0) or 0) for e in ends if e.get("event") == "stop") / max(
                1, len([e for e in ends if e.get("event") == "stop"])
            ) if any(e.get("event") == "stop" for e in ends) else None
        else:
            avg_secs = None

        cancels = [e for e in ends if e.get("event") == "cancel"]
        cancel_rate = (len(cancels) / len(ends)) if ends else None

        # Time-to-first-procrastination after each start, measured in secs column of the procrastination event
        tt_first = []
        i = 0
        while i < len(evs):
            if evs[i].get("event") != "start":
                i += 1
                continue
            j = i + 1
            first = None
            while j < len(evs) and evs[j].get("event") not in ("stop", "cancel", "start"):
                if evs[j].get("event") == "procrastination":
                    first = evs[j].get("secs", 0) or 0
                    break
                j += 1
            if first is not None:
                tt_first.append(first)
            while j < len(evs) and evs[j].get("event") not in ("stop", "cancel", "start"):
                j += 1
            i = j + 1 if j > i else i + 1

        avg_tt = (sum(tt_first) / len(tt_first)) if tt_first else None
        return avg_secs, cancel_rate, avg_tt

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1040x700")
        self.minsize(860, 560)

        self.active_task = tk.StringVar(value="Deep work")
        self.status = tk.StringVar(value="Idle")

        self.session_start_ts = None
        self.session_elapsed = 0.0
        self.last_tick = None

        self.prompt_enabled = tk.BooleanVar(value=True)
        self.topmost_prompt = tk.BooleanVar(value=True)
        self.beep_enabled = tk.BooleanVar(value=True)

        self.target_duration_min = tk.IntVar(value=30)
        self.auto_stop_enabled = tk.BooleanVar(value=True)

        self.current_interval_min = tk.IntVar(value=DEFAULT_INTERVAL_MIN)
        self.next_prompt_at = None

        self._refresh_job = None
        self._notes_save_job = None

        self.state = self._load_state()
        self.notes_map = self._load_notes()

        ui = self.state.setdefault("ui", {})
        if "mode" not in ui:
            ui["mode"] = "Light"
        self.ui_mode = tk.StringVar(value=str(ui.get("mode", "Light")))

        # Break tracking
        self.on_break = False
        self.break_start_ts = None
        self.break_elapsed = 0.0
        self.break_last_tick = None

        # Restore window geometry (saved in state)
        try:
            geom = ui.get("window_geometry")
            if geom:
                self.geometry(geom)
            if ui.get("window_zoomed"):
                try:
                    self.state('zoomed')
                except Exception:
                    pass
        except Exception:
            pass

        self._geom_save_job = None
        self.bind('<Configure>', self._on_window_configure)
        self.protocol('WM_DELETE_WINDOW', self._on_close)

        self._ensure_log_header()

        self.stats = StatsEngine(LOG_FILE)
        self._init_indicator_images()

        self.selected_day = tk.StringVar(value=date.today().strftime("%Y-%m-%d"))
        self.calendar_year = date.today().year
        self.calendar_month = date.today().month

        self.rundown_task_filter = tk.StringVar(value="All tasks")
        self.rundown_event_filter = tk.StringVar(value="All events")

        # caches for redraw-on-resize
        self._last_summary_onoff = (0, 0)
        self._last_week_days = None
        self._last_week_per_day = None

        self._setup_style()
        self._build_ui()

        self.active_task.trace_add('write', lambda *_args: self._on_active_task_changed())

        self._refresh_stats()
        self._tick()

    # ---------- Persistence ----------
    def _load_state(self):
        if os.path.exists(STATE_FILE):
            try:
                with open(STATE_FILE, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
        return {"tasks": {}, "ui": {"mode": "Light"}}

    def _save_state(self):
        try:
            with open(STATE_FILE, "w", encoding="utf-8") as f:
                json.dump(self.state, f, ensure_ascii=False, indent=2)
        except Exception:
            pass


    def _get_ui_state(self):
        return self.state.setdefault("ui", {})

    def _save_left_sashpos(self, pos: int):
        ui = self._get_ui_state()
        ui["stats_left_sashpos"] = int(pos)
        self._save_state()

    def _on_window_configure(self, _e=None):
        # Debounced geometry persistence
        if self._geom_save_job is not None:
            try:
                self.after_cancel(self._geom_save_job)
            except Exception:
                pass
        self._geom_save_job = self.after(400, self._save_window_geometry)

    def _save_window_geometry(self):
        self._geom_save_job = None
        try:
            ui = self._get_ui_state()
            ui["window_geometry"] = self.geometry()
            # Track maximized state on Windows
            try:
                ui["window_zoomed"] = (str(self.state()) == 'zoomed')
            except Exception:
                pass
            self._save_state()
        except Exception:
            pass

    def _on_close(self):
        try:
            self._save_window_geometry()
        except Exception:
            pass
        self.destroy()

    def _task_state(self, task: str):
        tasks = self.state.setdefault("tasks", {})
        if task not in tasks:
            tasks[task] = {"interval_min": DEFAULT_INTERVAL_MIN, "yes_streak": 0, "color": "#dfe8ff"}
            self._save_state()
        if "color" not in tasks[task]:
            tasks[task]["color"] = "#dfe8ff"
        return tasks[task]

    def _load_notes(self):
        if os.path.exists(NOTES_FILE):
            try:
                with open(NOTES_FILE, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    return data
            except Exception:
                return {}
        return {}

    def _save_notes(self):
        try:
            with open(NOTES_FILE, "w", encoding="utf-8") as f:
                json.dump(self.notes_map, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _schedule_save_current_note(self):
        if self._notes_save_job is not None:
            try:
                self.after_cancel(self._notes_save_job)
            except Exception:
                pass
        self._notes_save_job = self.after(400, self._save_current_note)

    def _load_current_note(self):
        ds = self.selected_day.get()
        txt = self.notes_map.get(ds, "")
        if hasattr(self, "notes_text"):
            self.notes_text.delete("1.0", "end")
            self.notes_text.insert("1.0", txt)

    def _save_current_note(self):
        self._notes_save_job = None
        ds = self.selected_day.get()
        if hasattr(self, "notes_text"):
            self.notes_map[ds] = self.notes_text.get("1.0", "end").rstrip()
            self._save_notes()

    # ---------- Logging ----------
    def _ensure_log_header(self):
        if not os.path.exists(LOG_FILE):
            with open(LOG_FILE, "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                w.writerow(["timestamp", "event", "task", "session_seconds", "note"])

    def _append_log(self, event: str, note: str = "", secs_override: int = None, task_override: str = None):
        task = (task_override if task_override is not None else self.active_task.get().strip())
        if secs_override is None:
            secs = int(self.session_elapsed) if self.session_start_ts else 0
        else:
            secs = int(max(0, secs_override))
        with open(LOG_FILE, "a", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow([now_iso(), event, task, secs, note])

    # ---------- Style ----------
    def _setup_style(self):
        style = ttk.Style(self)
        mode = (getattr(self, "ui_mode", None).get() if getattr(self, "ui_mode", None) else "Light")
        themes = set(style.theme_names())
        want = "clam" if mode == "Light" else ("vista" if "vista" in themes else ("xpnative" if "xpnative" in themes else "default"))
        try:
            if want in themes:
                style.theme_use(want)
        except Exception:
            pass

        if mode == "Light":
            try:
                style.configure(".", background="#f7f7f7")
                style.configure("TFrame", background="#f7f7f7")
                style.configure("TLabelFrame", background="#f7f7f7")
                style.configure("TLabelFrame.Label", background="#f7f7f7")
            except Exception:
                pass

        # Re-apply base styling AFTER theme selection (themes can override earlier config)
        style.configure(".", font=("Segoe UI", 10))
        style.configure("TLabelframe.Label", font=("Segoe UI", 10, "bold"))
        style.configure("Labelframe.Label", font=("Segoe UI", 10, "bold"))
        style.configure("TLabelFrame.Label", font=("Segoe UI", 10, "bold"))
        style.configure("TLabelframe", padding=(10, 8))

        style.configure("Title.TLabel", font=("Segoe UI", 12, "bold"))
        style.configure("Timer.TLabel", font=("Consolas", 24))
        style.configure("Status.TLabel", font=("Segoe UI", 10))

        style.configure("Start.TButton", padding=(14, 8), foreground="white", background="#2e7d32")
        style.map("Start.TButton", background=[("active", "#388e3c")])
        style.configure("Stop.TButton", padding=(14, 8), foreground="white", background="#c62828")
        style.map("Stop.TButton", background=[("active", "#d32f2f")])

        style.configure("Cancel.TButton", padding=(14, 8), foreground="#111111", background="#e0e0e0")
        style.map("Cancel.TButton", background=[("active", "#d5d5d5")])

        style.configure("Procrastinate.TButton", padding=(14, 8), foreground="#111111", background="#ffd54f")
        style.map("Procrastinate.TButton", background=[("active", "#ffca28")])

        style.configure("Secondary.TButton", padding=(12, 8))

        try:
            style.configure("Green.Horizontal.TProgressbar", troughcolor="#e0e0e0", background="#4caf50")
        except Exception:
            pass

        for name, bg in [
            ("DayNone.TButton", "#eeeeee"),
            ("DayLow.TButton", "#ffcdd2"),
            ("DayMid.TButton", "#ffe0b2"),
            ("DayHigh.TButton", "#c8e6c9"),
        ]:
            style.configure(name, padding=(6, 2), background=bg)
            style.map(name, background=[("active", bg)])

    def _apply_ui_mode(self, *_args):
        self.state.setdefault("ui", {})["mode"] = self.ui_mode.get()
        self._save_state()
        self._setup_style()
        self.update_idletasks()

    # ---------- UI ----------
    def _init_indicator_images(self):
        def solid_img(color: str, w: int = 10, h: int = 18):
            img = tk.PhotoImage(width=w, height=h)
            img.put(color, to=(0, 0, w, h))
            return img

        self._ind_img_start = solid_img("#2e7d32")   # green
        self._ind_img_stop = solid_img("#c62828")    # red
        self._ind_img_cancel = solid_img("#546e7a")  # blue-grey
        self._ind_img_pro = solid_img("#f9a825")     # amber
        self._ind_img_break = solid_img("#1976d2")   # blue
        self._ind_img_none = solid_img("#000000", w=1, h=18)

    def _build_ui(self):
        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=8, pady=8)

        self.tab_timer = ttk.Frame(self.nb)
        self.tab_stats = ttk.Frame(self.nb)

        self.nb.add(self.tab_timer, text="Timer")
        self.nb.add(self.tab_stats, text="Stats")

        self._build_timer_tab()
        self._build_stats_tab()

    def _build_timer_tab(self):
        root = ttk.Frame(self.tab_timer)
        root.pack(fill="both", expand=True, padx=12, pady=10)
        root.columnconfigure(0, weight=1)

        card = ttk.LabelFrame(root, text="Session")
        card.grid(row=0, column=0, sticky="nwe")
        card.columnconfigure(1, weight=1)

        ttk.Label(card, text="Task:", style="Title.TLabel").grid(row=0, column=0, sticky="w", padx=10, pady=(10, 6))
        ttk.Entry(card, textvariable=self.active_task, width=50).grid(row=0, column=1, sticky="we", padx=(8, 10), pady=(10, 6))
        self.timer_task_color_swatch = tk.Canvas(card, width=18, height=18, highlightthickness=1, highlightbackground="#bbbbbb")
        self.timer_task_color_swatch.grid(row=0, column=2, sticky="w", padx=(0, 6), pady=(10, 6))
        self.timer_task_color_swatch.bind("<Button-1>", lambda _e: self.pick_task_color())
        ttk.Button(card, text="Color…", style="Secondary.TButton", command=self.pick_task_color).grid(row=0, column=3, sticky="w", padx=(0, 0), pady=(10, 6))

        btns = ttk.Frame(card)
        btns.grid(row=1, column=0, columnspan=2, sticky="we", padx=10, pady=(0, 10))

        ttk.Button(btns, text="Start", command=self.start_session, style="Start.TButton").pack(side="left", padx=(0, 10))
        ttk.Button(btns, text="Stop", command=self.stop_session, style="Stop.TButton").pack(side="left", padx=(0, 10))
        ttk.Button(btns, text="Cancel", command=self.cancel_session, style="Cancel.TButton").pack(side="left", padx=(0, 10))
        ttk.Button(btns, text="Break", command=self.start_break, style="Secondary.TButton").pack(side="left", padx=(0, 10))
        ttk.Button(btns, text="Mark procrastination", command=self.mark_procrastination, style="Procrastinate.TButton").pack(side="left")

        dur = ttk.LabelFrame(card, text="Target duration")
        dur.grid(row=2, column=0, columnspan=2, sticky="we", padx=10, pady=(0, 10))
        for i, minutes in enumerate((15, 30, 60)):
            ttk.Radiobutton(dur, text=f"{minutes} min", value=minutes, variable=self.target_duration_min).grid(
                row=0, column=i, sticky="w", padx=(8 if i == 0 else 14, 0), pady=(6, 6)
            )
        ttk.Label(dur, text="Custom (min):").grid(row=1, column=0, sticky="w", padx=8, pady=(0, 8))
        ttk.Spinbox(dur, from_=5, to=240, textvariable=self.target_duration_min, width=6).grid(row=1, column=1, sticky="w", padx=(8, 0), pady=(0, 8))
        ttk.Checkbutton(dur, text="Auto-stop when target ends", variable=self.auto_stop_enabled).grid(row=1, column=2, sticky="w", padx=(14, 0), pady=(0, 8))

        info = ttk.LabelFrame(root, text="Status")
        info.grid(row=1, column=0, sticky="nwe", pady=(10, 0))
        info.columnconfigure(0, weight=1)

        ttk.Label(info, textvariable=self.status, style="Status.TLabel").grid(row=0, column=0, sticky="w", padx=10, pady=(10, 0))
        self.timer_lbl = ttk.Label(info, text="00:00:00", style="Timer.TLabel")
        self.timer_lbl.grid(row=1, column=0, sticky="w", padx=10, pady=(6, 6))

        self.progress = ttk.Progressbar(info, orient="horizontal", mode="determinate", style="Green.Horizontal.TProgressbar")
        self.progress.grid(row=2, column=0, sticky="we", padx=10, pady=(0, 10))

        # FIX: check-ins must be on next row (previously overlapped with appearance)
        settings = ttk.LabelFrame(root, text="Check-ins (adaptive)")
        settings.grid(row=3, column=0, sticky="nwe", pady=(10, 0))
        settings.columnconfigure(1, weight=1)

        ttk.Checkbutton(settings, text="Enable check-ins", variable=self.prompt_enabled).grid(row=0, column=0, sticky="w", padx=10, pady=(8, 4))
        ttk.Checkbutton(settings, text="Topmost prompt", variable=self.topmost_prompt).grid(row=0, column=1, sticky="w", padx=10, pady=(8, 4))
        ttk.Checkbutton(settings, text="Beep", variable=self.beep_enabled).grid(row=0, column=2, sticky="w", padx=10, pady=(8, 4))

        ttk.Label(settings, text="Adaptive interval (min) for this task:").grid(row=1, column=0, sticky="w", padx=10, pady=(4, 8))
        ttk.Spinbox(settings, from_=MIN_INTERVAL, to=MAX_INTERVAL, textvariable=self.current_interval_min, width=6).grid(row=1, column=1, sticky="w", padx=10, pady=(4, 8))
        ttk.Button(settings, text="Apply to task", style="Secondary.TButton", command=self._manual_interval_changed).grid(row=1, column=2, sticky="w", padx=10, pady=(4, 8))

    def _make_vscroll_frame(self, parent):
        outer = ttk.Frame(parent)
        outer.rowconfigure(0, weight=1)
        outer.columnconfigure(0, weight=1)

        canvas = tk.Canvas(outer, highlightthickness=0)
        vsb = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)

        canvas.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")

        inner = ttk.Frame(canvas)
        win_id = canvas.create_window((0, 0), window=inner, anchor="nw")

        def on_configure(_e=None):
            canvas.configure(scrollregion=canvas.bbox("all"))

        def on_resize(event):
            canvas.itemconfigure(win_id, width=event.width)

        inner.bind("<Configure>", on_configure)
        canvas.bind("<Configure>", on_resize)

        def _on_mousewheel(event):
            delta = -1 * int(event.delta / 120) if event.delta else (1 if event.num == 5 else -1)
            canvas.yview_scroll(delta, "units")

        canvas.bind_all("<MouseWheel>", _on_mousewheel)
        canvas.bind_all("<Button-4>", _on_mousewheel)
        canvas.bind_all("<Button-5>", _on_mousewheel)

        return outer, inner

    def _build_stats_tab(self):
        outer = ttk.Frame(self.tab_stats)
        outer.pack(fill="both", expand=True, padx=12, pady=10)
        outer.rowconfigure(1, weight=1)
        outer.columnconfigure(0, weight=1)

        top = ttk.Frame(outer)
        top.grid(row=0, column=0, sticky="we")
        ttk.Button(top, text="Refresh", command=self._request_refresh).pack(side="left")
        ttk.Button(top, text="< Prev", command=self._prev_month).pack(side="left", padx=(10, 0))
        ttk.Button(top, text="Next >", command=self._next_month).pack(side="left", padx=(6, 0))
        ttk.Button(top, text="Export current week…", command=self.export_current_week_csv).pack(side="left", padx=(12, 0))
        # Month label moved into Calendar title
        self.month_lbl = None

        pw = ttk.PanedWindow(outer, orient="horizontal")
        pw.grid(row=1, column=0, sticky="nsew")

        # Left pane: calendar + notes (notes smaller)
        left = ttk.Frame(pw)
        left.columnconfigure(0, weight=1)
        left.rowconfigure(0, weight=1)

        self.left_vpw = ttk.PanedWindow(left, orient="vertical")
        self.left_vpw.grid(row=0, column=0, sticky="nsew")

        self.cal_container = ttk.LabelFrame(self.left_vpw, text="Calendar")
        self.cal_container.columnconfigure(0, weight=1)
        self.cal_container.rowconfigure(0, weight=1)

        self.cal_frame = ttk.Frame(self.cal_container)
        self.cal_frame.grid(row=0, column=0, sticky="nsew")
        self._render_calendar()

        notes_container = ttk.LabelFrame(self.left_vpw, text="Agenda (selected day)")
        notes_container.columnconfigure(0, weight=1)
        notes_container.rowconfigure(0, weight=1)

        notes_text_frame = ttk.Frame(notes_container)
        notes_text_frame.grid(row=0, column=0, sticky="nsew", padx=4, pady=4)
        notes_text_frame.columnconfigure(0, weight=1)
        notes_text_frame.rowconfigure(0, weight=1)

        # smaller by default
        self.notes_text = tk.Text(notes_text_frame, wrap="word", height=4, undo=True)
        self.notes_text.grid(row=0, column=0, sticky="nsew")
        notes_vsb = ttk.Scrollbar(notes_text_frame, orient="vertical", command=self.notes_text.yview)
        self.notes_text.configure(yscrollcommand=notes_vsb.set)
        notes_vsb.grid(row=0, column=1, sticky="ns")

        self.notes_text.bind("<KeyRelease>", lambda _e: self._schedule_save_current_note())
        self._load_current_note()

        # weights favor calendar heavily
        self.left_vpw.add(self.cal_container, weight=1)
        self.left_vpw.add(notes_container, weight=1)

        pw.add(left, weight=0)

        # Keep the middle (left/right) divider stable: set an initial width and lock the sash.
        try:
            left.configure(width=420)
        except Exception:
            pass

        def _set_main_sash_once(_e=None):
            # Initial main divider: 1:3 (left:right), favor right. User adjustable afterwards.
            if getattr(self, "_main_sash_set", False):
                return
            try:
                self.update_idletasks()
                w = pw.winfo_width()
                if w and w > 100:
                    # Prefer ~35% left, but never narrower than calendar needs.
                    desired = int(w * 0.46)
                    try:
                        cal_need = self.cal_container.winfo_reqwidth() + 90
                    except Exception:
                        cal_need = 0
                    pos = max(desired, cal_need)
                    # avoid pushing too far right
                    pos = min(pos, int(w * 0.65))
                    pw.sashpos(0, pos)
                    self._main_sash_set = True
            except Exception:
                pass

        outer.bind("<Map>", _set_main_sash_once)

        # Apply initial sash position (after widget gets real size).
        # Default: Agenda height equals Calendar height.
        def _apply_initial_left_sash(_e=None):
            # Robust: wait until PanedWindow has a real height, then set 50/50
            if getattr(self, "_left_sash_applied", False):
                return

            def _try_set(attempt=0):
                try:
                    self.update_idletasks()
                    h = self.left_vpw.winfo_height()
                    if h < 200 and attempt < 8:
                        self.after(50, lambda: _try_set(attempt + 1))
                        return
                    if h <= 0:
                        h = max(400, self.winfo_height())
                    self.left_vpw.sashpos(0, int(h * 0.50))
                    self._left_sash_applied = True
                except Exception:
                    pass

            _try_set()

        left.bind("<Map>", _apply_initial_left_sash)

        # Right pane: scrollable
        right_outer, right = self._make_vscroll_frame(pw)
        pw.add(right_outer, weight=1)

        # --- Persist and restore main left/right divider (prevents it from jumping when switching tabs) ---
        self._stats_main_pw = pw

        def _restore_main_sashpos():
            try:
                ui = self._get_ui_state()
                saved = ui.get("stats_main_sashpos", None)
                self.update_idletasks()
                w = pw.winfo_width()
                if not w or w < 300:
                    return
                if saved is None:
                    pos = int(w * 0.46)
                else:
                    pos = int(saved)
                pos = max(260, min(pos, w - 260))
                pw.sashpos(0, pos)
            except Exception:
                pass

        def _save_main_sashpos(_e=None):
            try:
                ui = self._get_ui_state()
                ui["stats_main_sashpos"] = int(pw.sashpos(0))
                self._save_state()
            except Exception:
                pass

        # When user drags sash
        pw.bind("<ButtonRelease-1>", _save_main_sashpos)

        # When Stats tab becomes visible again
        def _on_tab_changed(_e=None):
            try:
                if self.nb.select() == str(self.tab_stats):
                    self.after(30, _restore_main_sashpos)
            except Exception:
                pass

        self.nb.bind("<<NotebookTabChanged>>", _on_tab_changed)

        # Initial restore
        self.after(60, _restore_main_sashpos)
        right.columnconfigure(0, weight=1)

        # Day rundown (top)
        rundown_box = ttk.LabelFrame(right, text="Today")
        rundown_box.grid(row=0, column=0, sticky="we", pady=(0, 10))
        rundown_box.columnconfigure(0, weight=1)

        filt = ttk.Frame(rundown_box)
        filt.grid(row=0, column=0, sticky="we", padx=10, pady=(8, 6))

        ttk.Label(filt, text="Task:").pack(side="left")
        self.rundown_task_cb = ttk.Combobox(filt, textvariable=self.rundown_task_filter, state="readonly", width=24, values=["All tasks"])
        self.rundown_task_cb.pack(side="left", padx=(6, 10))
        self.stats_task_color_swatch = tk.Canvas(filt, width=16, height=16, highlightthickness=1, highlightbackground="#bbbbbb")
        self.stats_task_color_swatch.pack(side="left", padx=(0, 6))

        ttk.Label(filt, text="Event:").pack(side="left")
        self.rundown_event_cb = ttk.Combobox(
            filt,
            textvariable=self.rundown_event_filter,
            state="readonly",
            width=18,
            values=["All events", "start", "session_complete", "stop", "break", "off_task", "procrastination", "cancel"]
        )
        self.rundown_event_cb.pack(side="left", padx=(6, 0))

        self.rundown_task_cb.bind("<<ComboboxSelected>>", lambda _e: (self._update_stats_task_swatch(), self._apply_rundown_filters()))
        self.rundown_event_cb.bind("<<ComboboxSelected>>", lambda _e: self._apply_rundown_filters())

        cols = ("time", "event", "task", "note")
        tv_frame = ttk.Frame(rundown_box)
        tv_frame.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))
        tv_frame.columnconfigure(0, weight=1)
        tv_frame.rowconfigure(0, weight=1)

        self.rundown = ttk.Treeview(tv_frame, columns=cols, show="tree headings", height=10)
        self.rundown.heading("#0", text="")
        self.rundown.column("#0", width=18, minwidth=18, stretch=False, anchor="center")
        # equal widths, auto-stretch
        for c, w in [("time", 200), ("event", 200), ("task", 200), ("note", 200)]:
            self.rundown.heading(c, text=c.capitalize(), command=lambda col=c: self._toggle_sort_rundown(col))
            self.rundown.column(c, width=w, anchor="w", stretch=True, minwidth=80)
        self.rundown.grid(row=0, column=0, sticky="nsew")

        vsb = ttk.Scrollbar(tv_frame, orient="vertical", command=self.rundown.yview)
        self.rundown.configure(yscrollcommand=vsb.set)
        vsb.grid(row=0, column=1, sticky="ns")

        hsb = ttk.Scrollbar(tv_frame, orient="horizontal", command=self.rundown.xview)
        self.rundown.configure(xscrollcommand=hsb.set)
        hsb.grid(row=1, column=0, sticky="we")

        # Task breakdown (middle)
        perf_box = ttk.LabelFrame(right, text="Task breakdown (sessions)")
        perf_box.grid(row=2, column=0, sticky="we", pady=(0, 10))
        perf_box.columnconfigure(0, weight=1)
        perf_box.rowconfigure(1, weight=1)

        # Task period selector
        self.task_period = tk.StringVar(value="Selected day")
        tp = ttk.Frame(perf_box)
        tp.grid(row=0, column=0, sticky="we", padx=10, pady=(8, 2))
        tp.columnconfigure(3, weight=1)

        ttk.Label(tp, text="Period:").grid(row=0, column=0, sticky="w")
        self.task_period_cb = ttk.Combobox(
            tp, textvariable=self.task_period, state="readonly", width=16,
            values=["Selected day", "Selected week", "All time"]
        )
        self.task_period_cb.grid(row=0, column=1, sticky="w", padx=(8, 0))
        self.task_period_cb.bind("<<ComboboxSelected>>", lambda _e: self._update_day_and_week_views(self.selected_day.get()))

        perf_frame = ttk.Frame(perf_box)
        perf_frame.grid(row=1, column=0, sticky="nsew", padx=10, pady=(6, 10))
        perf_frame.columnconfigure(0, weight=1)
        perf_frame.rowconfigure(0, weight=1)

        pcols = ("task", "sessions", "total_time", "avg_session", "pro_cnt")
        self.task_perf = ttk.Treeview(perf_frame, columns=pcols, show="headings", height=10)
        # equal widths, auto-stretch
        for c, w, a, t in [
            ("task", 180, "w", "Task"),
            ("sessions", 180, "e", "Sessions (#)"),
            ("total_time", 180, "e", "Total time"),
            ("avg_session", 180, "e", "Avg/session"),
            ("pro_cnt", 180, "e", "Procrast. (#)"),
        ]:
            self.task_perf.heading(c, text=t)
            self.task_perf.column(c, width=w, anchor=a, stretch=True, minwidth=80)
        self.task_perf.grid(row=0, column=0, sticky="nsew")

        p_vsb = ttk.Scrollbar(perf_frame, orient="vertical", command=self.task_perf.yview)
        self.task_perf.configure(yscrollcommand=p_vsb.set)
        p_vsb.grid(row=0, column=1, sticky="ns")        # Summary (overhaul) + last week (bottom)
        summary_week = ttk.LabelFrame(right, text="Summary")
        summary_week.grid(row=1, column=0, sticky="we", pady=(0, 10))
        summary_week.columnconfigure(1, weight=1)

        self.stats_period = tk.StringVar(value="Selected day")
        ttk.Label(summary_week, text="Period:").grid(row=0, column=0, sticky="w", padx=10, pady=(8, 4))
        self.stats_period_cb = ttk.Combobox(
            summary_week, textvariable=self.stats_period, state="readonly", width=18,
            values=["Selected day", "Selected week", "All time"]
        )
        self.stats_period_cb.grid(row=0, column=1, sticky="w", padx=10, pady=(8, 4))
        self.stats_period_cb.bind("<<ComboboxSelected>>", lambda _e: self._update_day_and_week_views(self.selected_day.get()))

        # KPI row
        self.kpi_onpct = ttk.Label(summary_week, text="—", font=("Segoe UI", 18, "bold"))
        self.kpi_onpct.grid(row=1, column=0, sticky="w", padx=10, pady=(4, 0))
        self.kpi_onoff = ttk.Label(summary_week, text="", font=("Segoe UI", 10))
        self.kpi_onoff.grid(row=1, column=1, sticky="w", padx=10, pady=(10, 0))

        self.kpi_meta = ttk.Label(summary_week, text="", justify="left")
        self.kpi_meta.grid(row=2, column=0, columnspan=2, sticky="we", padx=10, pady=(2, 6))

        # ON/OFF bar with percentage label
        self.summary_graph = tk.Canvas(summary_week, height=64, highlightthickness=0)
        self.summary_graph.grid(row=3, column=0, columnspan=2, sticky="we", padx=10, pady=(0, 8))
        self.summary_graph.bind("<Configure>", lambda _e: self._redraw_summary_graph())

        # Week view (based on selected day)
        week_row = ttk.Frame(summary_week)
        week_row.grid(row=4, column=0, columnspan=2, sticky="we", padx=10, pady=(2, 4))
        week_row.columnconfigure(1, weight=1)

        ttk.Label(week_row, text="Week:").grid(row=0, column=0, sticky="w")
        self.week_view = tk.StringVar(value="Current week")
        self.week_view_cb = ttk.Combobox(
            week_row, textvariable=self.week_view, state="readonly", width=16,
            values=["Current week", "Previous week"]
        )
        self.week_view_cb.grid(row=0, column=1, sticky="w", padx=(6, 0))
        self.week_view_cb.bind("<<ComboboxSelected>>", lambda _e: self._update_day_and_week_views(self.selected_day.get()))

        self.week_lbl = ttk.Label(summary_week, text="")
        self.week_lbl.grid(row=5, column=0, columnspan=2, sticky="w", padx=10, pady=(0, 4))

        self.week_graph = tk.Canvas(summary_week, height=78, highlightthickness=0)
        self.week_graph.grid(row=6, column=0, columnspan=2, sticky="we", padx=10, pady=(0, 10))
        self.week_graph.bind("<Configure>", lambda _e: self._redraw_week_graph())

        self._rundown_sort_state = {"col": "time", "reverse": False}
        self._update_day_and_week_views(self.selected_day.get())

    # ---------- Calendar navigation ----------
    def _prev_month(self):
        if self.calendar_month == 1:
            self.calendar_month = 12
            self.calendar_year -= 1
        else:
            self.calendar_month -= 1
        self._render_calendar()

    def _next_month(self):
        if self.calendar_month == 12:
            self.calendar_month = 1
            self.calendar_year += 1
        else:
            self.calendar_month += 1
        self._render_calendar()

    def _render_calendar(self):
        for w in self.cal_frame.winfo_children():
            w.destroy()

        if hasattr(self, 'cal_container') and self.cal_container is not None:
            self.cal_container.config(text=f"Calendar — {cal.month_name[self.calendar_month]} {self.calendar_year}")

        hdr = ttk.Frame(self.cal_frame)
        hdr.pack(anchor="w")
        for i, wd in enumerate(["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]):
            ttk.Label(hdr, text=wd, width=5, anchor="center").grid(row=0, column=i, padx=1, pady=1)

        month_cal = cal.Calendar(firstweekday=0).monthdayscalendar(self.calendar_year, self.calendar_month)
        grid = ttk.Frame(self.cal_frame)
        grid.pack(pady=(6, 0), anchor="w")

        for r, week in enumerate(month_cal):
            for c, d in enumerate(week):
                if d == 0:
                    ttk.Label(grid, text="", width=5).grid(row=r, column=c, padx=1, pady=1)
                    continue
                ds = date(self.calendar_year, self.calendar_month, d).strftime("%Y-%m-%d")
                txt = str(d)

                summ = self.stats.summary_for_day(ds)
                ratio = summ["ratio_on"]
                if ratio is None:
                    style = "DayNone.TButton"
                elif ratio < 0.40:
                    style = "DayLow.TButton"
                elif ratio < 0.70:
                    style = "DayMid.TButton"
                else:
                    style = "DayHigh.TButton"

                btn = ttk.Button(grid, text=txt, width=4, style=style, command=lambda ds=ds: self._select_day(ds))
                btn.grid(row=r, column=c, padx=1, pady=1)

                if ds == date.today().strftime("%Y-%m-%d"):
                    btn.configure(text=txt + "•")
                if ds == self.selected_day.get():
                    btn.configure(text="[" + txt + "]")

    def _select_day(self, ds: str):
        self.selected_day.set(ds)
        self._render_calendar()
        self._update_day_and_week_views(ds)
        self._load_current_note()

    # ---------- Timer helpers ----------
    def _target_minutes_int(self):
        try:
            return int(self.target_duration_min.get())
        except Exception:
            return None

    def _compose_note(self, reason, target_min, interval_min, extra=None):
        parts = []
        if reason:
            r = " ".join(str(reason).strip().split())
            if r:
                parts.append(r)
        kv = []
        if target_min:
            kv.append(f"target_min={int(target_min)}")
        if interval_min:
            kv.append(f"interval_min={int(interval_min)}")
        if extra:
            kv.append(str(extra).strip())
        if kv:
            parts.append(" ".join(kv))
        return " | ".join(parts).strip()

    

    def _clean_note_for_display(self, note: str) -> str:
        # Hide internal kv fields from Day rundown note column
        if not note:
            return ""
        s = str(note)
        s = re.sub(r"\binterval_min=\d+\b", "", s)
        s = re.sub(r"\bauto_stop=1\b", "", s)
        # normalize separators and whitespace
        s = re.sub(r"\s*\|\s*", " | ", s)
        s = re.sub(r"\s{2,}", " ", s).strip()
        s = s.strip(" |")
        return s

    def _ask_reason(self, title: str, prompt: str):
        return simpledialog.askstring(title, prompt, parent=self)

    # ---------- Timer ----------
    def _manual_interval_changed(self):
        task = self.active_task.get().strip()
        if not task:
            return
        st = self._task_state(task)
        st["interval_min"] = clamp(int(self.current_interval_min.get()), MIN_INTERVAL, MAX_INTERVAL)
        st["yes_streak"] = 0
        self._save_state()
        if self.session_start_ts:
            self.next_prompt_at = self.session_elapsed + st["interval_min"] * 60
        self._append_log("interval_set", note=f"interval_min={st['interval_min']}")
        self._request_refresh()

    def start_session(self):
        task = self.active_task.get().strip()
        if not task:
            return
        st = self._task_state(task)
        self.current_interval_min.set(int(st.get("interval_min", DEFAULT_INTERVAL_MIN)))

        self.session_start_ts = time.time()
        self.session_elapsed = 0.0
        self.last_tick = time.time()
        self.next_prompt_at = int(st["interval_min"]) * 60

        self._update_task_color_swatch()
        self._update_progress_max()

        tmin = self._target_minutes_int()
        interval_now = int(self.current_interval_min.get())
        note = self._compose_note(None, tmin, interval_now)

        self.status.set(f"Running: {task} (interval {st['interval_min']} min)")
        self._append_log("start", note=note)
        self._request_refresh()

    def stop_session(self):
        if not self.session_start_ts:
            return
        tmin = self._target_minutes_int()
        interval_now = int(self.current_interval_min.get())
        self._append_log("stop", note=self._compose_note(None, tmin, interval_now))
        self._end_session_ui(reset=True)
        self._request_refresh()

    def cancel_session(self):
        if not self.session_start_ts:
            return
        tmin = self._target_minutes_int()
        interval_now = int(self.current_interval_min.get())
        self._append_log("cancel", note=self._compose_note(None, tmin, interval_now))
        self._end_session_ui(reset=True)
        self._request_refresh()

    def start_break(self):
        # Start a break timer; if a session is running, stop it first.
        if self.on_break:
            return
        task = self.active_task.get().strip()
        tmin = self._target_minutes_int()
        interval_now = int(self.current_interval_min.get()) if task else None
        if self.session_start_ts:
            # Log stop of the current session, then begin break.
            self._append_log("stop", note=self._compose_note(None, tmin, interval_now, extra="manual_break=1"))
            self._end_session_ui(reset=True)
        self._begin_break(task_for_log=task, note=self._compose_note(None, tmin, interval_now, extra="manual_break=1"))

    def _begin_break(self, task_for_log: str, note: str = ""):
        if self.on_break:
            return
        self.on_break = True
        self.break_start_ts = time.time()
        self.break_elapsed = 0.0
        self.break_last_tick = time.time()
        self._break_task_for_log = (task_for_log or '').strip()
        self._break_note_for_log = note or ""
        self.status.set("On break")
        self._request_refresh()

        win = tk.Toplevel(self)
        win.title("Break")
        win.resizable(False, False)
        win.attributes("-topmost", bool(self.topmost_prompt.get()))
        win.grab_set()

        ttk.Label(win, text="Break in progress", font=("Segoe UI", 11, "bold")).pack(padx=14, pady=(12, 6))
        info = ttk.Label(win, text="00:00:00")
        info.pack(padx=14, pady=(0, 10))

        btns = ttk.Frame(win)
        btns.pack(padx=14, pady=(0, 12), fill="x")

        def end_only():
            self._end_break(log=True)
            win.destroy()
            self._request_refresh()

        def end_and_start():
            self._end_break(log=True)
            win.destroy()
            self.start_session()

        ttk.Button(btns, text="End break", command=end_only).pack(side="left", expand=True, fill="x", padx=(0, 8))
        ttk.Button(btns, text="End break & start session", command=end_and_start).pack(side="left", expand=True, fill="x")

        def on_close():
            self._end_break(log=True)
            win.destroy()
            self._request_refresh()
        win.protocol("WM_DELETE_WINDOW", on_close)

        def _update_lbl():
            if not self.on_break or not win.winfo_exists():
                return
            elapsed = time.time() - (self.break_start_ts or time.time())
            info.config(text=self._format_hms(elapsed))
            win.after(250, _update_lbl)
        _update_lbl()

        win.update_idletasks()
        w = win.winfo_width()
        h = win.winfo_height()
        x = (win.winfo_screenwidth() - w) // 2
        y = (win.winfo_screenheight() - h) // 2
        win.geometry(f"{w}x{h}+{x}+{y}")
        self.wait_window(win)

    def _end_break(self, log: bool = True):
        if not self.on_break:
            return
        try:
            elapsed = time.time() - (self.break_start_ts or time.time())
        except Exception:
            elapsed = float(self.break_elapsed or 0.0)
        self.on_break = False
        self.break_start_ts = None
        self.break_last_tick = None
        self.break_elapsed = 0.0
        self.status.set("Idle")
        if log:
            self._append_log(
                "break",
                note=self._break_note_for_log,
                secs_override=int(elapsed),
                task_override=self._break_task_for_log
            )

    def _end_session_ui(self, reset: bool = True):
        self.session_start_ts = None
        self.last_tick = None
        self.next_prompt_at = None
        if reset:
            self.session_elapsed = 0.0
            self.timer_lbl.configure(text="00:00:00", style="Timer.TLabel")
            self.progress["value"] = 0
        self.status.set("Idle")

    def mark_procrastination(self):
        if not self.session_start_ts:
            return
        reason = self._ask_reason("Procrastination", "Why did you procrastinate? (short)")
        if reason is None:
            return
        tmin = self._target_minutes_int()
        interval_now = int(self.current_interval_min.get())
        self._append_log("procrastination", note=self._compose_note(reason, tmin, interval_now))
        self._adapt_interval(on_task=False)
        self._request_refresh()

    def _adapt_interval(self, on_task: bool):
        task = self.active_task.get().strip()
        if not task:
            return
        st = self._task_state(task)

        interval = int(st.get("interval_min", DEFAULT_INTERVAL_MIN))
        yes_streak = int(st.get("yes_streak", 0))

        if on_task:
            yes_streak += 1
            if yes_streak >= STREAK_FOR_STEPUP:
                interval = clamp(interval + STEP_UP, MIN_INTERVAL, MAX_INTERVAL)
                yes_streak = 0
                self._append_log("interval_adapt_up", note=f"interval_min={interval}")
        else:
            interval = clamp(interval - STEP_DOWN, MIN_INTERVAL, MAX_INTERVAL)
            yes_streak = 0
            self._append_log("interval_adapt_down", note=f"interval_min={interval}")

        st["interval_min"] = interval
        st["yes_streak"] = yes_streak
        self.current_interval_min.set(interval)
        self._save_state()

        if self.session_start_ts:
            self.next_prompt_at = self.session_elapsed + interval * 60
            self.status.set(f"Running: {task} (interval {interval} min)")

    def _format_hms(self, seconds: float) -> str:
        s = int(seconds)
        return f"{s//3600:02d}:{(s%3600)//60:02d}:{s%60:02d}"

    def _beep(self):
        if not self.beep_enabled.get():
            return
        for i in range(BEEP_COUNT):
            self.after(i * BEEP_GAP_MS, self.bell)

    def _update_progress_max(self):
        try:
            target = int(self.target_duration_min.get())
        except Exception:
            target = 0
        self.progress.configure(maximum=max(1, target * 60))

    def _session_finished_dialog(self):
        self._beep()

        task = self.active_task.get().strip()
        elapsed = self._format_hms(self.session_elapsed)

        win = tk.Toplevel(self)
        win.title("Session finished")
        win.resizable(False, False)
        win.attributes("-topmost", True)
        win.grab_set()

        ttk.Label(win, text="Session complete.", font=("Segoe UI", 11, "bold")).pack(padx=14, pady=(12, 6))
        ttk.Label(win, text=f"Task: {task}\nElapsed: {elapsed}").pack(padx=14, pady=(0, 10))

        btns = ttk.Frame(win)
        btns.pack(padx=14, pady=(0, 12), fill="x")

        tmin = self._target_minutes_int()
        interval_now = int(self.current_interval_min.get())

        def do_break():
            win.destroy()
            # End the session UI, then start a break timer (duration will be logged when break ends)
            self._end_session_ui(reset=True)
            self._begin_break(task_for_log=task, note=self._compose_note(None, tmin, interval_now, extra="auto_stop=1"))

        def do_continue():
            win.destroy()
            self._end_session_ui(reset=True)
            self.start_session()

        def do_end():
            win.destroy()
            # Log as STOP (requested) and end session
            self._append_log("stop", note=self._compose_note(None, tmin, interval_now, extra="auto_stop=1"))
            self._end_session_ui(reset=True)
            self._request_refresh()

        ttk.Button(btns, text="Continue session", command=do_continue).pack(side="left", expand=True, fill="x", padx=(0, 8))
        ttk.Button(btns, text="Break", command=do_break).pack(side="left", expand=True, fill="x", padx=(0, 8))
        ttk.Button(btns, text="End session", command=do_end).pack(side="left", expand=True, fill="x")

        win.update_idletasks()
        w = win.winfo_width()
        h = win.winfo_height()
        x = (win.winfo_screenwidth() - w) // 2
        y = (win.winfo_screenheight() - h) // 2
        win.geometry(f"{w}x{h}+{x}+{y}")
        self.wait_window(win)

    def _prompt_checkin(self):
        self._beep()

        task = self.active_task.get().strip()
        elapsed = self._format_hms(self.session_elapsed)
        interval_now = int(self.current_interval_min.get())

        try:
            target = int(self.target_duration_min.get()) * 60
            rem = max(0, target - int(self.session_elapsed)) if target > 0 else None
        except Exception:
            rem = None
        rem_txt = self._format_hms(rem) if rem is not None else "n/a"

        win = tk.Toplevel(self)
        win.title("Check-in")
        win.resizable(False, False)
        win.attributes("-topmost", bool(self.topmost_prompt.get()))
        win.grab_set()

        ttk.Label(win, text="Still on task?", font=("Segoe UI", 11, "bold")).pack(padx=14, pady=(12, 6))
        ttk.Label(win, text=f"Task: {task}\nElapsed: {elapsed}\nRemaining: {rem_txt}\nInterval: {interval_now} min").pack(padx=14, pady=(0, 10))

        btns = ttk.Frame(win)
        btns.pack(padx=14, pady=(0, 12), fill="x")

        result = {"on_task": None}

        def yes():
            result["on_task"] = True
            win.destroy()

        def no():
            result["on_task"] = False
            win.destroy()

        ttk.Button(btns, text="Yes (on task)", command=yes).pack(side="left", expand=True, fill="x", padx=(0, 8))
        ttk.Button(btns, text="No (off task)", command=no).pack(side="left", expand=True, fill="x")

        win.update_idletasks()
        w = win.winfo_width()
        h = win.winfo_height()
        x = (win.winfo_screenwidth() - w) // 2
        y = (win.winfo_screenheight() - h) // 2
        win.geometry(f"{w}x{h}+{x}+{y}")

        self.wait_window(win)

        tmin = self._target_minutes_int()

        if result["on_task"] is True:
            self._append_log("checkin_on_task", note=self._compose_note(None, tmin, interval_now))
            self._adapt_interval(on_task=True)
            self._request_refresh()
            return

        if result["on_task"] is False:
            reason = self._ask_reason("Off task", "Why are you off task? (short)")
            if reason is None:
                return
            self._append_log("checkin_off_task", note=self._compose_note(reason, tmin, interval_now))
            self._adapt_interval(on_task=False)
            self._request_refresh()
            return

    def _tick(self):
        if self.session_start_ts:
            now = time.time()
            if self.last_tick is None:
                self.last_tick = now
            dt = now - self.last_tick
            self.last_tick = now
            self.session_elapsed += max(0.0, dt)

            self.timer_lbl.configure(text=self._format_hms(self.session_elapsed), style="Timer.TLabel")
            self._update_progress_max()
            self.progress["value"] = min(self.progress["maximum"], int(self.session_elapsed))

            if self.auto_stop_enabled.get():
                try:
                    target_s = int(self.target_duration_min.get()) * 60
                except Exception:
                    target_s = 0
                if target_s > 0 and self.session_elapsed >= target_s:
                    tmin = self._target_minutes_int()
                    interval_now = int(self.current_interval_min.get())
                    self._session_finished_dialog()

            if self.prompt_enabled.get() and self.next_prompt_at is not None:
                if self.session_elapsed >= self.next_prompt_at:
                    self._prompt_checkin()

        elif self.on_break:
            # Show break timer in the main timer label as well
            try:
                elapsed = time.time() - (self.break_start_ts or time.time())
            except Exception:
                elapsed = float(self.break_elapsed or 0.0)
            self.timer_lbl.configure(text=self._format_hms(elapsed), style="Timer.TLabel")
            self.progress["value"] = 0
            self.status.set("On break")

        self.after(200, self._tick)

    def _on_active_task_changed(self):
        task = (self.active_task.get() or '').strip()
        if not task:
            return
        self._task_state(task)
        if hasattr(self, 'timer_task_color_swatch'):
            self._update_task_color_swatch()

    # ---------- Task colors ----------
    def _update_task_color_swatch(self):
        task = self.active_task.get().strip()
        if not task:
            self.timer_task_color_swatch.delete("all")
            return
        st = self._task_state(task)
        col = st.get("color", "#dfe8ff")
        self.timer_task_color_swatch.delete("all")
        self.timer_task_color_swatch.create_rectangle(1, 1, 17, 17, fill=col, outline="")

    def pick_task_color(self):
        task = self.active_task.get().strip()
        if not task:
            return
        current = self._task_state(task).get("color", "#dfe8ff")
        chosen = colorchooser.askcolor(color=current, title=f"Color for task: {task}")[1]
        if not chosen:
            return
        st = self._task_state(task)
        st["color"] = chosen
        self._save_state()
        self._update_task_color_swatch()
        self._request_refresh()

    def _update_stats_task_swatch(self):
        task = self.rundown_task_filter.get()
        col = "#ffffff"
        if task and task != "All tasks":
            col = self._task_state(task).get("color", "#dfe8ff")
        self.stats_task_color_swatch.delete("all")
        self.stats_task_color_swatch.create_rectangle(1, 1, 15, 15, fill=col, outline="")

    # ---------- Stats refresh ----------
    def _request_refresh(self):
        if self._refresh_job is not None:
            try:
                self.after_cancel(self._refresh_job)
            except Exception:
                pass
        self._refresh_job = self.after(200, self._refresh_stats)

    def _refresh_stats(self):
        self._refresh_job = None
        self.stats.load()
        self._render_calendar()
        self._update_day_and_week_views(self.selected_day.get())

    # ---------- Summary/week redraw-on-resize ----------
    def _redraw_summary_graph(self):
        on_min, off_min = self._last_summary_onoff
        self._draw_summary_bar(on_min, off_min)

    def _redraw_week_graph(self):
        if self._last_week_days is not None and self._last_week_per_day is not None:
            self._draw_week_bars(self._last_week_days, self._last_week_per_day)

    # ---------- Day/Week updates ----------
    def _update_day_and_week_views(self, ds: str):
        day_events = self.stats.events_for_day(ds)
        tasks_today = sorted({(e["task"] or "").strip() for e in day_events if (e["task"] or "").strip()})
        values = ["All tasks"] + tasks_today
        self.rundown_task_cb.configure(values=values)
        if self.rundown_task_filter.get() not in values:
            self.rundown_task_filter.set("All tasks")
        self._update_stats_task_swatch()

        self._apply_rundown_filters()

        period_val = self.stats_period.get() if hasattr(self, "stats_period") else "Selected day"
        if period_val == "Selected day":
            start_s = end_s = ds
            title = f"Selected day: {ds}"
        elif period_val == "Selected week":
            anchor = datetime.strptime(ds, "%Y-%m-%d").date()
            wk_start = monday_of(anchor)
            wk_end = wk_start + timedelta(days=6)
            start_s = wk_start.strftime("%Y-%m-%d")
            end_s = wk_end.strftime("%Y-%m-%d")
            title = f"Selected week: {start_s} to {end_s} (Mon–Sun)"
        elif period_val == "All time":
            days = self.stats.days_present()
            if days:
                start_s, end_s = days[0], days[-1]
                title = f"All time: {start_s} to {end_s}"
            else:
                start_s = end_s = date.today().strftime("%Y-%m-%d")
                title = "All time: no data"
        else:
            start_s = end_s = ds
            title = f"Selected day: {ds}"
        # Week mini-graph (based on selected day) with toggle: current vs previous week
        try:
            anchor_day = datetime.strptime(ds, "%Y-%m-%d").date()
        except Exception:
            anchor_day = date.today()

        view = self.week_view.get() if hasattr(self, "week_view") else "Current week"
        week_anchor = anchor_day - timedelta(days=7) if view == "Previous week" else anchor_day

        wk_start = monday_of(week_anchor)
        wk_end = wk_start + timedelta(days=6)
        wk_start_s = wk_start.strftime("%Y-%m-%d")
        wk_end_s = wk_end.strftime("%Y-%m-%d")

        if hasattr(self, "week_lbl"):
            label = "Previous week" if view == "Previous week" else "Current week"
            self.week_lbl.config(text=f"{label}: {wk_start_s} to {wk_end_s} (Mon–Sun)")

        days, per_day = self.stats.week_summary(week_anchor)
        self._last_week_days = days
        self._last_week_per_day = per_day
        self._draw_week_bars(days, per_day)

        agg = self._aggregate_summary(start_s, end_s)
        ratio = agg["ratio_on"]
        ratio_txt = "n/a" if ratio is None else f"{int(ratio * 100)}%"

        avg_secs, cancel_rate, avg_tt = self.stats.session_stats_in_range(start_s, end_s)
        avg_s_txt = self._fmt_secs(avg_secs) if avg_secs is not None else "—"
        cancel_txt = (f"{int(cancel_rate * 100)}%" if cancel_rate is not None else "—")
        tt_txt = self._fmt_secs(avg_tt) if avg_tt is not None else "—"
        # KPI updates
        if hasattr(self, "kpi_onpct"):
            self.kpi_onpct.config(text=("—" if ratio is None else f"{int(ratio * 100)}% ON"))

        if hasattr(self, "kpi_onoff"):
            self.kpi_onoff.config(text=f"ON {agg['on_min']} min    OFF {agg['off_min']} min")

        if hasattr(self, "kpi_meta"):
            self.kpi_meta.config(text=(
                f"{title}\n"
                f"Sessions: start={agg['starts']}  stop={agg['stops']}  cancel={agg['cancels']}   |   Breaks: {agg.get('break_count',0)} ({self._fmt_secs(agg.get('break_secs',0))})   |   Procrastinations: {agg['procrastinations']}\n"
                f"Avg session: {avg_s_txt}   |   Cancel rate: {cancel_txt}   |   Avg time to 1st procrastination: {tt_txt}"
            ))

        self._last_summary_onoff = (agg["on_min"], agg["off_min"])
        self._draw_summary_bar(agg["on_min"], agg["off_min"])

        # Task breakdown period (separate from summary)
        task_period = self.task_period.get() if hasattr(self, "task_period") else period_val
        if task_period == "Selected day":
            start_t = end_t = ds
        elif task_period == "Selected week":
            anchor_t = datetime.strptime(ds, "%Y-%m-%d").date()
            tw_start = monday_of(anchor_t)
            tw_end = tw_start + timedelta(days=6)
            start_t = tw_start.strftime("%Y-%m-%d")
            end_t = tw_end.strftime("%Y-%m-%d")
        elif task_period == "All time":
            days_t = self.stats.days_present()
            if days_t:
                start_t, end_t = days_t[0], days_t[-1]
            else:
                start_t = end_t = date.today().strftime("%Y-%m-%d")
        else:
            start_t = end_t = ds

        pro_by_task = self._procrastination_counts_by_task(start_t, end_t)

        for item in self.task_perf.get_children():
            self.task_perf.delete(item)
        rows = []
        for task, sessions, total_secs, avg_secs, _cancels in self.stats.sessions_by_task_in_range(start_t, end_t):
            total_txt = self._fmt_secs(total_secs)
            avg_txt = "—" if avg_secs is None else self._fmt_secs(avg_secs)
            rows.append((task, sessions, total_txt, avg_txt, pro_by_task.get(task, 0)))
        rows.sort(key=lambda r: (r[1], r[4]), reverse=True)
        for r in rows:
            task_name = r[0]
            bg = self._task_state(task_name).get("color", "#ffffff") if task_name else "#ffffff"
            tag = f"taskbg_{bg}"
            if not hasattr(self, "_task_perf_tags"):
                self._task_perf_tags = set()
            if tag not in self._task_perf_tags:
                self.task_perf.tag_configure(tag, background=bg)
                self._task_perf_tags.add(tag)
            self.task_perf.insert("", "end", values=r, tags=(tag,))

    def _fmt_secs(self, secs):
        if secs is None:
            return "—"
        secs = int(max(0, secs))
        m, s = divmod(secs, 60)
        h, m = divmod(m, 60)
        if h:
            return f"{h}h {m}m"
        if m:
            return f"{m}m {s}s"
        return f"{s}s"

    def _aggregate_summary(self, start_day: str, end_day: str):
        on_min = off_min = 0
        pro = starts = stops = cancels = 0
        break_secs = 0
        break_count = 0

        for e in self.stats.events_in_range(start_day, end_day):
            evt = e.get("event", "")
            if evt == "procrastination":
                pro += 1
            elif evt == "start":
                starts += 1
            elif evt in ("stop", "session_complete"):
                stops += 1
            elif evt == "cancel":
                cancels += 1
            elif evt == "break":
                break_count += 1
                try:
                    break_secs += int(e.get("secs", 0) or 0)
                except Exception:
                    pass

        d0 = datetime.strptime(start_day, "%Y-%m-%d").date()
        d1 = datetime.strptime(end_day, "%Y-%m-%d").date()
        cur = d0
        while cur <= d1:
            ds = cur.strftime("%Y-%m-%d")
            s = self.stats.summary_for_day(ds)
            on_min += int(s.get("on_min", 0) or 0)
            off_min += int(s.get("off_min", 0) or 0)
            cur += timedelta(days=1)

        total = on_min + off_min
        ratio = (on_min / total) if total > 0 else None
        return {
            "on_min": on_min,
            "off_min": off_min,
            "ratio_on": ratio,
            "procrastinations": pro,
            "starts": starts,
            "stops": stops,
            "cancels": cancels,
            "break_count": break_count,
            "break_secs": break_secs,
        }

    def _procrastination_counts_by_task(self, start_day: str, end_day: str):
        counts = {}
        for e in self.stats.events_in_range(start_day, end_day):
            if e.get("event") != "procrastination":
                continue
            task = (e.get("task") or "").strip() or "(no task)"
            counts[task] = counts.get(task, 0) + 1
        return counts

    
    def _draw_summary_bar(self, on_min: int, off_min: int):
        c = self.summary_graph
        if not c.winfo_exists():
            return
        c.delete("all")
        c.update_idletasks()
        w = max(1, c.winfo_width())
        h = max(1, c.winfo_height())

        total = on_min + off_min
        margin = 10
        bar_h = 24
        y0 = (h - bar_h) // 2
        x0 = margin
        x1 = w - margin

        # Outline
        c.create_rectangle(x0, y0, x1, y0 + bar_h)

        if total <= 0:
            c.create_text((w // 2), y0 + bar_h + 16, text="No interval-based ON/OFF data in this period.")
            return

        on_ratio = on_min / total
        on_w = int((x1 - x0) * on_ratio)

        c.create_rectangle(x0, y0, x0 + on_w, y0 + bar_h, fill="#4caf50", outline="")
        c.create_rectangle(x0 + on_w, y0, x1, y0 + bar_h, fill="#f44336", outline="")

        # Labels + percent
        c.create_text(x0, y0 - 10, anchor="w", text="ON")
        c.create_text(x1, y0 - 10, anchor="e", text="OFF")
        c.create_text((x0 + x1) // 2, y0 + bar_h // 2, text=f"{int(on_ratio * 100)}% ON")

    def _draw_week_bars(self, days, per_day):
        c = self.week_graph
        if not c.winfo_exists():
            return
        c.delete("all")
        c.update_idletasks()
        w = max(1, c.winfo_width())
        h = max(1, c.winfo_height())

        margin_x = 10
        margin_y = 10
        usable_w = max(1, w - 2 * margin_x)
        usable_h = max(1, h - 2 * margin_y)

        totals = [d["on_min"] + d["off_min"] for d in per_day]
        max_total = max(totals) if totals else 0
        if max_total <= 0:
            c.create_text(w // 2, h // 2, text="No interval-based data in this week yet.")
            return

        # compute bar sizes robustly for small widths
        bar_w = max(10, int(usable_w / 7) - 6)
        gap = max(2, int((usable_w - bar_w * 7) / 6)) if usable_w > bar_w * 7 else 2

        x = margin_x
        for i in range(7):
            dsum = per_day[i]
            total = dsum["on_min"] + dsum["off_min"]
            label = days[i][8:10]
            if total <= 0:
                c.create_text(x + bar_w // 2, h - 2, anchor="s", text=label)
                x += bar_w + gap
                continue

            bar_total_h = int(usable_h * (total / max_total))
            on_h = int(bar_total_h * (dsum["on_min"] / total)) if total else 0
            off_h = bar_total_h - on_h

            y_bottom = h - margin_y
            c.create_rectangle(x, y_bottom - on_h, x + bar_w, y_bottom, fill="#4caf50", outline="")
            c.create_rectangle(x, y_bottom - on_h - off_h, x + bar_w, y_bottom - on_h, fill="#f44336", outline="")
            c.create_text(x + bar_w // 2, h - 2, anchor="s", text=label)
            x += bar_w + gap

    def _display_event_name(self, evt: str):
        return "off_task" if evt == "checkin_off_task" else evt

    def _indicator_for_event(self, evt: str):
        if evt in ("start", "session_complete"):
            return self._ind_img_start
        if evt == "stop":
            return self._ind_img_stop
        if evt == "cancel":
            return self._ind_img_cancel
        if evt == "procrastination":
            return self._ind_img_pro
        if evt == "break":
            return self._ind_img_break
        if evt == "checkin_off_task":
            return self._ind_img_pro
        return self._ind_img_none

    def _apply_rundown_filters(self):
        ds = self.selected_day.get()
        task_f = self.rundown_task_filter.get()
        evt_f = self.rundown_event_filter.get()

        for item in self.rundown.get_children():
            self.rundown.delete(item)

        allowed = {"start", "session_complete", "stop", "break", "cancel", "procrastination", "checkin_off_task"}
        for e in self.stats.events_for_day(ds):
            evt = e["event"]
            if evt not in allowed:
                continue

            task = (e["task"] or "").strip()
            if task_f != "All tasks" and task != task_f:
                continue

            shown_evt = self._display_event_name(evt)
            if evt_f != "All events" and shown_evt != evt_f:
                continue

            bg = self._task_state(task).get("color", "#ffffff") if task else "#ffffff"
            tag = f"taskbg_{bg}"
            if not hasattr(self, "_rundown_tags"):
                self._rundown_tags = set()
            if tag not in self._rundown_tags:
                self.rundown.tag_configure(tag, background=bg)
                self._rundown_tags.add(tag)

            img = self._indicator_for_event(evt)
            t = e["dt"].strftime("%H:%M:%S")
            self.rundown.insert("", "end", image=img, values=(t, shown_evt, task, self._clean_note_for_display(e.get("note", ""))), tags=(tag,))

        col = self._rundown_sort_state["col"]
        rev = self._rundown_sort_state["reverse"]
        self._sort_treeview(self.rundown, col, rev)

    def _toggle_sort_rundown(self, col: str):
        st = self._rundown_sort_state
        if st["col"] == col:
            st["reverse"] = not st["reverse"]
        else:
            st["col"] = col
            st["reverse"] = False
        self._sort_treeview(self.rundown, st["col"], st["reverse"])

    def _sort_treeview(self, tv: ttk.Treeview, col: str, reverse: bool):
        try:
            items = [(tv.set(k, col), k) for k in tv.get_children("")]
        except Exception:
            return

        def as_number(x):
            try:
                return float(x)
            except Exception:
                return None

        nums = [as_number(v) for v, _k in items]
        if all(n is not None for n in nums):
            items.sort(key=lambda t: float(t[0]), reverse=reverse)
        else:
            items.sort(key=lambda t: t[0], reverse=reverse)

        for idx, (_val, k) in enumerate(items):
            tv.move(k, "", idx)

    def export_current_week_csv(self):
        today = date.today()
        wk_start = monday_of(today)
        wk_end = wk_start + timedelta(days=6)
        start_s = wk_start.strftime("%Y-%m-%d")
        end_s = wk_end.strftime("%Y-%m-%d")

        default_name = f"procheck_week_{start_s}_to_{end_s}.csv"
        path = filedialog.asksaveasfilename(
            title="Export current week to CSV",
            defaultextension=".csv",
            initialfile=default_name,
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
        )
        if not path:
            return

        evs = self.stats.events_in_range(start_s, end_s)
        days, per_day = self.stats.week_summary(today)
        task_rows = self.stats.on_off_by_task_in_range(start_s, end_s)
        avg_secs, cancel_rate, avg_tt = self.stats.session_stats_in_range(start_s, end_s)

        try:
            with open(path, "w", encoding="utf-8", newline="") as f:
                w = csv.writer(f)

                w.writerow(["Export", "Current week", start_s, end_s])
                w.writerow([])
                w.writerow(["Insights"])
                w.writerow(["Avg session duration", self._fmt_secs(avg_secs)])
                w.writerow(["Cancel rate", "—" if cancel_rate is None else f"{int(cancel_rate*100)}%"])
                w.writerow(["Avg time to first procrastination", self._fmt_secs(avg_tt)])
                w.writerow([])

                w.writerow(["Per-day summary (interval-based)"])
                w.writerow(["day", "on_min", "off_min", "on_pct", "procrastinations", "starts", "stops", "cancels"])
                for s in per_day:
                    onp = "—" if s["ratio_on"] is None else f"{int(s['ratio_on']*100)}%"
                    w.writerow([s["day"], s["on_min"], s["off_min"], onp, s["procrastinations"], s["starts"], s["stops"], s["cancels"]])
                w.writerow([])

                w.writerow(["Task performance (interval-based)"])
                w.writerow(["task", "on_min", "off_min", "on_pct"])
                for task, onm, offm, _total, onp in task_rows:
                    onp_txt = "—" if onp is None else f"{int(onp*100)}%"
                    w.writerow([task, onm, offm, onp_txt])
                w.writerow([])

                w.writerow(["Events"])
                w.writerow(["timestamp", "event", "task", "session_seconds", "note"])
                for e in evs:
                    w.writerow([e["timestamp"], e["event"], e["task"], e["secs"], e["note"]])

            messagebox.showinfo("Export complete", f"Saved:\n{path}")
        except Exception as ex:
            messagebox.showerror("Export failed", str(ex))


if __name__ == "__main__":
    App().mainloop()