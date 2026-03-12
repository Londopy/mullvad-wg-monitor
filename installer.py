"""
Mullvad WireGuard Latency Monitor — Installer
Converts to .exe via PyInstaller. Bundles its own Python runtime so it runs
even on machines with no Python installed.

Build command (run once you have PyInstaller):
    pyinstaller --onefile --windowed --name "MullvadPingInstaller" installer.py
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import threading
import subprocess
import sys
import os
import platform
import urllib.request
import shutil
import tempfile
import json
from pathlib import Path

# ── THEME ──────────────────────────────────────────────────────────────────────
BG      = "#0d1117"
BG2     = "#161b22"
BG3     = "#21262d"
BG4     = "#2d333b"
ACCENT  = "#00e5ff"
GREEN   = "#7ee787"
RED     = "#f85149"
YELLOW  = "#e3b341"
FG      = "#e6edf3"
FG_DIM  = "#8b949e"
FG_DARK = "#484f58"
MONO    = ("Courier New", 9)
UI      = ("Segoe UI", 10)
UI_SM   = ("Segoe UI", 9)
UI_LG   = ("Segoe UI", 12)
UI_H    = ("Segoe UI", 11, "bold")

REQUIRED_PACKAGES = [
    ("matplotlib", "matplotlib"),
    ("seaborn",    "seaborn"),
    ("pandas",     "pandas"),
    ("numpy",      "numpy"),
    ("folium",     "folium"),
    ("pystray",    "pystray"),
    ("PIL",        "Pillow"),
]

PYTHON_DOWNLOAD_WIN   = "https://www.python.org/ftp/python/3.12.3/python-3.12.3-amd64.exe"
PYTHON_DOWNLOAD_MAC   = "https://www.python.org/ftp/python/3.12.3/python-3.12.3-macos11.pkg"
MAIN_SCRIPT_NAME      = "mullvad_ping.py"
MAIN_SCRIPT_GITHUB    = "https://raw.githubusercontent.com/Londopy/mullvad-wg-monitor/main/mullvad_ping.py"

# ── HELPERS ────────────────────────────────────────────────────────────────────

def find_python():
    """Return (path, version_str) for the best available Python 3, or (None, None)."""
    candidates = ["python3", "python", sys.executable]
    for cmd in candidates:
        try:
            r = subprocess.run([cmd, "--version"], capture_output=True, text=True, timeout=5)
            out = (r.stdout + r.stderr).strip()
            if "Python 3" in out:
                return cmd, out.split()[-1]
        except Exception:
            pass
    return None, None

def pip_list(python_cmd):
    """Return set of installed package names (lowercase)."""
    try:
        r = subprocess.run(
            [python_cmd, "-m", "pip", "list", "--format=json"],
            capture_output=True, text=True, timeout=15)
        pkgs = json.loads(r.stdout)
        return {p["name"].lower() for p in pkgs}
    except Exception:
        return set()

def install_package(python_cmd, pip_name, log_cb):
    """Install a single package via pip, calling log_cb with each output line."""
    proc = subprocess.Popen(
        [python_cmd, "-m", "pip", "install", "--upgrade", pip_name],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, bufsize=1)
    for line in proc.stdout:
        log_cb(line.rstrip())
    proc.wait()
    return proc.returncode == 0

# ── MAIN APP ───────────────────────────────────────────────────────────────────

class InstallerApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Mullvad WireGuard Latency Monitor  —  Installer v2.0")
        self.configure(bg=BG)
        self.geometry("720x620")
        self.resizable(False, False)

        self._python_cmd   = None
        self._python_ver   = None
        self._installed_ok = set()
        self._install_dir  = tk.StringVar(value=str(Path.home() / "MullvadPingTool"))
        self._source_var   = tk.StringVar(value="github")

        self._apply_style()
        self._build_ui()
        self.after(200, self._auto_detect)

    # ── STYLE ──────────────────────────────────────────────────────────────────
    def _apply_style(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        s.configure("custom.Horizontal.TProgressbar",
                    troughcolor=BG3, background=ACCENT,
                    darkcolor=ACCENT, lightcolor=ACCENT,
                    bordercolor=BG3, relief="flat")
        s.configure("TCheckbutton",
                    background=BG2, foreground=FG,
                    font=UI_SM, focuscolor=BG2)
        s.map("TCheckbutton", background=[("active", BG2)])

    # ── BUILD UI ───────────────────────────────────────────────────────────────
    def _build_ui(self):
        # Header
        hdr = tk.Frame(self, bg=BG2, pady=14)
        hdr.pack(fill=tk.X)
        tk.Label(hdr, text="  MULLVAD  LAX PING TOOL",
                 font=("Courier New", 16, "bold"), fg=ACCENT, bg=BG2).pack(side=tk.LEFT, padx=20)
        tk.Label(hdr, text="Installer  v2.0",
                 font=MONO, fg=FG_DIM, bg=BG2).pack(side=tk.RIGHT, padx=20)

        # Body uses a left sidebar + right panel layout
        body = tk.Frame(self, bg=BG)
        body.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)

        # ── Left: steps sidebar ────────────────────────────────────────────────
        sidebar = tk.Frame(body, bg=BG2, width=180, pady=20, padx=0)
        sidebar.pack(side=tk.LEFT, fill=tk.Y)
        sidebar.pack_propagate(False)

        tk.Label(sidebar, text="STEPS", font=("Courier New", 9, "bold"),
                 fg=FG_DIM, bg=BG2).pack(pady=(0, 10))

        self._step_labels = {}
        steps = [
            ("detect",   "1. Detect Python"),
            ("packages", "2. Install Packages"),
            ("location", "3. Install Location"),
            ("download", "4. Download / Copy"),
            ("launch",   "5. Launch"),
        ]
        for key, text in steps:
            lbl = tk.Label(sidebar, text=text, font=UI_SM, fg=FG_DIM,
                           bg=BG2, anchor="w", padx=18, pady=6)
            lbl.pack(fill=tk.X)
            self._step_labels[key] = lbl

        sep = tk.Frame(body, bg=BG3, width=1)
        sep.pack(side=tk.LEFT, fill=tk.Y)

        # ── Right: main panel ──────────────────────────────────────────────────
        right = tk.Frame(body, bg=BG)
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self._notebook = ttk.Notebook(right)
        self._notebook.pack(fill=tk.BOTH, expand=True)

        s = ttk.Style(self)
        s.configure("TNotebook",     background=BG,  borderwidth=0)
        s.configure("TNotebook.Tab", background=BG3, foreground=FG_DIM,
                    padding=[14, 5], font=UI_SM)
        s.map("TNotebook.Tab",
              background=[("selected", BG)],
              foreground=[("selected", ACCENT)])

        self._build_tab_detect()
        self._build_tab_packages()
        self._build_tab_location()
        self._build_tab_log()

        # ── Bottom bar ─────────────────────────────────────────────────────────
        bot = tk.Frame(self, bg=BG2, pady=10)
        bot.pack(fill=tk.X, side=tk.BOTTOM)

        self.progress = ttk.Progressbar(bot, style="custom.Horizontal.TProgressbar",
                                        length=720, maximum=100)
        self.progress.pack(fill=tk.X, padx=0, pady=(0, 8))

        self.status_var = tk.StringVar(value="Detecting your environment…")
        tk.Label(bot, textvariable=self.status_var,
                 font=MONO, fg=FG_DIM, bg=BG2, anchor="w").pack(side=tk.LEFT, padx=16)

        self.btn_install = tk.Button(
            bot, text="Install  ▶",
            font=("Segoe UI", 10, "bold"),
            fg=BG, bg=ACCENT, activebackground="#00b8cc",
            relief=tk.FLAT, padx=18, pady=4,
            cursor="hand2", command=self._start_install)
        self.btn_install.pack(side=tk.RIGHT, padx=16)

        self.btn_launch = tk.Button(
            bot, text="Launch App  ▶",
            font=("Segoe UI", 10, "bold"),
            fg=BG, bg=GREEN, activebackground="#5ccd65",
            relief=tk.FLAT, padx=18, pady=4,
            cursor="hand2", command=self._launch_app,
            state=tk.DISABLED)
        self.btn_launch.pack(side=tk.RIGHT, padx=(0, 8))

    # ── TAB: DETECT ────────────────────────────────────────────────────────────
    def _build_tab_detect(self):
        f = tk.Frame(self._notebook, bg=BG, padx=20, pady=16)
        self._notebook.add(f, text="  Python  ")

        tk.Label(f, text="Python Installation", font=UI_H, fg=FG, bg=BG).pack(anchor="w")
        tk.Label(f, text="The tool requires Python 3.8 or newer.",
                 font=UI_SM, fg=FG_DIM, bg=BG).pack(anchor="w", pady=(2, 14))

        # Detection result card
        self._py_card = tk.Frame(f, bg=BG2, padx=16, pady=12)
        self._py_card.pack(fill=tk.X, pady=(0, 12))
        self._py_status_dot = tk.Label(self._py_card, text="●", fg=FG_DIM,
                                       bg=BG2, font=("Segoe UI", 18))
        self._py_status_dot.pack(side=tk.LEFT, padx=(0, 12))
        py_text = tk.Frame(self._py_card, bg=BG2)
        py_text.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self._py_title = tk.Label(py_text, text="Checking…",
                                  font=UI_H, fg=FG, bg=BG2)
        self._py_title.pack(anchor="w")
        self._py_sub = tk.Label(py_text, text="",
                                font=MONO, fg=FG_DIM, bg=BG2)
        self._py_sub.pack(anchor="w")

        # Manual path override
        tk.Label(f, text="Python executable path (override):",
                 font=UI_SM, fg=FG_DIM, bg=BG).pack(anchor="w", pady=(10, 3))
        row = tk.Frame(f, bg=BG)
        row.pack(fill=tk.X)
        self._py_path_var = tk.StringVar()
        tk.Entry(row, textvariable=self._py_path_var,
                 bg=BG3, fg=FG, insertbackground=FG,
                 relief=tk.FLAT, font=MONO,
                 highlightbackground=BG4, highlightthickness=1).pack(side=tk.LEFT, fill=tk.X,
                                                                     expand=True, ipady=5)
        tk.Button(row, text="Browse", font=UI_SM, fg=FG_DIM, bg=BG3,
                  activebackground=BG4, relief=tk.FLAT, padx=10,
                  cursor="hand2",
                  command=self._browse_python).pack(side=tk.LEFT, padx=(6, 0))
        tk.Button(row, text="Apply", font=UI_SM, fg=BG, bg=ACCENT,
                  activebackground="#00b8cc", relief=tk.FLAT, padx=10,
                  cursor="hand2",
                  command=self._apply_python_path).pack(side=tk.LEFT, padx=(4, 0))

        # Download Python button
        self._btn_dl_py = tk.Button(
            f, text="Download Python 3.12 from python.org",
            font=UI_SM, fg=FG_DIM, bg=BG3, activebackground=BG4,
            relief=tk.FLAT, padx=12, pady=6, cursor="hand2",
            command=self._download_python)
        self._btn_dl_py.pack(anchor="w", pady=(14, 0))
        tk.Label(f, text="Opens the official Python installer for your platform.",
                 font=("Courier New", 8), fg=FG_DARK, bg=BG).pack(anchor="w", pady=(3, 0))

    # ── TAB: PACKAGES ──────────────────────────────────────────────────────────
    def _build_tab_packages(self):
        f = tk.Frame(self._notebook, bg=BG, padx=20, pady=16)
        self._notebook.add(f, text="  Packages  ")

        tk.Label(f, text="Required Packages", font=UI_H, fg=FG, bg=BG).pack(anchor="w")
        tk.Label(f, text="Checked against your Python environment. Uncheck to skip.",
                 font=UI_SM, fg=FG_DIM, bg=BG).pack(anchor="w", pady=(2, 14))

        self._pkg_rows = {}
        for import_name, pip_name in REQUIRED_PACKAGES:
            row = tk.Frame(f, bg=BG2, padx=12, pady=8)
            row.pack(fill=tk.X, pady=(0, 4))

            var = tk.BooleanVar(value=True)
            cb  = ttk.Checkbutton(row, variable=var, style="TCheckbutton")
            cb.pack(side=tk.LEFT)

            name_lbl = tk.Label(row, text=pip_name, font=("Courier New", 10, "bold"),
                                fg=FG, bg=BG2, width=14, anchor="w")
            name_lbl.pack(side=tk.LEFT, padx=(6, 0))

            status_lbl = tk.Label(row, text="•  checking…",
                                  font=MONO, fg=FG_DIM, bg=BG2)
            status_lbl.pack(side=tk.LEFT, padx=(10, 0))

            self._pkg_rows[import_name] = {
                "var": var, "status": status_lbl, "pip": pip_name
            }

        tk.Button(f, text="Re-check installed packages",
                  font=UI_SM, fg=FG_DIM, bg=BG3, activebackground=BG4,
                  relief=tk.FLAT, padx=10, pady=4, cursor="hand2",
                  command=lambda: threading.Thread(
                      target=self._check_packages, daemon=True).start()
                  ).pack(anchor="w", pady=(12, 0))

    # ── TAB: LOCATION ──────────────────────────────────────────────────────────
    def _build_tab_location(self):
        f = tk.Frame(self._notebook, bg=BG, padx=20, pady=16)
        self._notebook.add(f, text="  Location  ")

        tk.Label(f, text="Install Location", font=UI_H, fg=FG, bg=BG).pack(anchor="w")
        tk.Label(f,
                 text="Choose where to install mullvad_ping.py.\nA shortcut / launcher script is also created.",
                 font=UI_SM, fg=FG_DIM, bg=BG, justify="left").pack(anchor="w", pady=(2, 14))

        row = tk.Frame(f, bg=BG)
        row.pack(fill=tk.X)
        tk.Entry(row, textvariable=self._install_dir,
                 bg=BG3, fg=FG, insertbackground=FG,
                 relief=tk.FLAT, font=MONO,
                 highlightbackground=BG4, highlightthickness=1).pack(side=tk.LEFT, fill=tk.X,
                                                                     expand=True, ipady=5)
        tk.Button(row, text="Browse", font=UI_SM, fg=FG_DIM, bg=BG3,
                  activebackground=BG4, relief=tk.FLAT, padx=10, cursor="hand2",
                  command=self._browse_dir).pack(side=tk.LEFT, padx=(6, 0))

        # Options
        opts = tk.Frame(f, bg=BG, pady=14)
        opts.pack(fill=tk.X)
        self._opt_desktop = tk.BooleanVar(value=True)
        self._opt_startmenu = tk.BooleanVar(value=True)
        self._opt_launch_after = tk.BooleanVar(value=True)

        for var, text in [
            (self._opt_desktop,     "Create desktop shortcut  (Windows)"),
            (self._opt_startmenu,   "Add to Start Menu  (Windows)"),
            (self._opt_launch_after,"Launch app after installation"),
        ]:
            row2 = tk.Frame(opts, bg=BG)
            row2.pack(fill=tk.X, pady=2)
            tk.Checkbutton(row2, variable=var, bg=BG, activebackground=BG,
                           fg=FG, selectcolor=BG3, relief=tk.FLAT,
                           font=UI_SM, text=text,
                           highlightthickness=0).pack(side=tk.LEFT)

        # Source selection
        tk.Label(f, text="Source for mullvad_ping.py:",
                 font=UI_SM, fg=FG_DIM, bg=BG).pack(anchor="w", pady=(10, 4))

        # GitHub option (default — highlighted)
        gh_card = tk.Frame(f, bg=BG2, padx=12, pady=8)
        gh_card.pack(fill=tk.X, pady=(0, 4))
        tk.Radiobutton(gh_card, variable=self._source_var, value="github",
                       text="Download latest from GitHub  (recommended)",
                       bg=BG2, fg=ACCENT, activebackground=BG2,
                       selectcolor=BG3, font=('Segoe UI', 9, 'bold'),
                       highlightthickness=0).pack(anchor="w")
        tk.Label(gh_card,
                 text=f"  {MAIN_SCRIPT_GITHUB}",
                 font=('Courier New', 8), fg=FG_DIM, bg=BG2).pack(anchor="w")

        # Local fallback
        local_card = tk.Frame(f, bg=BG, padx=2, pady=4)
        local_card.pack(fill=tk.X)
        tk.Radiobutton(local_card, variable=self._source_var, value="local",
                       text="Use local copy  (mullvad_ping.py next to this installer)",
                       bg=BG, fg=FG_DIM, activebackground=BG,
                       selectcolor=BG3, font=UI_SM,
                       highlightthickness=0).pack(anchor="w")

    # ── TAB: LOG ───────────────────────────────────────────────────────────────
    def _build_tab_log(self):
        f = tk.Frame(self._notebook, bg=BG)
        self._notebook.add(f, text="  Log  ")

        self._log = tk.Text(f, bg=BG2, fg=FG_DIM, font=MONO,
                            relief=tk.FLAT, state=tk.DISABLED,
                            wrap=tk.WORD, insertbackground=FG)
        sb = tk.Scrollbar(f, command=self._log.yview, bg=BG3, troughcolor=BG3,
                          relief=tk.FLAT, width=10)
        self._log.configure(yscrollcommand=sb.set)
        self._log.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)

        self._log.tag_configure("ok",   foreground=GREEN)
        self._log.tag_configure("err",  foreground=RED)
        self._log.tag_configure("warn", foreground=YELLOW)
        self._log.tag_configure("info", foreground=ACCENT)
        self._log.tag_configure("dim",  foreground=FG_DIM)

    def _log_write(self, msg, tag="dim"):
        self._log.configure(state=tk.NORMAL)
        self._log.insert(tk.END, msg + "\n", tag)
        self._log.see(tk.END)
        self._log.configure(state=tk.DISABLED)

    # ── DETECTION ─────────────────────────────────────────────────────────────
    def _auto_detect(self):
        threading.Thread(target=self._detect_all, daemon=True).start()

    def _detect_all(self):
        self._set_step("detect", "active")
        self._set_status("Detecting Python…")
        cmd, ver = find_python()
        self._python_cmd = cmd
        self._python_ver = ver
        self.after(0, self._update_python_card)

        if cmd:
            self._check_packages()
        self._set_step("detect", "done")
        self._set_status("Detection complete.")
        self.after(0, lambda: self.progress.configure(value=20))

    def _update_python_card(self):
        if self._python_cmd:
            self._py_status_dot.config(fg=GREEN)
            self._py_title.config(text=f"Python {self._python_ver}  found", fg=FG)
            path = shutil.which(self._python_cmd) or self._python_cmd
            self._py_sub.config(text=path)
            self._py_path_var.set(path)
            self._log_write(f"[detect]  Python {self._python_ver} at {path}", "ok")
        else:
            self._py_status_dot.config(fg=RED)
            self._py_title.config(text="Python not found", fg=RED)
            self._py_sub.config(text="Install Python 3.8+ or set the path manually.")
            self._log_write("[detect]  No Python 3 installation found.", "err")

    def _check_packages(self):
        if not self._python_cmd:
            for pkg in REQUIRED_PACKAGES:
                self._set_pkg_status(pkg[0], "skip", "—  no Python")
            return
        installed = pip_list(self._python_cmd)
        self._log_write("[packages]  Checking installed packages…", "info")
        for import_name, pip_name in REQUIRED_PACKAGES:
            if pip_name.lower() in installed or import_name.lower() in installed:
                self._set_pkg_status(import_name, "ok", f"✓  installed")
                self._installed_ok.add(import_name)
                self._log_write(f"  {pip_name:12}  already installed", "ok")
            else:
                self._set_pkg_status(import_name, "warn", "⚠  not found — will install")
                self._log_write(f"  {pip_name:12}  not found", "warn")

    def _set_pkg_status(self, import_name, level, msg):
        colors = {"ok": GREEN, "warn": YELLOW, "err": RED, "skip": FG_DIM}
        color  = colors.get(level, FG_DIM)
        self.after(0, lambda: self._pkg_rows[import_name]["status"].config(
            text=msg, fg=color))

    # ── PYTHON MANAGEMENT ─────────────────────────────────────────────────────
    def _browse_python(self):
        path = filedialog.askopenfilename(
            title="Select Python executable",
            filetypes=[("Python", "python*.exe python3*"), ("All", "*")])
        if path:
            self._py_path_var.set(path)

    def _apply_python_path(self):
        path = self._py_path_var.get().strip()
        if not path:
            return
        try:
            r = subprocess.run([path, "--version"], capture_output=True, text=True, timeout=5)
            ver = (r.stdout + r.stderr).strip()
            if "Python 3" in ver:
                self._python_cmd = path
                self._python_ver = ver.split()[-1]
                self._update_python_card()
                threading.Thread(target=self._check_packages, daemon=True).start()
            else:
                messagebox.showerror("Not Python 3", f"That executable returned:\n{ver}")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def _download_python(self):
        system = platform.system()
        if system == "Windows":
            url = PYTHON_DOWNLOAD_WIN
        elif system == "Darwin":
            url = PYTHON_DOWNLOAD_MAC
        else:
            messagebox.showinfo("Linux",
                "Use your package manager to install Python 3:\n\n"
                "  sudo apt install python3 python3-pip  (Debian/Ubuntu)\n"
                "  sudo dnf install python3              (Fedora)\n"
                "  sudo pacman -S python                 (Arch)")
            return
        import webbrowser
        webbrowser.open(url)
        self._log_write(f"[python]  Opened Python download: {url}", "info")

    # ── LOCATION ───────────────────────────────────────────────────────────────
    def _browse_dir(self):
        d = filedialog.askdirectory(title="Choose install directory")
        if d:
            self._install_dir.set(d)

    # ── INSTALL ────────────────────────────────────────────────────────────────
    def _set_step(self, key, state):
        colors = {"active": ACCENT, "done": GREEN, "err": RED, "idle": FG_DIM}
        col = colors.get(state, FG_DIM)
        self.after(0, lambda: self._step_labels[key].config(fg=col))

    def _set_status(self, msg):
        self.after(0, lambda: self.status_var.set(msg))

    def _set_progress(self, val):
        self.after(0, lambda: self.progress.configure(value=val))

    def _start_install(self):
        if not self._python_cmd:
            messagebox.showerror("No Python",
                "Python was not found.\n\n"
                "Please install Python 3.8+ and re-run this installer,\n"
                "or set the path manually in the Python tab.")
            return
        self.btn_install.config(state=tk.DISABLED, text="Installing…")
        self._notebook.select(3)  # Switch to Log tab
        threading.Thread(target=self._run_install, daemon=True).start()

    def _run_install(self):
        try:
            # Step 1: pip upgrade
            self._set_step("packages", "active")
            self._set_status("Upgrading pip…")
            self._log_write("\n── Upgrading pip ──────────────────", "info")
            subprocess.run([self._python_cmd, "-m", "pip", "install",
                            "--upgrade", "pip"],
                           capture_output=True, timeout=60)
            self._log_write("pip up to date.", "ok")
            self._set_progress(30)

            # Step 2: install packages
            total = len(REQUIRED_PACKAGES)
            for i, (import_name, pip_name) in enumerate(REQUIRED_PACKAGES, 1):
                pkg_data = self._pkg_rows[import_name]
                if not pkg_data["var"].get():
                    self._log_write(f"  {pip_name:12}  skipped (unchecked)", "dim")
                    continue
                if import_name in self._installed_ok:
                    self._log_write(f"  {pip_name:12}  already installed — skipping", "ok")
                    self._set_pkg_status(import_name, "ok", "✓  already installed")
                    self._set_progress(30 + int(30 * i / total))
                    continue

                self._set_status(f"Installing {pip_name}…")
                self._log_write(f"\n── Installing {pip_name} ──────────────", "info")
                self._set_pkg_status(import_name, "warn", "⟳  installing…")
                ok = install_package(self._python_cmd, pip_name, lambda l: self._log_write("  " + l))
                if ok:
                    self._set_pkg_status(import_name, "ok", "✓  installed")
                    self._log_write(f"  {pip_name} installed successfully.", "ok")
                else:
                    self._set_pkg_status(import_name, "err", "✗  failed")
                    self._log_write(f"  ERROR: {pip_name} installation failed.", "err")
                self._set_progress(30 + int(30 * i / total))

            self._set_step("packages", "done")

            # Step 3: create install directory
            self._set_step("location", "active")
            install_dir = Path(self._install_dir.get())
            self._set_status(f"Creating {install_dir}…")
            self._log_write(f"\n── Creating directory: {install_dir} ──", "info")
            install_dir.mkdir(parents=True, exist_ok=True)
            self._log_write("  Directory ready.", "ok")
            self._set_progress(65)

            # Step 4: copy / download main script
            self._set_step("download", "active")
            dest = install_dir / MAIN_SCRIPT_NAME

            if self._source_var.get() == "github":
                self._set_status("Downloading mullvad_ping.py from GitHub…")
                self._log_write("\n── Downloading mullvad_ping.py from GitHub ──", "info")
                self._log_write(f"  URL: {MAIN_SCRIPT_GITHUB}", "dim")
                try:
                    req = urllib.request.Request(
                        MAIN_SCRIPT_GITHUB,
                        headers={"User-Agent": "MullvadPingInstaller/2.0"})
                    with urllib.request.urlopen(req, timeout=30) as resp:
                        data = resp.read()
                    dest.write_bytes(data)
                    self._log_write(f"  ✓  Downloaded {len(data):,} bytes to {dest}", "ok")
                except Exception as e:
                    self._log_write(f"  Download failed: {e}", "err")
                    self._log_write("  Falling back to local copy next to installer…", "warn")
                    self._copy_local(dest)
            else:
                self._copy_local(dest)

            self._set_progress(75)

            # Step 5: create launcher script
            self._set_status("Creating launcher…")
            self._log_write("\n── Creating launcher ─────────────────", "info")
            self._create_launcher(install_dir, dest)
            self._set_progress(85)

            # Step 6: shortcuts
            if platform.system() == "Windows":
                if self._opt_desktop.get():
                    self._create_shortcut_windows(install_dir, dest, "desktop")
                if self._opt_startmenu.get():
                    self._create_shortcut_windows(install_dir, dest, "startmenu")

            self._set_step("location", "done")
            self._set_step("download", "done")
            self._set_step("launch",   "done")
            self._set_progress(100)
            self._set_status("Installation complete!")
            self._log_write("\n✓  Installation complete!", "ok")
            self._log_write(f"   Location: {install_dir}", "ok")
            self._log_write(f"   Run with: {self._python_cmd} \"{dest}\"", "ok")

            self.after(0, lambda: self.btn_launch.config(state=tk.NORMAL))

            if self._opt_launch_after.get():
                self.after(500, self._launch_app)

        except Exception as e:
            self._log_write(f"\nInstall error: {e}", "err")
            self._set_status(f"Error: {e}")
        finally:
            self.after(0, lambda: self.btn_install.config(
                state=tk.NORMAL, text="Re-install  ▶"))

    def _copy_local(self, dest):
        # Look next to the installer exe/script
        exe_dir = Path(sys.executable).parent
        script_dir = Path(__file__).parent if not getattr(sys, "frozen", False) else exe_dir
        candidates = [
            script_dir / MAIN_SCRIPT_NAME,
            exe_dir    / MAIN_SCRIPT_NAME,
            Path.cwd() / MAIN_SCRIPT_NAME,
        ]
        for src in candidates:
            if src.exists():
                shutil.copy2(src, dest)
                self._log_write(f"  Copied from {src}", "ok")
                return
        self._log_write(
            f"  WARNING: {MAIN_SCRIPT_NAME} not found next to installer.\n"
            "  Place mullvad_ping.py in the same folder as this installer,\n"
            "  or select 'Download from GitHub' in the Location tab.", "warn")

    def _create_launcher(self, install_dir, script_path):
        py = self._python_cmd or "python"
        if platform.system() == "Windows":
            bat = install_dir / "Run MullvadPing.bat"
            bat.write_text(
                f'@echo off\n"{py}" "{script_path}"\n', encoding="utf-8")
            self._log_write(f"  Launcher: {bat}", "ok")
        else:
            sh = install_dir / "run_mullvad_ping.sh"
            sh.write_text(
                f'#!/bin/bash\n"{py}" "{script_path}"\n', encoding="utf-8")
            sh.chmod(0o755)
            self._log_write(f"  Launcher: {sh}", "ok")

    def _create_shortcut_windows(self, install_dir, script_path, target):
        try:
            import winreg  # noqa: F401 — only available on Windows
            if target == "desktop":
                desktop = Path(os.path.join(os.environ.get("USERPROFILE", "~"),
                                            "Desktop"))
                shortcut = desktop / "Mullvad Ping Tool.bat"
            else:
                sm = Path(os.environ.get("APPDATA", "~")) / \
                     "Microsoft/Windows/Start Menu/Programs"
                sm.mkdir(parents=True, exist_ok=True)
                shortcut = sm / "Mullvad Ping Tool.bat"
            shortcut.write_text(
                f'@echo off\n"{self._python_cmd}" "{script_path}"\n',
                encoding="utf-8")
            self._log_write(f"  Shortcut: {shortcut}", "ok")
        except Exception as e:
            self._log_write(f"  Could not create shortcut: {e}", "warn")

    # ── LAUNCH ─────────────────────────────────────────────────────────────────
    def _launch_app(self):
        dest = Path(self._install_dir.get()) / MAIN_SCRIPT_NAME
        if not dest.exists():
            # Try next to installer
            fallback = Path(__file__).parent / MAIN_SCRIPT_NAME
            if fallback.exists():
                dest = fallback
            else:
                messagebox.showerror("Not found",
                    f"{MAIN_SCRIPT_NAME} was not found.\n\n"
                    "Run the installer first, or ensure the file\n"
                    "is in the install directory.")
                return
        self._log_write(f"\n[launch]  Starting {dest}…", "info")
        try:
            subprocess.Popen([self._python_cmd, str(dest)],
                             creationflags=0x00000008 if platform.system() == "Windows" else 0)
        except Exception as e:
            messagebox.showerror("Launch failed", str(e))


if __name__ == "__main__":
    app = InstallerApp()
    app.mainloop()
