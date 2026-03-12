"""
Mullvad LAX WireGuard Server Ping Tool
  - IP-based location detection (with user permission)
  - Live results table
  - Seaborn/matplotlib statistics dashboard
  - Static map with user location + lines to each datacenter
  - Interactive Folium map
"""

import tkinter as tk
from tkinter import ttk
import threading
import subprocess
import platform
import re
import webbrowser
import tempfile
import urllib.request
import urllib.error
import urllib.parse
import json
import math

import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
import matplotlib.patches as mpatches
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import seaborn as sns
import pandas as pd
import numpy as np
import folium

# ── SERVERS ────────────────────────────────────────────────────────────────────
SERVERS = [
    "us-lax-wg-001.relays.mullvad.net","us-lax-wg-002.relays.mullvad.net",
    "us-lax-wg-003.relays.mullvad.net","us-lax-wg-004.relays.mullvad.net",
    "us-lax-wg-005.relays.mullvad.net","us-lax-wg-006.relays.mullvad.net",
    "us-lax-wg-007.relays.mullvad.net","us-lax-wg-008.relays.mullvad.net",
    "us-lax-wg-201.relays.mullvad.net","us-lax-wg-202.relays.mullvad.net",
    "us-lax-wg-203.relays.mullvad.net","us-lax-wg-402.relays.mullvad.net",
    "us-lax-wg-403.relays.mullvad.net","us-lax-wg-404.relays.mullvad.net",
    "us-lax-wg-405.relays.mullvad.net","us-lax-wg-406.relays.mullvad.net",
    "us-lax-wg-407.relays.mullvad.net","us-lax-wg-408.relays.mullvad.net",
    "us-lax-wg-409.relays.mullvad.net","us-lax-wg-601.relays.mullvad.net",
    "us-lax-wg-602.relays.mullvad.net","us-lax-wg-603.relays.mullvad.net",
    "us-lax-wg-604.relays.mullvad.net","us-lax-wg-605.relays.mullvad.net",
    "us-lax-wg-606.relays.mullvad.net","us-lax-wg-607.relays.mullvad.net",
    "us-lax-wg-608.relays.mullvad.net","us-lax-wg-701.relays.mullvad.net",
    "us-lax-wg-702.relays.mullvad.net","us-lax-wg-703.relays.mullvad.net",
    "us-lax-wg-704.relays.mullvad.net",
]

DATACENTER_INFO = {
    "LAX-A (001-008)": {
        "servers": [s for s in SERVERS if re.search(r"wg-00[1-8]", s)],
        "lat": 34.0522, "lon": -118.2437,
        "location": "CoreSite LA1 - Downtown Los Angeles",
        "color": "#00e5ff",
    },
    "LAX-B (201-203)": {
        "servers": [s for s in SERVERS if re.search(r"wg-20[123]", s)],
        "lat": 33.9425, "lon": -118.4081,
        "location": "Equinix LA3 - El Segundo (near LAX airport)",
        "color": "#7ee787",
    },
    "LAX-C (402-409)": {
        "servers": [s for s in SERVERS if re.search(r"wg-40[2-9]", s)],
        "lat": 34.1808, "lon": -118.3090,
        "location": "Zayo Burbank - Media District",
        "color": "#e3b341",
    },
    "LAX-D (601-608)": {
        "servers": [s for s in SERVERS if re.search(r"wg-60[1-8]", s)],
        "lat": 33.6846, "lon": -117.8265,
        "location": "Equinix LA4 - Irvine / Orange County",
        "color": "#f78166",
    },
    "LAX-E (701-704)": {
        "servers": [s for s in SERVERS if re.search(r"wg-70[1-4]", s)],
        "lat": 33.7701, "lon": -118.1937,
        "location": "CoreSite LA2 - Long Beach",
        "color": "#bc8cff",
    },
}

GROUP_PALETTE = {k: v["color"] for k, v in DATACENTER_INFO.items()}

def server_group(server):
    n = int(re.search(r"wg-(\d+)", server).group(1))
    if n < 100:  return "LAX-A (001-008)"
    if n < 300:  return "LAX-B (201-203)"
    if n < 500:  return "LAX-C (402-409)"
    if n < 700:  return "LAX-D (601-608)"
    return             "LAX-E (701-704)"

# ── THEME ──────────────────────────────────────────────────────────────────────
BG     = "#0d1117"
BG2    = "#161b22"
BG3    = "#21262d"
ACCENT = "#00e5ff"
GREEN  = "#7ee787"
RED    = "#f85149"
YELLOW = "#e3b341"
ORANGE = "#ff9500"
FG     = "#e6edf3"
FG_DIM = "#8b949e"
MONO   = ("Courier New", 10)
UI     = ("Segoe UI", 10)

# ── GEO HELPERS ────────────────────────────────────────────────────────────────
def haversine_km(lat1, lon1, lat2, lon2):
    """Straight-line distance between two lat/lon points in kilometres."""
    R = 6371.0
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    dphi  = math.radians(lat2 - lat1)
    dlam  = math.radians(lon2 - lon1)
    a = math.sin(dphi/2)**2 + math.cos(phi1)*math.cos(phi2)*math.sin(dlam/2)**2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1-a))

def fetch_location_ip():
    """
    Coarse IP-based location from ip-api.com. Used only as a fallback / prefill.
    Returns a dict or None.
    """
    try:
        url = "http://ip-api.com/json/?fields=status,message,country,regionName,city,lat,lon,isp,query"
        req = urllib.request.Request(url, headers={"User-Agent": "MullvadPingTool/1.0"})
        with urllib.request.urlopen(req, timeout=6) as resp:
            data = json.loads(resp.read().decode())
        if data.get("status") == "success":
            return {
                "lat":     data["lat"],
                "lon":     data["lon"],
                "city":    data.get("city", "Unknown"),
                "region":  data.get("regionName", ""),
                "country": data.get("country", ""),
                "isp":     data.get("isp", ""),
                "ip":      data.get("query", ""),
                "source":  "ip",
            }
    except Exception:
        pass
    return None


def geocode_address(query):
    """
    Geocode a free-text address/place via Nominatim (OpenStreetMap).
    Returns a list of result dicts, each with: lat, lon, display_name.
    Free — no API key required. Results are building/street accurate.
    """
    try:
        q = urllib.parse.quote(query)
        url = (f"https://nominatim.openstreetmap.org/search"
               f"?q={q}&format=json&addressdetails=1&limit=6")
        req = urllib.request.Request(
            url, headers={"User-Agent": "MullvadPingTool/1.0"})
        with urllib.request.urlopen(req, timeout=8) as resp:
            results = json.loads(resp.read().decode())
        out = []
        for r in results:
            addr = r.get("address", {})
            city    = (addr.get("city") or addr.get("town") or
                       addr.get("village") or addr.get("county") or "")
            region  = addr.get("state", "")
            country = addr.get("country", "")
            out.append({
                "lat":          float(r["lat"]),
                "lon":          float(r["lon"]),
                "display_name": r["display_name"],
                "city":         city,
                "region":       region,
                "country":      country,
                "source":       "address",
            })
        return out
    except Exception:
        return []

# ── PING HELPERS ───────────────────────────────────────────────────────────────
def ping_server(host, count=4):
    flag = "-n" if platform.system() == "Windows" else "-c"
    try:
        r = subprocess.run(["ping", flag, str(count), host],
                           capture_output=True, text=True, timeout=20)
        out = r.stdout + r.stderr
        win  = re.search(r"Minimum = (\d+)ms.*Maximum = (\d+)ms.*Average = (\d+)ms", out)
        unix = re.search(r"min/avg/max.*?=\s*([\d.]+)/([\d.]+)/([\d.]+)", out)
        loss_m = re.search(r"(\d+)%\s*(packet\s*)?loss", out, re.IGNORECASE)
        loss = int(loss_m.group(1)) if loss_m else 100
        if win:
            return int(win.group(3)), int(win.group(1)), int(win.group(2)), loss
        elif unix:
            v = [float(x) for x in [unix.group(1), unix.group(2), unix.group(3)]]
            return v[1], v[0], v[2], loss
        elif loss == 100:
            return None
    except Exception:
        pass
    return None

def ms_tag(avg):
    if avg is None or avg >= 999: return "dead"
    if avg < 30:  return "good"
    if avg < 70:  return "ok"
    if avg < 120: return "slow"
    return "bad"

def ping_hex(avg):
    if avg is None: return FG_DIM
    if avg < 30:  return GREEN
    if avg < 70:  return ACCENT
    if avg < 120: return YELLOW
    return RED

def ping_folium_color(avg):
    if avg is None: return "#8b949e"
    if avg < 30:  return "#7ee787"
    if avg < 70:  return "#00e5ff"
    if avg < 120: return "#e3b341"
    return "#f85149"

# ── LOCATION DIALOG ────────────────────────────────────────────────────────────
class LocationDialog(tk.Toplevel):
    """
    Address-search dialog backed by Nominatim (OpenStreetMap).
    Street / neighbourhood / city accurate — no API key required.

    self.location is set to the chosen result dict on confirm, else None.
    """
    def __init__(self, parent, prefill=""):
        super().__init__(parent)
        self.location = None
        self._results = []        # list of geocode result dicts
        self._selected = None     # index into _results

        self.title("Set Your Location")
        self.configure(bg=BG)
        self.resizable(False, False)
        self.grab_set()
        self.transient(parent)
        self.geometry("540x580")

        self._build_ui(prefill)
        self._centre(parent)

        # Pre-fill from IP on first open (non-blocking)
        if prefill:
            self._search_var.set(prefill)

    def _centre(self, parent):
        self.update_idletasks()
        px = parent.winfo_x() + parent.winfo_width()  // 2
        py = parent.winfo_y() + parent.winfo_height() // 2
        w, h = self.winfo_width(), self.winfo_height()
        self.geometry(f"+{px - w//2}+{py - h//2}")

    def _build_ui(self, prefill):
        outer = tk.Frame(self, bg=BG, padx=28, pady=24)
        outer.pack(fill=tk.BOTH, expand=True)

        # ── Title ─────────────────────────────────────────────────────────────
        title_row = tk.Frame(outer, bg=BG)
        title_row.pack(fill=tk.X, pady=(0, 4))
        tk.Label(title_row, text="◎", font=("Segoe UI", 22),
                 fg=ACCENT, bg=BG).pack(side=tk.LEFT, padx=(0, 10))
        tk.Label(title_row, text="Set Your Location",
                 font=("Segoe UI", 14, "bold"), fg=FG, bg=BG).pack(side=tk.LEFT)
        tk.Frame(outer, bg=BG3, height=1).pack(fill=tk.X, pady=(8, 14))

        # ── Search bar ────────────────────────────────────────────────────────
        tk.Label(outer, text="Enter your address, neighbourhood, city, or zip code:",
                 font=("Segoe UI", 10), fg=FG_DIM, bg=BG).pack(anchor="w")

        search_row = tk.Frame(outer, bg=BG)
        search_row.pack(fill=tk.X, pady=(6, 0))

        self._search_var = tk.StringVar(value=prefill)
        self._entry = tk.Entry(
            search_row, textvariable=self._search_var,
            bg=BG3, fg=FG, insertbackground=FG, relief=tk.FLAT,
            font=("Segoe UI", 11),
            highlightbackground=ACCENT, highlightthickness=1)
        self._entry.pack(side=tk.LEFT, fill=tk.X, expand=True, ipady=7)
        self._entry.bind("<Return>", lambda e: self._do_search())
        self._entry.focus_set()

        self._search_btn = tk.Button(
            search_row, text="Search",
            font=("Segoe UI", 10, "bold"), fg=BG, bg=ACCENT,
            activebackground="#00b8cc", relief=tk.FLAT,
            padx=14, pady=7, cursor="hand2",
            command=self._do_search)
        self._search_btn.pack(side=tk.LEFT, padx=(6, 0))

        # ── Status line ───────────────────────────────────────────────────────
        self._status_var = tk.StringVar(value="Type an address and press Search.")
        tk.Label(outer, textvariable=self._status_var,
                 font=("Courier New", 9), fg=FG_DIM, bg=BG,
                 anchor="w").pack(fill=tk.X, pady=(6, 4))

        # ── Results list ──────────────────────────────────────────────────────
        list_frame = tk.Frame(outer, bg=BG2)
        list_frame.pack(fill=tk.BOTH, expand=True)

        self._listbox = tk.Listbox(
            list_frame,
            bg=BG2, fg=FG, selectbackground=BG3, selectforeground=ACCENT,
            activestyle="none", relief=tk.FLAT,
            font=("Segoe UI", 9), borderwidth=0,
            highlightthickness=0)
        sb = tk.Scrollbar(list_frame, orient=tk.VERTICAL,
                          command=self._listbox.yview,
                          bg=BG3, troughcolor=BG3, relief=tk.FLAT, width=8)
        self._listbox.configure(yscrollcommand=sb.set)
        self._listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self._listbox.bind("<<ListboxSelect>>", self._on_select)
        self._listbox.bind("<Double-Button-1>", lambda e: self._confirm())

        # ── Selected preview card ─────────────────────────────────────────────
        self._preview = tk.Frame(outer, bg=BG2, padx=14, pady=10)
        self._preview.pack(fill=tk.X, pady=(8, 0))
        self._prev_title = tk.Label(self._preview, text="No result selected",
                                    font=("Segoe UI", 10, "bold"),
                                    fg=FG_DIM, bg=BG2, anchor="w")
        self._prev_title.pack(fill=tk.X)
        self._prev_coords = tk.Label(self._preview, text="",
                                     font=("Courier New", 9),
                                     fg=FG_DIM, bg=BG2, anchor="w")
        self._prev_coords.pack(fill=tk.X)

        # ── Footer buttons ────────────────────────────────────────────────────
        tk.Frame(outer, bg=BG3, height=1).pack(fill=tk.X, pady=(14, 10))
        btn_row = tk.Frame(outer, bg=BG)
        btn_row.pack(fill=tk.X)

        tk.Button(btn_row, text="Use IP Location Instead",
                  font=("Segoe UI", 9), fg=FG_DIM, bg=BG3,
                  activebackground=BG2, relief=tk.FLAT,
                  padx=12, pady=5, cursor="hand2",
                  command=self._use_ip).pack(side=tk.LEFT)

        tk.Button(btn_row, text="Cancel",
                  font=("Segoe UI", 10), fg=FG_DIM, bg=BG3,
                  activebackground=BG2, relief=tk.FLAT,
                  padx=14, pady=5, cursor="hand2",
                  command=self.destroy).pack(side=tk.RIGHT, padx=(6, 0))

        self._confirm_btn = tk.Button(
            btn_row, text="Use This Location  ✓",
            font=("Segoe UI", 10, "bold"), fg=BG, bg=ACCENT,
            activebackground="#00b8cc", relief=tk.FLAT,
            padx=14, pady=5, cursor="hand2",
            state=tk.DISABLED,
            command=self._confirm)
        self._confirm_btn.pack(side=tk.RIGHT)

    # ── Search ────────────────────────────────────────────────────────────────
    def _do_search(self):
        query = self._search_var.get().strip()
        if not query:
            return
        self._status_var.set("Searching…")
        self._search_btn.config(state=tk.DISABLED)
        self._listbox.delete(0, tk.END)
        self._results = []
        self._selected = None
        self._confirm_btn.config(state=tk.DISABLED)
        self._prev_title.config(text="No result selected", fg=FG_DIM)
        self._prev_coords.config(text="")
        threading.Thread(target=self._fetch_results, args=(query,), daemon=True).start()

    def _fetch_results(self, query):
        results = geocode_address(query)
        self.after(0, self._populate_results, results)

    def _populate_results(self, results):
        self._search_btn.config(state=tk.NORMAL)
        self._results = results
        self._listbox.delete(0, tk.END)
        if not results:
            self._status_var.set("No results found. Try a different address or city.")
            return
        self._status_var.set(f"{len(results)} result(s) — click one to select.")
        for r in results:
            # Truncate long display names to fit the listbox width
            name = r["display_name"]
            if len(name) > 72:
                name = name[:69] + "…"
            self._listbox.insert(tk.END, f"  {name}")

    def _on_select(self, event):
        sel = self._listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        self._selected = idx
        r = self._results[idx]
        label = r["city"]
        if r.get("region"):
            label += f", {r['region']}"
        if r.get("country"):
            label += f", {r['country']}"
        self._prev_title.config(
            text=label or r["display_name"][:60], fg=FG)
        self._prev_coords.config(
            text=f"  {r['lat']:.5f}, {r['lon']:.5f}  —  {r['display_name'][:80]}")
        self._confirm_btn.config(state=tk.NORMAL)

    def _confirm(self):
        if self._selected is None:
            return
        self.location = self._results[self._selected]
        self.destroy()

    def _use_ip(self):
        """Fall back to IP-based lookup and close."""
        self._status_var.set("Fetching IP location…")
        threading.Thread(target=self._fetch_ip, daemon=True).start()

    def _fetch_ip(self):
        loc = fetch_location_ip()
        self.after(0, self._on_ip_result, loc)

    def _on_ip_result(self, loc):
        if loc:
            self.location = loc
            self.destroy()
        else:
            self._status_var.set("IP location failed. Please enter an address manually.")


# ── MAIN APP ───────────────────────────────────────────────────────────────────
class MullvadApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Mullvad LAX  |  WireGuard Latency Monitor")
        self.configure(bg=BG)
        self.geometry("1280x880")
        self.minsize(960, 700)

        self.results  = {}
        self.running  = False
        self._map_tmp = None
        self._stats_canvas_widget = None
        self._map_canvas_widget   = None
        self._dc_stat_labels      = {}

        # Location state
        self._user_loc     = None   # dict or None
        self._loc_allowed  = False

        self._apply_ttk_style()
        self._build_header()
        self._build_notebook()

        # Ask for location after window is visible
        self.after(400, self._request_location)

    # ── STYLE ──────────────────────────────────────────────────────────────────
    def _apply_ttk_style(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        s.configure("TNotebook",     background=BG,  borderwidth=0)
        s.configure("TNotebook.Tab", background=BG3, foreground=FG_DIM,
                    padding=[16, 6], font=("Segoe UI", 10))
        s.map("TNotebook.Tab",
              background=[("selected", BG2)], foreground=[("selected", ACCENT)])
        s.configure("Treeview",
                    background=BG2, foreground=FG, fieldbackground=BG2,
                    rowheight=26, borderwidth=0, font=MONO)
        s.configure("Treeview.Heading",
                    background=BG3, foreground=FG_DIM,
                    font=("Segoe UI", 9, "bold"), relief="flat")
        s.map("Treeview",
              background=[("selected", BG3)], foreground=[("selected", ACCENT)])
        s.configure("custom.Horizontal.TProgressbar",
                    troughcolor=BG3, background=ACCENT,
                    darkcolor=ACCENT, lightcolor=ACCENT,
                    bordercolor=BG3, relief="flat")

    # ── HEADER ─────────────────────────────────────────────────────────────────
    def _build_header(self):
        h = tk.Frame(self, bg=BG2, pady=10)
        h.pack(fill=tk.X)
        tk.Label(h, text="  MULLVAD", font=("Courier New", 17, "bold"),
                 fg=ACCENT, bg=BG2).pack(side=tk.LEFT, padx=18)
        tk.Label(h, text="LAX WireGuard  |  Latency Monitor",
                 font=UI, fg=FG_DIM, bg=BG2).pack(side=tk.LEFT)

        self.btn = tk.Button(
            h, text="  Run Ping Test", font=("Segoe UI", 10, "bold"),
            fg=BG, bg=ACCENT, activebackground="#00b8cc",
            relief=tk.FLAT, padx=16, pady=5, cursor="hand2",
            command=self.start_pinging)
        self.btn.pack(side=tk.RIGHT, padx=18)

        # Location badge (right of title, left of run button)
        self._loc_badge_frame = tk.Frame(h, bg=BG3, padx=10, pady=4)
        self._loc_badge_frame.pack(side=tk.RIGHT, padx=(0, 8))
        self._loc_dot   = tk.Label(self._loc_badge_frame, text="◎",
                                   fg=FG_DIM, bg=BG3, font=("Segoe UI", 11))
        self._loc_dot.pack(side=tk.LEFT, padx=(0, 6))
        self._loc_text  = tk.Label(self._loc_badge_frame,
                                   text="Location: not set",
                                   font=("Courier New", 9), fg=FG_DIM, bg=BG3)
        self._loc_text.pack(side=tk.LEFT)
        self._loc_badge_frame.bind("<Button-1>", lambda e: self._request_location(force=True))
        self._loc_dot.bind("<Button-1>",         lambda e: self._request_location(force=True))
        self._loc_text.bind("<Button-1>",        lambda e: self._request_location(force=True))
        tk.Label(self._loc_badge_frame, text="↺",
                 fg=FG_DIM, bg=BG3, font=("Segoe UI", 10), cursor="hand2").pack(side=tk.LEFT, padx=(4,0))

        # Progress + status
        pf = tk.Frame(self, bg=BG, pady=4)
        pf.pack(fill=tk.X, padx=18)
        self.status_var = tk.StringVar(value="Ready — press Run Ping Test.")
        tk.Label(pf, textvariable=self.status_var,
                 font=MONO, fg=FG_DIM, bg=BG, anchor="w").pack(fill=tk.X)
        self.progress = ttk.Progressbar(pf, style="custom.Horizontal.TProgressbar",
                                        maximum=len(SERVERS))
        self.progress.pack(fill=tk.X, pady=(3, 0))

        # Summary stat cards
        cf = tk.Frame(self, bg=BG, pady=6)
        cf.pack(fill=tk.X, padx=18)
        self.cards = {}
        for lbl in ["Best Server", "Worst Server", "Avg Latency", "Reachable"]:
            c = tk.Frame(cf, bg=BG2, padx=16, pady=8)
            c.pack(side=tk.LEFT, expand=True, fill=tk.BOTH, padx=(0, 8))
            tk.Label(c, text=lbl.upper(), font=("Courier New", 8),
                     fg=FG_DIM, bg=BG2).pack(anchor="w")
            v   = tk.Label(c, text="--", font=("Segoe UI", 13, "bold"), fg=ACCENT, bg=BG2)
            v.pack(anchor="w")
            sub = tk.Label(c, text="", font=MONO, fg=FG_DIM, bg=BG2)
            sub.pack(anchor="w")
            self.cards[lbl] = (v, sub)

    # ── LOCATION ───────────────────────────────────────────────────────────────
    def _request_location(self, force=False):
        """Open the address-search dialog. Pre-fill with IP city on first open."""
        prefill = ""
        if not self._loc_allowed:
            # Silent IP fetch just to pre-fill the search box
            try:
                ip_loc = fetch_location_ip()
                if ip_loc:
                    prefill = f"{ip_loc['city']}, {ip_loc.get('region','')}"
            except Exception:
                pass

        dlg = LocationDialog(self, prefill=prefill)
        self.wait_window(dlg)

        if dlg.location:
            self._loc_allowed = True
            self.after(50, self._on_location_result, dlg.location)
        else:
            if not self._loc_allowed:
                self._loc_text.config(text="Location: not set", fg=FG_DIM)
                self._loc_dot.config(fg=FG_DIM)

    def _do_fetch_location(self):
        loc = fetch_location_ip()
        self.after(0, self._on_location_result, loc)

    def _on_location_result(self, loc):
        if loc:
            self._user_loc = loc
            city   = loc.get("city", "")
            region = loc.get("region", "")
            label  = f"{city}, {region}".strip(", ") if (city or region) else "Custom location"
            source = "address" if loc.get("source") == "address" else "IP"
            self._loc_text.config(text=f"  {label}", fg=GREEN)
            self._loc_dot.config(fg=GREEN)
            self.status_var.set(
                f"Location set ({source}): {label}  "
                f"({loc['lat']:.4f}, {loc['lon']:.4f})")
            df = self._build_dataframe()
            self._draw_static_map(df if not df.empty else None)
        else:
            self._user_loc = None
            self._loc_text.config(text="Detection failed", fg=RED)
            self._loc_dot.config(fg=RED)

    # ── NOTEBOOK ───────────────────────────────────────────────────────────────
    def _build_notebook(self):
        self.nb = ttk.Notebook(self)
        self.nb.pack(fill=tk.BOTH, expand=True, padx=18, pady=(0, 14))
        self._build_table_tab()
        self._build_stats_tab()
        self._build_map_tab()

    # ── TAB 1: TABLE ───────────────────────────────────────────────────────────
    def _build_table_tab(self):
        f = tk.Frame(self.nb, bg=BG)
        self.nb.add(f, text="  Results  ")
        cols   = ("Server", "Group", "Avg ms", "Min ms", "Max ms", "Loss %", "Status")
        widths = [220, 145, 80, 80, 80, 70, 125]
        self.tree = ttk.Treeview(f, columns=cols, show="headings", selectmode="browse")
        for col, w in zip(cols, widths):
            anch = "w" if col in ("Server","Group") else "center"
            self.tree.heading(col, text=col)
            self.tree.column(col, width=w, anchor=anch)
        sb = ttk.Scrollbar(f, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        for tag, col in [("good", GREEN),("ok", ACCENT),("slow", YELLOW),
                         ("bad", RED),("dead", FG_DIM)]:
            self.tree.tag_configure(tag, foreground=col)

    # ── TAB 2: STATS ───────────────────────────────────────────────────────────
    def _build_stats_tab(self):
        f = tk.Frame(self.nb, bg=BG)
        self.nb.add(f, text="  Statistics  ")
        self.stats_ph = tk.Label(f, text="Run a ping test to generate statistics.",
                                 font=("Segoe UI", 13), fg=FG_DIM, bg=BG)
        self.stats_ph.pack(expand=True)
        self._stats_frame = f

    def _draw_stats(self):
        df = self._build_dataframe()
        if df.empty:
            return
        if self._stats_canvas_widget:
            self._stats_canvas_widget.get_tk_widget().destroy()
        self.stats_ph.pack_forget()

        sns.set_theme(style="dark", rc={
            "axes.facecolor":   BG2,   "figure.facecolor": BG,
            "axes.edgecolor":   BG3,   "axes.labelcolor":  FG_DIM,
            "xtick.color":      FG_DIM,"ytick.color":      FG_DIM,
            "text.color":       FG,    "grid.color":       BG3,
            "grid.linestyle":   "--",  "grid.alpha":       0.5,
        })
        fig = plt.Figure(figsize=(15, 9), facecolor=BG)
        gs  = gridspec.GridSpec(2, 3, figure=fig, hspace=0.50, wspace=0.40,
                                left=0.06, right=0.97, top=0.93, bottom=0.08)

        # 1 — Sorted bar chart
        ax1 = fig.add_subplot(gs[0, :2])
        sdf = df.sort_values("avg").reset_index(drop=True)
        bar_cols = [GROUP_PALETTE[g] for g in sdf["Group"]]
        ax1.bar(range(len(sdf)), sdf["avg"], color=bar_cols, width=0.75, zorder=3)
        ax1.errorbar(range(len(sdf)), sdf["avg"],
                     yerr=[sdf["avg"]-sdf["min"], sdf["max"]-sdf["avg"]],
                     fmt="none", ecolor="#ffffff33", capsize=2, lw=0.8, zorder=4)
        ax1.set_xticks([])
        ax1.set_title("All Servers — Avg Latency (sorted, bars = min/max range)",
                      color=FG, fontsize=11, pad=8)
        ax1.set_ylabel("ms", color=FG_DIM)
        ax1.set_facecolor(BG2)
        handles = [mpatches.Patch(color=c, label=g) for g, c in GROUP_PALETTE.items()
                   if g in df["Group"].values]
        ax1.legend(handles=handles, fontsize=7, framealpha=0.15,
                   labelcolor=FG, facecolor=BG3, edgecolor=BG3, loc="upper left")

        # 2 — KDE
        ax2 = fig.add_subplot(gs[0, 2])
        for grp, gcol in GROUP_PALETTE.items():
            sub = df[df["Group"] == grp]["avg"]
            if len(sub) >= 2:
                sns.kdeplot(sub, ax=ax2, color=gcol,
                            fill=True, alpha=0.30, linewidth=1.6, label=grp)
            elif len(sub) == 1:
                ax2.axvline(sub.iloc[0], color=gcol, lw=1.6, label=grp)
        ax2.set_title("Latency Distribution (KDE)", color=FG, fontsize=11, pad=8)
        ax2.set_xlabel("ms", color=FG_DIM)
        ax2.set_ylabel("Density", color=FG_DIM)
        ax2.set_facecolor(BG2)

        # 3 — Box plot
        ax3 = fig.add_subplot(gs[1, 0])
        grp_order  = [g for g in GROUP_PALETTE if g in df["Group"].values]
        grp_colors = [GROUP_PALETTE[g] for g in grp_order]
        sns.boxplot(data=df, x="Group", y="avg", ax=ax3,
                    order=grp_order, palette=grp_colors, linewidth=1.2,
                    flierprops={"marker":"o","markersize":3,"markerfacecolor":FG_DIM})
        ax3.set_xticklabels([g.split(" ")[0] for g in grp_order], fontsize=8)
        ax3.set_title("Latency by Datacenter Group", color=FG, fontsize=11, pad=8)
        ax3.set_xlabel("", color=FG_DIM)
        ax3.set_ylabel("Avg ms", color=FG_DIM)
        ax3.set_facecolor(BG2)

        # 4 — Min vs Max scatter
        ax4 = fig.add_subplot(gs[1, 1])
        for grp, gcol in GROUP_PALETTE.items():
            sub = df[df["Group"] == grp]
            if not sub.empty:
                ax4.scatter(sub["min"], sub["max"], color=gcol,
                            s=60, alpha=0.85, zorder=3, label=grp)
        mn_, mx_ = df["min"].min(), df["max"].max()
        ax4.plot([mn_, mx_], [mn_, mx_], color="#ffffff22", lw=1, ls="--")
        ax4.set_title("Min vs Max Latency", color=FG, fontsize=11, pad=8)
        ax4.set_xlabel("Min ms", color=FG_DIM)
        ax4.set_ylabel("Max ms", color=FG_DIM)
        ax4.set_facecolor(BG2)

        # 5 — Packet loss heatmap
        ax5 = fig.add_subplot(gs[1, 2])
        hm_df = df[["short","loss"]].set_index("short")
        n      = len(hm_df)
        cols_n = 4
        rows_n = -(-n // cols_n)
        grid   = np.full((rows_n, cols_n), np.nan)
        annots = [[""] * cols_n for _ in range(rows_n)]
        for idx, (nm, row) in enumerate(hm_df.iterrows()):
            r, c = divmod(idx, cols_n)
            grid[r, c]   = row["loss"]
            annots[r][c] = nm.replace("us-lax-wg-", "")
        im = sns.heatmap(grid, ax=ax5, cmap="YlOrRd", vmin=0, vmax=100,
                         linewidths=0.5, linecolor=BG,
                         annot=annots, fmt="s",
                         annot_kws={"size":6,"color":FG},
                         cbar_kws={"label":"Loss %","shrink":0.8})
        ax5.set_title("Packet Loss Heatmap", color=FG, fontsize=11, pad=8)
        ax5.set_xticks([]); ax5.set_yticks([])
        ax5.set_facecolor(BG2)
        cbar = im.collections[0].colorbar
        cbar.ax.yaxis.label.set_color(FG_DIM)
        cbar.ax.tick_params(colors=FG_DIM)

        canvas = FigureCanvasTkAgg(fig, master=self._stats_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._stats_canvas_widget = canvas
        plt.close(fig)

    # ── TAB 3: MAP ─────────────────────────────────────────────────────────────
    def _build_map_tab(self):
        f = tk.Frame(self.nb, bg=BG)
        self.nb.add(f, text="  Map  ")

        info = tk.Frame(f, bg=BG2, pady=10, padx=16)
        info.pack(fill=tk.X)
        tk.Label(info, text="Mullvad LAX Datacenter Locations",
                 font=("Segoe UI", 12, "bold"), fg=FG, bg=BG2).pack(side=tk.LEFT)
        self.map_btn = tk.Button(
            info, text="  Open Interactive Map (browser)",
            font=("Segoe UI", 10, "bold"), fg=BG, bg=ACCENT,
            relief=tk.FLAT, padx=14, pady=5, cursor="hand2",
            command=self._open_map, state=tk.DISABLED)
        self.map_btn.pack(side=tk.RIGHT)

        # Datacenter legend cards
        dc_frame = tk.Frame(f, bg=BG, pady=8, padx=16)
        dc_frame.pack(fill=tk.X)
        for dc_name, dc in DATACENTER_INFO.items():
            card = tk.Frame(dc_frame, bg=BG2, padx=12, pady=8)
            card.pack(side=tk.LEFT, expand=True, fill=tk.BOTH, padx=(0, 8))
            tk.Label(card, text="*", fg=dc["color"], bg=BG2,
                     font=("Segoe UI", 18)).pack(anchor="w")
            tk.Label(card, text=dc_name, font=("Segoe UI", 9, "bold"),
                     fg=FG, bg=BG2).pack(anchor="w")
            tk.Label(card, text=dc["location"], font=("Courier New", 8),
                     fg=FG_DIM, bg=BG2, wraplength=170, justify="left").pack(anchor="w")
            sl = tk.Label(card, text=f"{len(dc['servers'])} servers",
                          font=MONO, fg=dc["color"], bg=BG2)
            sl.pack(anchor="w")
            self._dc_stat_labels[dc_name] = sl

        self._map_frame = tk.Frame(f, bg=BG)
        self._map_frame.pack(fill=tk.BOTH, expand=True, padx=16, pady=(0, 14))
        self._draw_static_map(None)

    # ── STATIC MAP ─────────────────────────────────────────────────────────────
    def _draw_static_map(self, df):
        if self._map_canvas_widget:
            self._map_canvas_widget.get_tk_widget().destroy()

        loc = self._user_loc

        # Determine map bounds — zoom out if user is far from LA
        if loc:
            lats = [loc["lat"]] + [dc["lat"] for dc in DATACENTER_INFO.values()]
            lons = [loc["lon"]] + [dc["lon"] for dc in DATACENTER_INFO.values()]
            lat_pad = max((max(lats) - min(lats)) * 0.25, 0.5)
            lon_pad = max((max(lons) - min(lons)) * 0.25, 0.5)
            xlim = (min(lons) - lon_pad, max(lons) + lon_pad)
            ylim = (min(lats) - lat_pad, max(lats) + lat_pad)
        else:
            xlim = (-119.1, -117.1)
            ylim = (33.35, 34.55)

        fig, ax = plt.subplots(figsize=(14, 6), facecolor=BG)
        ax.set_facecolor(BG2)
        title = "LA-Area Mullvad WireGuard Datacenters"
        if loc:
            title += f"  —  Your location: {loc['city']}, {loc.get('region','')}"
        ax.set_title(title, color=FG, fontsize=12, pad=10)
        ax.set_xlim(*xlim); ax.set_ylim(*ylim)
        ax.set_xlabel("Longitude", color=FG_DIM)
        ax.set_ylabel("Latitude",  color=FG_DIM)
        ax.tick_params(colors=FG_DIM)
        for spine in ax.spines.values():
            spine.set_edgecolor(BG3)
        ax.grid(True, color=BG3, linestyle="--", alpha=0.4)

        # City reference dots
        cities = {
            "Los Angeles":  (34.0522, -118.2437),
            "Santa Monica": (34.0195, -118.4912),
            "Burbank":      (34.1808, -118.3090),
            "Long Beach":   (33.7701, -118.1937),
            "Irvine":       (33.6846, -117.8265),
            "El Segundo":   (33.9165, -118.4150),
        }
        for city, (lat, lon) in cities.items():
            if xlim[0] < lon < xlim[1] and ylim[0] < lat < ylim[1]:
                ax.plot(lon, lat, "o", color="#ffffff18", markersize=4, zorder=2)
                ax.text(lon + 0.013, lat + 0.008, city,
                        color=FG_DIM, fontsize=6.5, alpha=0.45, zorder=2)

        # ── User location ──────────────────────────────────────────────────────
        if loc:
            ulat, ulon = loc["lat"], loc["lon"]

            # Lines from user to each datacenter
            for dc in DATACENTER_INFO.values():
                dist_km = haversine_km(ulat, ulon, dc["lat"], dc["lon"])
                ax.plot([ulon, dc["lon"]], [ulat, dc["lat"]],
                        color="#ffffff14", lw=1.0, ls="--", zorder=3)
                # Midpoint distance label
                mid_lon = (ulon + dc["lon"]) / 2
                mid_lat = (ulat + dc["lat"]) / 2
                ax.text(mid_lon, mid_lat, f"{dist_km:.0f} km",
                        color="#ffffff40", fontsize=6.5, ha="center",
                        va="center", zorder=4,
                        bbox=dict(boxstyle="round,pad=0.2", facecolor=BG,
                                  edgecolor="none", alpha=0.6))

            # Pulsing rings
            for r, a in [(0.06, 0.12), (0.04, 0.22), (0.02, 0.55)]:
                ax.add_patch(plt.Circle((ulon, ulat), r, color=ORANGE,
                                        fill=False, alpha=a, lw=1.2, zorder=8))

            # User dot
            ax.scatter(ulon, ulat, s=140, color=ORANGE, zorder=9,
                       edgecolors="#fff8", linewidths=1.5)
            ax.plot(ulon, ulat, "+", color="#fff", markersize=9,
                    markeredgewidth=1.5, zorder=10)

            loc_label = f"YOU\n{loc['city']}"
            if loc.get("region"):
                loc_label += f"\n{loc['region']}"
            ax.annotate(loc_label, (ulon, ulat),
                        xytext=(14, -22), textcoords="offset points",
                        color=FG, fontsize=8, fontweight="bold",
                        bbox=dict(boxstyle="round,pad=0.45", facecolor=BG3,
                                  edgecolor=ORANGE, alpha=0.92, lw=1.5),
                        zorder=11)

        # ── Datacenters ────────────────────────────────────────────────────────
        for dc_name, dc in DATACENTER_INFO.items():
            if df is not None and not df.empty:
                rows     = df[df["server"].isin(dc["servers"])]
                avg_ping = rows["avg"].mean() if not rows.empty else None
                reach    = len(rows)
            else:
                avg_ping = None
                reach    = len(dc["servers"])

            color  = dc["color"] if avg_ping is None else ping_hex(avg_ping)
            size   = 320 + reach * 120
            label  = f"{dc_name}\n{reach} servers"
            if avg_ping is not None:
                label += f"\n{avg_ping:.1f} ms avg"
            if loc:
                dist = haversine_km(loc["lat"], loc["lon"], dc["lat"], dc["lon"])
                label += f"\n{dist:.0f} km from you"

            ax.scatter(dc["lon"], dc["lat"], s=size, color=color,
                       alpha=0.70, zorder=5,
                       edgecolors="#ffffff44", linewidths=1.5)
            ax.plot(dc["lon"], dc["lat"], "+", color=color,
                    markersize=9, zorder=6, markeredgewidth=2)
            ax.annotate(label, (dc["lon"], dc["lat"]),
                        xytext=(14, 14), textcoords="offset points",
                        color=FG, fontsize=7.5,
                        bbox=dict(boxstyle="round,pad=0.4", facecolor=BG3,
                                  edgecolor=color, alpha=0.90), zorder=7)

        # Legend
        legend_items = [
            mpatches.Patch(color=dc["color"], label=name)
            for name, dc in DATACENTER_INFO.items()
        ]
        if loc:
            legend_items.append(
                mpatches.Patch(color=ORANGE, label=f"Your location ({loc['city']})")
            )
        ax.legend(handles=legend_items, fontsize=7, framealpha=0.2,
                  labelcolor=FG, facecolor=BG3, edgecolor=BG3,
                  loc="lower right")

        canvas = FigureCanvasTkAgg(fig, master=self._map_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._map_canvas_widget = canvas
        plt.close(fig)

    # ── INTERACTIVE FOLIUM MAP ─────────────────────────────────────────────────
    def _open_map(self):
        df  = self._build_dataframe()
        loc = self._user_loc

        # Auto-centre: if user loc exists, fit both; otherwise default LA
        if loc:
            center = [(loc["lat"] + 33.95) / 2, (loc["lon"] + (-118.25)) / 2]
            zoom   = 8 if abs(loc["lat"] - 33.95) < 2 else 5
        else:
            center = [33.95, -118.25]
            zoom   = 10

        m = folium.Map(location=center, zoom_start=zoom,
                       tiles="CartoDB dark_matter")

        # ── User location marker ───────────────────────────────────────────────
        if loc:
            src_note = ("IP-based — approximate" if loc.get("source") == "ip"
                        else "Address geocoded via OpenStreetMap")
            user_popup = (
                f"<b style='color:{ORANGE}'>Your Location</b><br>"
                f"{loc.get('city','')}, {loc.get('region','')}, {loc.get('country','')}<br>"
                f"Coords: {loc['lat']:.5f}, {loc['lon']:.5f}<br>"
                f"<i style='color:#8b949e;font-size:10px'>{src_note}</i>"
            )
            # Pulsing orange circle
            folium.Circle(
                location=[loc["lat"], loc["lon"]],
                radius=8000, color=ORANGE, fill=True,
                fill_color=ORANGE, fill_opacity=0.12,
                popup=folium.Popup(user_popup, max_width=250),
                tooltip="Your location (IP-based)",
            ).add_to(m)
            folium.Circle(
                location=[loc["lat"], loc["lon"]],
                radius=3500, color=ORANGE, fill=True,
                fill_color=ORANGE, fill_opacity=0.25,
            ).add_to(m)
            folium.Marker(
                location=[loc["lat"], loc["lon"]],
                popup=folium.Popup(user_popup, max_width=250),
                tooltip=f"You — {loc['city']}",
                icon=folium.DivIcon(html=(
                    f"<div style='background:{ORANGE};color:#000;font-weight:bold;"
                    f"font-size:11px;padding:4px 9px;border-radius:50%;opacity:0.95;"
                    f"border:2px solid #fff;text-align:center;line-height:1.2'>YOU</div>"))
            ).add_to(m)

            # Lines from user to each datacenter
            for dc_name, dc in DATACENTER_INFO.items():
                dist = haversine_km(loc["lat"], loc["lon"], dc["lat"], dc["lon"])
                dc_rows  = df[df["server"].isin(dc["servers"])] if not df.empty else pd.DataFrame()
                avg_ping = dc_rows["avg"].mean() if not dc_rows.empty else None
                line_col = ping_folium_color(avg_ping)
                folium.PolyLine(
                    locations=[[loc["lat"], loc["lon"]], [dc["lat"], dc["lon"]]],
                    color=line_col, weight=1.5, opacity=0.45,
                    tooltip=f"{dc_name}: {dist:.0f} km away"
                            + (f", {avg_ping:.1f} ms avg" if avg_ping else ""),
                    dash_array="6 4",
                ).add_to(m)

        # ── Datacenter circles + markers ───────────────────────────────────────
        np.random.seed(42)
        for dc_name, dc in DATACENTER_INFO.items():
            dc_servers = dc["servers"]
            if not df.empty:
                rows     = df[df["server"].isin(dc_servers)]
                avg_ping = rows["avg"].mean() if not rows.empty else None
                reach    = len(rows)
            else:
                avg_ping = None
                reach    = len(dc_servers)

            col = ping_folium_color(avg_ping)
            rad = 800 + reach * 280
            dist_str = ""
            if loc:
                dist = haversine_km(loc["lat"], loc["lon"], dc["lat"], dc["lon"])
                dist_str = f"<br>Distance from you: <b>{dist:.0f} km</b>"

            tip = (f"<b style='color:{dc['color']}'>{dc_name}</b><br>"
                   f"{dc['location']}<br>"
                   f"Servers: {reach}/{len(dc_servers)}<br>"
                   + (f"Avg: <b>{avg_ping:.1f} ms</b>" if avg_ping else "No data yet")
                   + dist_str)

            folium.Circle(location=[dc["lat"], dc["lon"]],
                          radius=rad, color=dc["color"], fill=True,
                          fill_color=dc["color"], fill_opacity=0.30,
                          popup=folium.Popup(tip, max_width=250),
                          tooltip=dc_name).add_to(m)
            folium.Marker(
                location=[dc["lat"], dc["lon"]],
                popup=folium.Popup(tip, max_width=250),
                tooltip=dc_name,
                icon=folium.DivIcon(html=(
                    f"<div style='background:{dc['color']};color:#000;"
                    f"font-weight:bold;font-size:10px;"
                    f"padding:3px 7px;border-radius:4px;opacity:0.92;"
                    f"white-space:nowrap'>"
                    f"{dc_name.split(' ')[0]}"
                    f"{f' | {avg_ping:.0f}ms' if avg_ping else ''}</div>"))
            ).add_to(m)

            # Individual server dots (jittered around datacenter)
            for s in dc_servers:
                jlat = dc["lat"] + np.random.uniform(-0.013, 0.013)
                jlon = dc["lon"] + np.random.uniform(-0.016, 0.016)
                row  = df[df["server"] == s] if not df.empty else pd.DataFrame()
                avg  = row["avg"].values[0] if not row.empty else None
                scol = ping_folium_color(avg)
                short = s.replace(".relays.mullvad.net","").replace("us-lax-","")
                stip  = f"{short}: {avg:.1f} ms" if avg else f"{short}: no data"
                folium.CircleMarker(location=[jlat, jlon], radius=5,
                                    color=scol, fill=True, fill_color=scol,
                                    fill_opacity=0.85, tooltip=stip).add_to(m)

        tmp = tempfile.NamedTemporaryFile(suffix=".html", delete=False, mode="w")
        self._map_tmp = tmp.name
        tmp.close()
        m.save(self._map_tmp)
        webbrowser.open(f"file://{self._map_tmp}")

    # ── DATA ───────────────────────────────────────────────────────────────────
    def _build_dataframe(self):
        rows = []
        for s, d in self.results.items():
            if d and d[3] < 100:
                rows.append({
                    "server": s,
                    "short":  s.replace(".relays.mullvad.net",""),
                    "Group":  server_group(s),
                    "avg": d[0], "min": d[1], "max": d[2], "loss": d[3],
                })
        return pd.DataFrame(rows)

    # ── PING LOOP ──────────────────────────────────────────────────────────────
    def start_pinging(self):
        if self.running: return
        self.running = True
        self.btn.config(state=tk.DISABLED, text="  Running...")
        self.results.clear()
        self.progress["value"] = 0
        for row in self.tree.get_children():
            self.tree.delete(row)
        for v, sub in self.cards.values():
            v.config(text="--", fg=ACCENT); sub.config(text="")
        threading.Thread(target=self._ping_all, daemon=True).start()

    def _ping_all(self):
        for i, server in enumerate(SERVERS, 1):
            self.after(0, self.status_var.set,
                       f"Pinging {server}  ({i}/{len(SERVERS)})")
            data = ping_server(server)
            self.results[server] = data
            self.after(0, self._add_row, server, data)
            self.after(0, lambda v=i: self.progress.config(value=v))
        self.after(0, self._finish)

    def _add_row(self, server, data):
        short = server.replace(".relays.mullvad.net","")
        grp   = server_group(server)
        if data is None:
            tag = "dead"
            row = (short, grp, "--", "--", "--", "100%", "x  UNREACHABLE")
        else:
            avg, mn, mx, loss = data
            status_map = {"good":"  EXCELLENT","ok":"  GOOD",
                          "slow":"  SLOW","bad":"  HIGH LAT"}
            tag    = ms_tag(avg)
            status = status_map.get(tag, "x  UNREACHABLE")
            row    = (short, grp,
                      f"{avg:.1f}", f"{mn:.1f}", f"{mx:.1f}",
                      f"{loss}%", status)
        self.tree.insert("", tk.END, values=row, tags=(tag,))

    def _finish(self):
        self.running = False
        self.status_var.set(f"Done — {len(SERVERS)} servers tested.")
        self.btn.config(state=tk.NORMAL, text="  Run Again")

        reach = {s: d for s, d in self.results.items() if d and d[3] < 100}
        if reach:
            best_s  = min(reach, key=lambda s: reach[s][0])
            worst_s = max(reach, key=lambda s: reach[s][0])
            overall = sum(d[0] for d in reach.values()) / len(reach)
            def sh(s): return s.replace(".relays.mullvad.net","").replace("us-lax-","")

            bv, bs = self.cards["Best Server"]
            bv.config(text=sh(best_s), fg=GREEN)
            bs.config(text=f"{reach[best_s][0]:.1f} ms avg")

            wv, ws = self.cards["Worst Server"]
            wv.config(text=sh(worst_s), fg=RED)
            ws.config(text=f"{reach[worst_s][0]:.1f} ms avg")

            av, as_ = self.cards["Avg Latency"]
            av.config(text=f"{overall:.1f} ms", fg=ping_hex(overall))
            as_.config(text=f"across {len(reach)} servers")

            rv, rs = self.cards["Reachable"]
            rv.config(text=f"{len(reach)} / {len(SERVERS)}", fg=ACCENT)
            rs.config(text=f"{len(SERVERS)-len(reach)} unreachable")

            df = self._build_dataframe()
            for dc_name, dc in DATACENTER_INFO.items():
                lbl = self._dc_stat_labels.get(dc_name)
                if lbl:
                    rows = df[df["server"].isin(dc["servers"])]
                    text = f"{len(rows)} servers | {rows['avg'].mean():.1f} ms avg" \
                           if not rows.empty else "0 servers reachable"
                    lbl.config(text=text)
        else:
            rv, rs = self.cards["Reachable"]
            rv.config(text=f"0 / {len(SERVERS)}", fg=RED)
            rs.config(text="all unreachable")

        self._draw_stats()
        df = self._build_dataframe()
        self._draw_static_map(df if not df.empty else None)
        self.map_btn.config(state=tk.NORMAL)


if __name__ == "__main__":
    app = MullvadApp()
    app.mainloop()
