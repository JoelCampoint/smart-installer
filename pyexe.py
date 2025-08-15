#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# --- Silence early SyntaxWarning from peutils (must be the very first lines) ---
import warnings as _w
_w.filterwarnings("ignore", category=SyntaxWarning, module=r"^peutils$")
# fallback, falls die Modul-Filterung mal nicht greift:
_w.filterwarnings("ignore", message=r"invalid escape sequence .*", category=SyntaxWarning)
try:
    import peutils  # pre-import under active filter so later imports are no-ops
except Exception:
    pass
# --- end ---

import os
import sys
import re
import ast
import json
import shlex
import queue
import shutil
import threading
import subprocess
import sysconfig
from pathlib import Path
from datetime import datetime
from typing import Optional

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter.scrolledtext import ScrolledText

try:
    from importlib import metadata as importlib_metadata  # Py>=3.8
except Exception:  # pragma: no cover
    import importlib_metadata  # type: ignore

import importlib.util


APP_TITLE = "Smart PyInstaller Builder"
PROFILE_SUFFIX = ".buildprofile.json"
AUTO_DATA_DIRS = ["assets", "data", "resources", "templates", "static", "config", "images", "locale"]
FILE_EXT_PATTERN = re.compile(
    r"""(?P<path>[A-Za-z0-9_\-./\\:]+?\.(?:csv|tsv|xlsx|xls|json|yaml|yml|ini|txt|png|jpg|jpeg|gif|svg|ico|
    qml|ui|html|css|toml|md|db|sqlite|ttf|otf|xml|jinja2|jinja|mo|po))""",
    re.IGNORECASE | re.VERBOSE,
)
HEAVY_LIBS = {"matplotlib", "sklearn", "cv2", "PIL", "Pillow", "nltk", "spacy", "torch", "transformers",
              "openpyxl", "pydantic", "jinja2", "yaml", "cryptography", "numba", "scipy"}


def data_sep() -> str:
    return ";" if os.name == "nt" else ":"


def quote_path(p: Path) -> str:
    return str(p)


def get_stdlib_modules() -> set:
    std = set()
    if hasattr(sys, "stdlib_module_names"):  # Py>=3.10
        std.update(sys.stdlib_module_names)
    else:
        std_paths = {Path(sysconfig.get_paths()["stdlib"]).resolve()}
        for p in std_paths:
            if p.exists():
                for item in p.glob("**/*.py"):
                    try:
                        name = item.relative_to(p).with_suffix("").as_posix().replace("/", ".")
                        std.add(name.split(".")[0])
                    except Exception:
                        pass
    # Builtins
    try:
        import builtins  # noqa
        std.update(sys.builtin_module_names)
    except Exception:
        pass
    return std


def top_level_module(name: str) -> str:
    return name.split(".")[0] if name else name


def packages_distributions_map() -> dict:
    try:
        return importlib_metadata.packages_distributions()
    except Exception:
        return {}


def is_third_party(mod: str, stdlib: set, pkg_map: dict) -> bool:
    m = top_level_module(mod)
    if not m or m in stdlib:
        return False
    if m in pkg_map:
        return True
    try:
        spec = importlib.util.find_spec(m)
        if spec is None or spec.origin in (None, "built-in"):
            return False
        stdlib_path = Path(sysconfig.get_paths()["stdlib"]).resolve()
        origin = Path(spec.origin).resolve()
        return stdlib_path not in origin.parents and origin != stdlib_path
    except Exception:
        return True


# ---- FIX: sichere Extraktion von String-Literalen aus AST-Knoten (ohne ast.Str/.s) ----
def _extract_str_constant(node: ast.AST) -> Optional[str]:
    """
    Liefert den String-Wert aus einem AST-Knoten, falls dieser eine String-Konstante ist.
    Auf modernen Pythons (>=3.8) ausschließlich über ast.Constant.
    Fallback auf ast.Str nur, falls ast.Constant nicht existiert (sehr alte Versionen).
    """
    Constant = getattr(ast, "Constant", None)
    if Constant is not None and isinstance(node, Constant):
        val = getattr(node, "value", None)
        return val if isinstance(val, str) else None

    # Fallback nur für sehr alte Pythons; auf modernen führt dies nicht zu DeprecationWarnings
    if Constant is None:
        Str = getattr(ast, "Str", None)
        if Str is not None and isinstance(node, Str):
            return getattr(node, "s", None)

    return None


def parse_imports_from_file(py_file: Path) -> tuple[set, set]:
    imports = set()
    dynamic = set()
    try:
        src = py_file.read_text(encoding="utf-8", errors="ignore")
        tree = ast.parse(src, filename=str(py_file))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name:
                        imports.add(top_level_module(alias.name))
            elif isinstance(node, ast.ImportFrom):
                if node.module:
                    imports.add(top_level_module(node.module))
            elif isinstance(node, ast.Call):
                # importlib.import_module("x.y")  oder  __import__("x.y")
                try:
                    func_name = ""
                    if isinstance(node.func, ast.Attribute):
                        func_name = node.func.attr
                    elif isinstance(node.func, ast.Name):
                        func_name = node.func.id

                    if func_name in {"import_module", "__import__"}:
                        mod = None
                        # Positional arg
                        if node.args:
                            mod = _extract_str_constant(node.args[0])
                        # Keyword-arg (name=/module=)
                        if mod is None:
                            for kw in (node.keywords or []):
                                if kw.arg in {"name", "module"}:
                                    mod = _extract_str_constant(kw.value)
                                    if mod:
                                        break
                        if mod:
                            dynamic.add(top_level_module(mod))
                except Exception:
                    pass
    except Exception:
        pass
    return imports, dynamic


def find_literal_files(py_file: Path, project_root: Path) -> set[Path]:
    found = set()
    try:
        src = py_file.read_text(encoding="utf-8", errors="ignore")
        for m in FILE_EXT_PATTERN.finditer(src):
            raw = m.group("path")
            if not raw:
                continue
            # normalize
            candidate = Path(raw.replace("\\\\", "\\"))
            # relative to script file
            if not candidate.is_absolute():
                candidate = (py_file.parent / candidate).resolve()
            if candidate.exists() and candidate.is_file():
                try:
                    # include only files within project root if possible; otherwise include by basename
                    if str(candidate).startswith(str(project_root)):
                        found.add(candidate)
                    else:
                        found.add(candidate)
                except Exception:
                    found.add(candidate)
    except Exception:
        pass
    return found


def scan_project(script_path: Path, scan_all_py: bool) -> dict:
    project_root = script_path.parent.resolve()
    files = [script_path]
    if scan_all_py:
        for p in project_root.rglob("*.py"):
            if p.is_file():
                files.append(p.resolve())
    imports = set()
    dynamic = set()
    literal_files = set()
    for f in set(files):
        imps, dyn = parse_imports_from_file(f)
        imports |= imps
        dynamic |= dyn
        literal_files |= find_literal_files(f, project_root)
    return {
        "project_root": project_root,
        "imports": imports,
        "dynamic_imports": dynamic,
        "literal_files": literal_files,
    }


def auto_data_dirs(project_root: Path) -> list[tuple[Path, str]]:
    datas = []
    for name in AUTO_DATA_DIRS:
        d = (project_root / name)
        if d.exists() and d.is_dir():
            datas.append((d, name))
    return datas


def map_add_data_entries(paths: list[Path], project_root: Path) -> list[tuple[Path, str]]:
    mapped = []
    for p in paths:
        p = p.resolve()
        try:
            rel = p.relative_to(project_root)
            dest = str(rel.parent) if p.is_file() else str(rel)
            if dest == ".":
                dest = "."
        except Exception:
            dest = p.name if p.is_file() else p.name
        mapped.append((p, dest))
    return mapped


def suggest_collect_all(imports: set) -> list[str]:
    s = set()
    for m in imports:
        root = top_level_module(m)
        if root in HEAVY_LIBS:
            s.add(root if root != "PIL" else "Pillow")
    return sorted(s)


def ensure_pyinstaller_available(log_cb) -> tuple[bool, str]:
    exe = shutil.which("pyinstaller") or shutil.which("pyi-makespec")
    if exe:
        try:
            out = subprocess.check_output([exe, "--version"], stderr=subprocess.STDOUT, text=True, encoding="utf-8")
            return True, out.strip()
        except Exception:
            return True, ""
    # try module
    try:
        out = subprocess.check_output([sys.executable, "-m", "PyInstaller", "--version"], stderr=subprocess.STDOUT, text=True, encoding="utf-8")
        return True, out.strip()
    except Exception:
        log_cb("PyInstaller nicht gefunden.")
        return False, ""


def _with_peutils_syntaxwarning_filter_env(env: Optional[dict] = None) -> dict:
    """
    Ergänzt die Umgebungsvariable PYTHONWARNINGS um eine gezielte
    Unterdrückung der bekannten SyntaxWarning aus dem Modul 'peutils'.
    Wirkt in Subprozessen (pip/PyInstaller).
    """
    if env is None:
        env = os.environ.copy()
    rule = "ignore::SyntaxWarning:peutils"
    existing = env.get("PYTHONWARNINGS", "")
    if existing:
        parts = [p.strip() for p in existing.split(",") if p.strip()]
        if rule not in parts:
            env["PYTHONWARNINGS"] = existing + "," + rule
    else:
        env["PYTHONWARNINGS"] = rule
    return env


def install_pyinstaller(log_cb) -> bool:
    try:
        log_cb("Installiere/aktualisiere PyInstaller …")
        cmd = [sys.executable, "-m", "pip", "install", "--upgrade", "pyinstaller"]
        p = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            env=_with_peutils_syntaxwarning_filter_env(),
        )
        for line in p.stdout:  # type: ignore
            log_cb(line.rstrip())
        rc = p.wait()
        if rc == 0:
            log_cb("PyInstaller installiert.")
            return True
        log_cb(f"pip Rückgabecode {rc}.")
        return False
    except Exception as e:
        log_cb(f"pip-Fehler: {e}")
        return False


def build_command(
    script_path: Path,
    name: str | None,
    onefile: bool,
    windowed: bool,
    clean: bool,
    icon_path: Path | None,
    add_datas: list[tuple[Path, str]],
    hidden_imports: list[str],
    collect_all_pkgs: list[str],
    extra_paths: list[Path] | None,
    noconfirm: bool = True,
    version_file: Path | None = None,    # NEW
    noupx: bool = False,                 # NEW
    runtime_tmpdir: Optional[str] = None # NEW
) -> list[str]:
    cmd = [sys.executable, "-m", "PyInstaller"]
    if clean:
        cmd.append("--clean")
    if noconfirm:
        cmd.append("--noconfirm")
    cmd.append("--onefile" if onefile else "--onedir")
    if windowed:
        cmd.append("--windowed")
    if name:
        cmd += ["--name", name]
    if icon_path and icon_path.exists():
        cmd += ["--icon", quote_path(icon_path)]
    for p, dest in add_datas:
        cmd += ["--add-data", f"{quote_path(p)}{data_sep()}{dest}"]
    for hi in hidden_imports:
        cmd += ["--hidden-import", hi]
    for pkg in collect_all_pkgs:
        cmd += ["--collect-all", pkg]
    if extra_paths:
        for ep in extra_paths:
            cmd += ["--paths", quote_path(ep)]
    if noupx:
        cmd.append("--noupx")  # Do not use UPX even if available
    if runtime_tmpdir:
        cmd += ["--runtime-tmpdir", runtime_tmpdir]
    if version_file and version_file.exists():
        cmd += ["--version-file", quote_path(version_file)]
    cmd.append(quote_path(script_path))
    return cmd


def open_folder(path: Path):
    try:
        if os.name == "nt":
            os.startfile(str(path))  # noqa
        elif sys.platform == "darwin":
            subprocess.Popen(["open", str(path)])
        else:
            subprocess.Popen(["xdg-open", str(path)])
    except Exception:
        pass


class BuilderGUI:
    def __init__(self, root: tk.Tk):
        self.root = root
        root.title(APP_TITLE)
        root.geometry("1080x820")

        self.log_queue = queue.Queue()
        self.build_thread = None

        self.script_var = tk.StringVar()
        self.icon_var = tk.StringVar()
        self.name_var = tk.StringVar()
        self.onefile_var = tk.BooleanVar(value=True)
        self.windowed_var = tk.BooleanVar(value=False)
        self.clean_var = tk.BooleanVar(value=True)
        self.scan_all_var = tk.BooleanVar(value=True)
        self.auto_data_dirs_var = tk.BooleanVar(value=True)
        self.collect_all_var = tk.BooleanVar(value=True)

        # NEW: zusätzliche Optionen/Metadaten
        self.noupx_var = tk.BooleanVar(value=True)
        self.runtime_tmpdir_var = tk.StringVar()
        self.use_versioninfo_var = tk.BooleanVar(value=True)

        self.publisher_var = tk.StringVar()
        self.product_var = tk.StringVar()
        self.version_var = tk.StringVar(value="1.0.0")
        self.desc_var = tk.StringVar()
        self.copyright_var = tk.StringVar()

        self.extra_paths: list[Path] = []
        self.manual_datas: list[tuple[Path, str]] = []
        self.manual_hidden: list[str] = []

        self.detected_imports: set[str] = set()
        self.detected_dynamic: set[str] = set()
        self.detected_literal_files: set[Path] = set()
        self.detected_collect_all: list[str] = []

        self._build_ui()
        self.root.after(100, self._poll_log)

        ok, ver = ensure_pyinstaller_available(self._log)
        self._set_status(ok, ver)

        self._log(f"Python: {sys.version.split()[0]}  @ {sys.executable}")
        self._log(f"Arbeitsverzeichnis: {Path.cwd()}")

    def _build_ui(self):
        pad = {"padx": 8, "pady": 6}

        top = ttk.Frame(self.root)
        top.pack(fill="x", **pad)

        ttk.Label(top, text="Python-Script:").grid(row=0, column=0, sticky="w")
        self.script_entry = ttk.Entry(top, textvariable=self.script_var)
        self.script_entry.grid(row=0, column=1, sticky="ew")
        ttk.Button(top, text="Auswählen…", command=self._choose_script).grid(row=0, column=2, sticky="w")

        ttk.Label(top, text="Name:").grid(row=1, column=0, sticky="w")
        self.name_entry = ttk.Entry(top, textvariable=self.name_var)
        self.name_entry.grid(row=1, column=1, sticky="ew")

        ttk.Label(top, text="Icon (.ico optional):").grid(row=2, column=0, sticky="w")
        self.icon_entry = ttk.Entry(top, textvariable=self.icon_var)
        self.icon_entry.grid(row=2, column=1, sticky="ew")
        ttk.Button(top, text="Icon wählen…", command=self._choose_icon).grid(row=2, column=2, sticky="w")

        top.columnconfigure(1, weight=1)

        opts = ttk.LabelFrame(self.root, text="Optionen")
        opts.pack(fill="x", **pad)
        ttk.Checkbutton(opts, text="One-File (EXE)", variable=self.onefile_var).grid(row=0, column=0, sticky="w")
        ttk.Checkbutton(opts, text="GUI-App (ohne Konsole)", variable=self.windowed_var).grid(row=0, column=1, sticky="w")
        ttk.Checkbutton(opts, text="Clean Build", variable=self.clean_var).grid(row=0, column=2, sticky="w")
        ttk.Checkbutton(opts, text="Gesamtes Projekt scannen", variable=self.scan_all_var).grid(row=1, column=0, sticky="w")
        ttk.Checkbutton(opts, text="Standard-Datenordner einbinden", variable=self.auto_data_dirs_var).grid(row=1, column=1, sticky="w")
        ttk.Checkbutton(opts, text="Sammele Daten zu großen Paketen (--collect-all)", variable=self.collect_all_var).grid(row=1, column=2, sticky="w")

        # NEW: zusätzliche Optionen in opts
        ttk.Checkbutton(opts, text="UPX deaktivieren (--noupx)", variable=self.noupx_var).grid(row=2, column=0, sticky="w")
        ttk.Label(opts, text="Runtime-Tmpdir (--runtime-tmpdir):").grid(row=2, column=1, sticky="e")
        rtmp = ttk.Entry(opts, textvariable=self.runtime_tmpdir_var, width=36)
        rtmp.grid(row=2, column=2, sticky="ew")

        lists = ttk.Frame(self.root)
        lists.pack(fill="both", expand=True, **pad)

        left = ttk.Frame(lists)
        left.pack(side="left", fill="both", expand=True)
        mid = ttk.Frame(lists)
        mid.pack(side="left", fill="both", expand=True)
        right = ttk.Frame(lists)
        right.pack(side="left", fill="both", expand=True)

        # Detected imports
        ttk.Label(left, text="Erkannte Drittanbieter-Module/Hidden-Imports").pack(anchor="w")
        self.imports_list = tk.Listbox(left, selectmode="extended")
        self.imports_list.pack(fill="both", expand=True)
        imp_btns = ttk.Frame(left)
        imp_btns.pack(fill="x")
        ttk.Button(imp_btns, text="Aus Liste entfernen", command=self._remove_selected_imports).pack(side="left")

        # Data files
        ttk.Label(mid, text="Einzuschließende Daten (Dateien/Ordner)").pack(anchor="w")
        self.datas_list = tk.Listbox(mid, selectmode="extended")
        self.datas_list.pack(fill="both", expand=True)
        data_btns = ttk.Frame(mid)
        data_btns.pack(fill="x")
        ttk.Button(data_btns, text="Datei hinzufügen…", command=self._add_file_data).pack(side="left")
        ttk.Button(data_btns, text="Ordner hinzufügen…", command=self._add_dir_data).pack(side="left")
        ttk.Button(data_btns, text="Aus Liste entfernen", command=self._remove_selected_datas).pack(side="left")

        # Extra paths + collect-all
        ttk.Label(right, text="Zusätzliche Pfade / Collect-All-Vorschläge").pack(anchor="w")
        self.paths_list = tk.Listbox(right, selectmode="extended")
        self.paths_list.pack(fill="both", expand=True)
        paths_btns = ttk.Frame(right)
        paths_btns.pack(fill="x")
        ttk.Button(paths_btns, text="Pfad hinzufügen…", command=self._add_extra_path).pack(side="left")
        ttk.Button(paths_btns, text="Aus Liste entfernen", command=self._remove_selected_paths).pack(side="left")

        # NEW: Metadaten-Box
        meta = ttk.LabelFrame(self.root, text="Metadaten (Windows-Versioninfos)")
        meta.pack(fill="x", **pad)
        ttk.Checkbutton(meta, text="Versioninfos einbetten (--version-file)", variable=self.use_versioninfo_var).grid(row=0, column=0, sticky="w")
        ttk.Label(meta, text="Publisher/Firma:").grid(row=1, column=0, sticky="e")
        ttk.Entry(meta, textvariable=self.publisher_var).grid(row=1, column=1, sticky="ew")
        ttk.Label(meta, text="Produktname:").grid(row=2, column=0, sticky="e")
        ttk.Entry(meta, textvariable=self.product_var).grid(row=2, column=1, sticky="ew")
        ttk.Label(meta, text="Version:").grid(row=3, column=0, sticky="e")
        ttk.Entry(meta, textvariable=self.version_var, width=16).grid(row=3, column=1, sticky="w")
        ttk.Label(meta, text="Beschreibung:").grid(row=4, column=0, sticky="e")
        ttk.Entry(meta, textvariable=self.desc_var).grid(row=4, column=1, sticky="ew")
        ttk.Label(meta, text="Copyright:").grid(row=5, column=0, sticky="e")
        ttk.Entry(meta, textvariable=self.copyright_var).grid(row=5, column=1, sticky="ew")
        meta.columnconfigure(1, weight=1)

        act = ttk.Frame(self.root)
        act.pack(fill="x", **pad)
        ttk.Button(act, text="Analysieren", command=self._analyze).pack(side="left")
        ttk.Button(act, text="PyInstaller installieren/aktualisieren", command=self._install_pyinstaller).pack(side="left")
        ttk.Button(act, text="Build starten", command=self._build).pack(side="left")
        ttk.Button(act, text="Dist öffnen", command=self._open_dist).pack(side="left")
        ttk.Button(act, text="Profil speichern", command=self._save_profile).pack(side="right")
        ttk.Button(act, text="Profil laden", command=self._load_profile).pack(side="right")

        self.status_var = tk.StringVar(value="Status: unbekannt")
        ttk.Label(self.root, textvariable=self.status_var).pack(anchor="w", **pad)

        self.log = ScrolledText(self.root, height=16)
        self.log.pack(fill="both", expand=False, **pad)
        self.log.configure(state="disabled")

    def _set_status(self, ok: bool, ver: str):
        if ok:
            self.status_var.set(f"PyInstaller gefunden (Version: {ver})")
        else:
            self.status_var.set("PyInstaller nicht gefunden – bitte installieren.")

    def _choose_script(self):
        fn = filedialog.askopenfilename(title="Python-Datei wählen", filetypes=[("Python", "*.py")])
        if fn:
            self.script_var.set(fn)
            if not self.name_var.get():
                self.name_var.set(Path(fn).stem)

    def _choose_icon(self):
        fn = filedialog.askopenfilename(title="Icon wählen (.ico)", filetypes=[("Icon", "*.ico"), ("Alle", "*.*")])
        if fn:
            self.icon_var.set(fn)

    def _add_file_data(self):
        fns = filedialog.askopenfilenames(title="Dateien hinzufügen")
        for fn in fns:
            p = Path(fn).resolve()
            if p.exists() and p.is_file():
                self.manual_datas.append((p, "."))
        self._refresh_datas_list()

    def _add_dir_data(self):
        d = filedialog.askdirectory(title="Ordner hinzufügen")
        if d:
            p = Path(d).resolve()
            if p.exists() and p.is_dir():
                self.manual_datas.append((p, p.name))
        self._refresh_datas_list()

    def _remove_selected_datas(self):
        sel = list(self.datas_list.curselection())[::-1]
        for i in sel:
            item = self.datas_list.get(i)
            # find tuple to remove
            for t in list(self.manual_datas):
                if item.startswith(str(t[0])):
                    self.manual_datas.remove(t)
                    break
        self._refresh_datas_list()

    def _add_extra_path(self):
        d = filedialog.askdirectory(title="Zusätzlichen Pfad hinzufügen (wird zu --paths)")
        if d:
            p = Path(d).resolve()
            if p not in self.extra_paths:
                self.extra_paths.append(p)
        self._refresh_paths_list()

    def _remove_selected_paths(self):
        sel = list(self.paths_list.curselection())[::-1]
        for i in sel:
            val = self.paths_list.get(i)
            try:
                self.extra_paths.remove(Path(val))
            except Exception:
                pass
        self._refresh_paths_list()

    def _remove_selected_imports(self):
        sel = list(self.imports_list.curselection())[::-1]
        items = [self.imports_list.get(i) for i in sel]
        for it in items:
            try:
                self.detected_imports.remove(it)
            except KeyError:
                pass
        self._refresh_imports_list()

    def _refresh_imports_list(self):
        self.imports_list.delete(0, tk.END)
        for m in sorted(self.detected_imports | self.detected_dynamic | set(self.manual_hidden)):
            self.imports_list.insert(tk.END, m)

    def _refresh_datas_list(self):
        self.datas_list.delete(0, tk.END)
        for p, dest in self.manual_datas:
            self.datas_list.insert(tk.END, f"{p}  ->  {dest}")
        # also show auto-detected literal files (read-only visual)
        for f in sorted(self.detected_literal_files):
            self.datas_list.insert(tk.END, f"{f}  (auto)")

        if self.auto_data_dirs_var.get() and self.script_var.get():
            project_root = Path(self.script_var.get()).parent.resolve()
            for p, dest in auto_data_dirs(project_root):
                self.datas_list.insert(tk.END, f"{p}  ->  {dest}  (auto-dir)")

    def _refresh_paths_list(self):
        self.paths_list.delete(0, tk.END)
        for p in self.extra_paths:
            self.paths_list.insert(tk.END, str(p))
        if self.collect_all_var.get():
            if self.detected_collect_all:
                self.paths_list.insert(tk.END, "--- Collect-All-Vorschläge ---")
                for pkg in self.detected_collect_all:
                    self.paths_list.insert(tk.END, f"--collect-all {pkg}")

    def _log(self, text: str):
        self.log_queue.put(text)

    def _poll_log(self):
        try:
            while True:
                line = self.log_queue.get_nowait()
                self.log.configure(state="normal")
                self.log.insert(tk.END, line + "\n")
                self.log.see(tk.END)
                self.log.configure(state="disabled")
        except queue.Empty:
            pass
        self.root.after(80, self._poll_log)

    def _install_pyinstaller(self):
        threading.Thread(target=self._install_pyinstaller_bg, daemon=True).start()

    def _install_pyinstaller_bg(self):
        ok = install_pyinstaller(self._log)
        ok2, ver = ensure_pyinstaller_available(self._log)
        self._set_status(ok and ok2, ver)

    def _analyze(self):
        script = Path(self.script_var.get().strip()) if self.script_var.get().strip() else None
        if not script or not script.exists():
            messagebox.showerror(APP_TITLE, "Bitte zuerst eine Python-Datei wählen.")
            return
        self._log("Analysiere Projekt …")
        res = scan_project(script, self.scan_all_var.get())
        stdlib = get_stdlib_modules()
        pkg_map = packages_distributions_map()

        third_party = set()
        for m in sorted(res["imports"]):
            if is_third_party(m, stdlib, pkg_map):
                third_party.add(m)

        dynamic = set()
        for m in sorted(res["dynamic_imports"]):
            if is_third_party(m, stdlib, pkg_map):
                dynamic.add(m)

        self.detected_imports = third_party
        self.detected_dynamic = dynamic
        self.detected_literal_files = set(res["literal_files"])
        self.detected_collect_all = suggest_collect_all(self.detected_imports | self.detected_dynamic)

        self._log(f"Gefundene Imports: {len(res['imports'])}, davon Drittanbieter: {len(third_party)}, dynamisch: {len(dynamic)}")
        if self.detected_collect_all:
            self._log("Collect-All-Empfehlungen: " + ", ".join(self.detected_collect_all))

        self._refresh_imports_list()
        self._refresh_datas_list()
        self._refresh_paths_list()

    def _assemble_datas(self) -> list[tuple[Path, str]]:
        result: list[tuple[Path, str]] = []
        script = Path(self.script_var.get()).resolve()
        project_root = script.parent

        # manual
        result.extend(self.manual_datas)

        # literal files
        mapped_literal = map_add_data_entries(list(self.detected_literal_files), project_root)
        for t in mapped_literal:
            if t not in result:
                result.append(t)

        # auto dirs
        if self.auto_data_dirs_var.get():
            for p, dest in auto_data_dirs(project_root):
                if (p, dest) not in result:
                    result.append((p, dest))
        return result

    def _assemble_hidden_imports(self) -> list[str]:
        # combine detected + manual
        s = set(self.detected_imports) | set(self.detected_dynamic) | set(self.manual_hidden)
        return sorted(s)

    # --- NEW: Versioninfo-Datei erzeugen (Windows) ---------------------------
    @staticmethod
    def _parse_version_tuple(s: str) -> tuple[int, int, int, int]:
        parts = [p for p in re.split(r"[^\d]+", s) if p][:4]
        nums = [int(x) for x in parts[:4]]
        return tuple((nums + [0, 0, 0, 0])[:4])  # (major, minor, patch, build)

    def _write_version_file(self, exe_name: str) -> Optional[Path]:
        if os.name != "nt" or not self.use_versioninfo_var.get():
            return None
        vmaj, vmin, vpatch, vbuild = self._parse_version_tuple(self.version_var.get() or "1.0.0.0")
        content = f'''# UTF-8
# auto-generated by Smart PyInstaller Builder
VSVersionInfo(
  ffi=FixedFileInfo(
    filevers=({vmaj}, {vmin}, {vpatch}, {vbuild}),
    prodvers=({vmaj}, {vmin}, {vpatch}, {vbuild}),
    mask=0x3f, flags=0x0, OS=0x40004, fileType=0x1, subtype=0x0, date=(0, 0)
  ),
  kids=[
    StringFileInfo([StringTable('040904E4', [
      StringStruct('CompanyName', u'{self.publisher_var.get()}'),
      StringStruct('FileDescription', u'{self.desc_var.get() or exe_name}'),
      StringStruct('FileVersion', u'{self.version_var.get()}'),
      StringStruct('InternalName', u'{exe_name}'),
      StringStruct('LegalCopyright', u'{self.copyright_var.get()}'),
      StringStruct('OriginalFilename', u'{exe_name}.exe'),
      StringStruct('ProductName', u'{self.product_var.get() or exe_name}'),
      StringStruct('ProductVersion', u'{self.version_var.get()}'),
      StringStruct('Comments', u'Build: {datetime.now().isoformat(timespec="seconds")}')
    ])]),
    VarFileInfo([VarStruct('Translation', [1033, 1200])])
  ]
)
'''
        dst = Path(self.script_var.get()).parent / f"{exe_name}.versioninfo.txt"
        dst.write_text(content, encoding="utf-8")
        return dst

    def _build(self):
        script = Path(self.script_var.get().strip()) if self.script_var.get().strip() else None
        if not script or not script.exists():
            messagebox.showerror(APP_TITLE, "Bitte zuerst eine Python-Datei wählen.")
            return
        ok, _ = ensure_pyinstaller_available(self._log)
        if not ok:
            if not messagebox.askyesno(APP_TITLE, "PyInstaller nicht gefunden. Jetzt installieren?"):
                return
            self._install_pyinstaller_bg()
            return

        name = self.name_var.get().strip() or script.stem
        icon = Path(self.icon_var.get().strip()) if self.icon_var.get().strip() else None

        datas = self._assemble_datas()
        hidden_imports = self._assemble_hidden_imports()
        collect_all_pkgs = self.detected_collect_all if self.collect_all_var.get() else []
        extra_paths = self.extra_paths

        version_file = self._write_version_file(name)

        cmd = build_command(
            script_path=script,
            name=name,
            onefile=self.onefile_var.get(),
            windowed=self.windowed_var.get(),
            clean=self.clean_var.get(),
            icon_path=icon,
            add_datas=datas,
            hidden_imports=hidden_imports,
            collect_all_pkgs=collect_all_pkgs,
            extra_paths=extra_paths,
            version_file=version_file,
            noupx=self.noupx_var.get(),
            runtime_tmpdir=(self.runtime_tmpdir_var.get().strip() or None),
        )
        self._log("Starte Build:")
        self._log(" ".join(shlex.quote(x) for x in cmd))
        self._start_build_thread(cmd, script.parent)

    def _start_build_thread(self, cmd: list[str], cwd: Path):
        if self.build_thread and self.build_thread.is_alive():
            messagebox.showwarning(APP_TITLE, "Build läuft bereits.")
            return
        self.build_thread = threading.Thread(target=self._run_build, args=(cmd, cwd), daemon=True)
        self.build_thread.start()

    def _run_build(self, cmd: list[str], cwd: Path):
        try:
            p = subprocess.Popen(
                cmd,
                cwd=str(cwd),
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                env=_with_peutils_syntaxwarning_filter_env(),
            )
            for line in p.stdout:  # type: ignore
                self._log(line.rstrip())
            rc = p.wait()
            if rc == 0:
                self._log("Build erfolgreich.")
                dist = cwd / "dist"
                if dist.exists():
                    self._log(f"Ausgabe: {dist}")
            else:
                self._log(f"Build fehlgeschlagen. Rückgabecode {rc}.")
        except Exception as e:
            self._log(f"Build-Fehler: {e}")

    def _open_dist(self):
        script = self.script_var.get().strip()
        if not script:
            return
        dist = Path(script).parent / "dist"
        if dist.exists():
            open_folder(dist)
        else:
            messagebox.showinfo(APP_TITLE, "Kein dist-Ordner gefunden.")

    def _save_profile(self):
        script = self.script_var.get().strip()
        if not script:
            messagebox.showerror(APP_TITLE, "Kein Script gewählt.")
            return
        profile = {
            "script": script,
            "name": self.name_var.get().strip(),
            "icon": self.icon_var.get().strip(),
            "onefile": self.onefile_var.get(),
            "windowed": self.windowed_var.get(),
            "clean": self.clean_var.get(),
            "scan_all": self.scan_all_var.get(),
            "auto_data_dirs": self.auto_data_dirs_var.get(),
            "collect_all": self.collect_all_var.get(),
            "extra_paths": [str(p) for p in self.extra_paths],
            "manual_datas": [(str(p), dest) for p, dest in self.manual_datas],
            "manual_hidden": list(self.manual_hidden),
            # NEW
            "noupx": self.noupx_var.get(),
            "runtime_tmpdir": self.runtime_tmpdir_var.get(),
            "profile_meta": {
                "use_versioninfo": self.use_versioninfo_var.get(),
                "publisher": self.publisher_var.get(),
                "product": self.product_var.get(),
                "version": self.version_var.get(),
                "description": self.desc_var.get(),
                "copyright": self.copyright_var.get(),
            },
        }
        fn = Path(script).with_suffix(PROFILE_SUFFIX)
        fn.write_text(json.dumps(profile, indent=2), encoding="utf-8")
        self._log(f"Profil gespeichert: {fn}")

    def _load_profile(self):
        script = self.script_var.get().strip()
        start_dir = Path(script).parent if script else Path.cwd()
        fn = filedialog.askopenfilename(title="Profil laden", initialdir=str(start_dir),
                                        filetypes=[("Buildprofile", f"*{PROFILE_SUFFIX}"), ("Alle", "*.*")])
        if not fn:
            return
        try:
            profile = json.loads(Path(fn).read_text(encoding="utf-8"))
            self.script_var.set(profile.get("script", ""))
            self.name_var.set(profile.get("name", ""))
            self.icon_var.set(profile.get("icon", ""))
            self.onefile_var.set(bool(profile.get("onefile", True)))
            self.windowed_var.set(bool(profile.get("windowed", False)))
            self.clean_var.set(bool(profile.get("clean", True)))
            self.scan_all_var.set(bool(profile.get("scan_all", True)))
            self.auto_data_dirs_var.set(bool(profile.get("auto_data_dirs", True)))
            self.collect_all_var.set(bool(profile.get("collect_all", True)))
            self.extra_paths = [Path(p) for p in profile.get("extra_paths", [])]
            self.manual_datas = [(Path(p), dest) for p, dest in profile.get("manual_datas", [])]
            self.manual_hidden = list(profile.get("manual_hidden", []))

            # NEW: weitere Felder
            self.noupx_var.set(bool(profile.get("noupx", True)))
            self.runtime_tmpdir_var.set(profile.get("runtime_tmpdir", ""))

            m = profile.get("profile_meta", {})
            self.use_versioninfo_var.set(bool(m.get("use_versioninfo", True)))
            self.publisher_var.set(m.get("publisher", ""))
            self.product_var.set(m.get("product", ""))
            self.version_var.set(m.get("version", "1.0.0"))
            self.desc_var.set(m.get("description", ""))
            self.copyright_var.set(m.get("copyright", ""))

            self._analyze()
            self._refresh_datas_list()
            self._refresh_paths_list()
            self._refresh_imports_list()
            self._log(f"Profil geladen: {fn}")
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"Profil konnte nicht geladen werden:\n{e}")


def main():
    root = tk.Tk()
    BuilderGUI(root)
    root.mainloop()


if __name__ == "__main__":
    main()
