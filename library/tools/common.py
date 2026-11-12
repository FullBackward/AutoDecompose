"""Shared helpers for the library tools. Standard library only.

Every tool fetches source code by *raw view* at a pinned commit; no API token is
used and no mirror of a source is kept. Fetched files used only for searching
go to library/cache/ (git-ignored, safe to delete); files that belong to an
entry are copied verbatim into library/entries/<id>/code/.
"""
from __future__ import annotations

import datetime as _dt
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

for _s in (sys.stdout, sys.stderr):                    # Windows consoles default to a
    try:                                                # legacy code page; Lean and Rocq
        _s.reconfigure(encoding="utf-8", errors="replace")  # text is full of Unicode
    except Exception:
        pass

LIB = Path(__file__).resolve().parent.parent          # library/
REPO = LIB.parent
LEDGER = LIB / "ledger"
SOURCES = LIB / "sources"
ENTRIES = LIB / "entries"
CACHE = LIB / "cache"
REPORTS = LIB / "reports"

USER_AGENT = "library-harvest/0.1 (research; raw view only)"
POLITE_DELAY = 0.25  # seconds between network requests from one process

MOVES = [
    "case-split", "induction", "iff-split", "witness", "extensionality",
    "calc-chain", "suffices-or-strengthen", "key-invariant",
    "generalise-then-instantiate", "interface-lemma", "per-callee-lemma",
    "sorrify-at-failure", "extract-have", "blueprint-node", "statement-object",
    "workflow", "other",
]
KINDS = ["instance", "skill", "anti-pattern"]
STATUSES = ["draft", "verified", "accepted", "flagged", "deprecated"]
VERDICTS = ["unverified", "verified", "refuted", "unverifiable"]
EVIDENCE_KINDS = ["check", "author-statement", "measurement", "known-use"]
CHECK_STATUSES = ["pass", "fail", "not-run", "ci-record"]

LANG_BY_EXT = {
    ".lean": "lean", ".v": "rocq", ".thy": "isabelle", ".ML": "isabelle-ml",
    ".ml": "ocaml", ".md": "markdown", ".tex": "latex", ".py": "python",
    ".sml": "sml", ".json": "json", ".yaml": "yaml", ".yml": "yaml",
}


def now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def die(msg: str, code: int = 1) -> None:
    print(f"error: {msg}", file=sys.stderr)
    sys.exit(code)


def read_json(p: Path):
    return json.loads(p.read_text(encoding="utf-8"))


def load_entries() -> tuple[list[dict], list[str]]:
    """Every entry.json that parses, and the ids of those that do not (a worker may be
    writing one while a run is going; a broken one fails validate_entry.py anyway)."""
    good, bad = [], []
    for d in sorted(p for p in ENTRIES.iterdir() if (p / "entry.json").exists()):
        try:
            good.append(read_json(d / "entry.json"))
        except (json.JSONDecodeError, UnicodeDecodeError):
            bad.append(d.name)
    return good, bad


def write_json(p: Path, obj) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


# ---------------------------------------------------------------- sources

def parse_url(url: str) -> dict:
    """Split a repository URL into host kind, base, owner/repo."""
    m = re.match(r"https://github\.com/([^/]+)/([^/#?]+?)(?:\.git)?/?$", url)
    if m:
        return {"host": "github", "base": "https://github.com", "path": f"{m[1]}/{m[2]}"}
    m = re.match(r"(https://[^/]*gitlab[^/]*)/(.+?)(?:\.git)?/?$", url)
    if m:
        return {"host": "gitlab", "base": m[1], "path": m[2]}
    die(f"unsupported repository URL: {url}")


def raw_url(src: dict, path: str) -> str:
    sha, base, p = src["commit"], src["base"], src["repo_path"]
    if src["host"] == "github":
        return f"https://raw.githubusercontent.com/{p}/{sha}/{path}"
    return f"{base}/{p}/-/raw/{sha}/{path}"


def permalink(src: dict, path: str, lines: list[int] | None = None) -> str:
    sha, base, p = src["commit"], src["base"], src["repo_path"]
    if src["host"] == "github":
        url = f"{base}/{p}/blob/{sha}/{path}"
        return url + (f"#L{lines[0]}-L{lines[1]}" if lines else "")
    url = f"{base}/{p}/-/blob/{sha}/{path}"
    return url + (f"#L{lines[0]}-{lines[1]}" if lines else "")


def load_source(source_id: str) -> dict:
    p = SOURCES / source_id / "source.json"
    if not p.exists():
        die(f"source '{source_id}' is not registered (run register_source.py)")
    return read_json(p)


def ls_remote(url: str, ref: str = "HEAD") -> str:
    out = subprocess.run(["git", "ls-remote", url, ref], capture_output=True,
                         text=True, timeout=60)
    if out.returncode != 0 or not out.stdout.strip():
        die(f"git ls-remote failed for {url} {ref}: {out.stderr.strip()}")
    return out.stdout.split()[0]


# ---------------------------------------------------------------- network

_last = [0.0]


def http_get(url: str, tries: int = 3) -> bytes:
    """GET with a generic user agent, politeness delay and backoff."""
    for attempt in range(tries):
        wait = POLITE_DELAY - (time.time() - _last[0])
        if wait > 0:
            time.sleep(wait)
        _last[0] = time.time()
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(req, timeout=30) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            if e.code == 404:
                raise FileNotFoundError(url) from e
            if e.code in (429, 500, 502, 503, 504) and attempt + 1 < tries:
                time.sleep(2 ** attempt * 2)
                continue
            raise
        except urllib.error.URLError:
            if attempt + 1 < tries:
                time.sleep(2 ** attempt * 2)
                continue
            raise
    raise RuntimeError(f"unreachable: {url}")


def fetch_at_commit(src: dict, path: str) -> bytes:
    return http_get(raw_url(src, path))


# ---------------------------------------------------------------- content

def language_of(path: str) -> str:
    return LANG_BY_EXT.get(Path(path).suffix, "other")


def strip_comments(text: str, lang: str) -> str:
    if lang == "lean":
        text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
        text = re.sub(r"--[^\n]*", " ", text)
    elif lang in ("rocq", "isabelle", "isabelle-ml", "ocaml", "sml"):
        prev = None
        while prev != text:                     # nested (* *) comments
            prev = text
            text = re.sub(r"\(\*(?:(?!\(\*).)*?\*\)", " ", text, flags=re.S)
    return text


def normalised_hash(text: str, lang: str) -> str:
    t = strip_comments(text, lang)
    t = re.sub(r"\s+", " ", t).strip()
    return sha256_bytes(t.encode("utf-8"))


def append_jsonl(p: Path, rec: dict) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open("a", encoding="utf-8", newline="\n") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")


def read_jsonl(p: Path) -> list[dict]:
    if not p.exists():
        return []
    out = []
    for i, l in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
        if l.strip():
            try:
                out.append(json.loads(l))
            except json.JSONDecodeError:   # a line being appended while we read
                print(f"# skipped unparsable line {i} of {p.name}", file=sys.stderr)
    return out
