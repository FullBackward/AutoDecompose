"""Register a source repository: pin a commit, copy its licence, write its note.

  py.sh register_source.py URL --id ID --language lean|rocq|isabelle|mixed \
        [--ref HEAD] [--how-found TEXT] [--note TEXT]
  py.sh register_source.py --start-set library/sources/start-set.json [--batch 1 ...]
  py.sh register_source.py --id ID --set-licence SPDX_EXPRESSION --why TEXT [--by NAME] \
        [--licence-file PATH ...]
  py.sh register_source.py --id ID --set-language lean|rocq|isabelle|mixed --why TEXT [--by NAME]

Writes library/sources/<id>/source.json, the licence file(s) copied verbatim,
and SOURCE.md (links, commit, licence, attribution), and appends one record to
ledger/sources.jsonl. A registered source is never re-pinned silently: use
--repin, which appends a new ledger record and keeps the old one.
"""
from __future__ import annotations

import argparse
import re

from common import (SOURCES, LEDGER, append_jsonl, die, http_get, ls_remote,
                    now, parse_url, permalink, raw_url, read_json, write_json)

LICENCE_RE = re.compile(r"^(LICEN[CS]E|COPYING|COPYRIGHT|NOTICE|CeCILL)[\w.\-]*$", re.I)


def root_files(src: dict) -> list[str]:
    """Names of files at the repository root at the pinned commit."""
    import json, shutil, subprocess, tempfile, urllib.parse
    if src["host"] == "github":
        try:
            data = json.loads(http_get(
                f"https://data.jsdelivr.com/v1/packages/gh/{src['repo_path']}@{src['commit']}"))
            return [f["name"] for f in data["files"] if f.get("type") == "file"]
        except Exception:
            pass
    if src["host"] == "gitlab":
        try:
            pid = urllib.parse.quote(src["repo_path"], safe="")
            data = json.loads(http_get(f"{src['base']}/api/v4/projects/{pid}/repository/tree"
                                       f"?ref={src['commit']}&per_page=100"))
            return [f["name"] for f in data if f.get("type") == "blob"]
        except Exception:
            pass
    tmp = tempfile.mkdtemp(prefix="root-")
    try:
        run = lambda *a: subprocess.run(a, cwd=tmp, capture_output=True, text=True, timeout=300)
        run("git", "init", "-q")
        run("git", "remote", "add", "origin", f"{src['base']}/{src['repo_path']}.git")
        run("git", "fetch", "-q", "--depth", "1", "--filter=blob:none", "origin", src["commit"])
        out = run("git", "ls-tree", "--name-only", src["commit"]).stdout
        return [l for l in out.splitlines() if l]
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def detect_spdx(text: str) -> str:
    m = re.search(r"SPDX-License-Identifier:\s*([\w.\-+ ()]+)", text)
    if m:
        return m[1].strip()
    t = " ".join(text.split())
    rules = [
        (r"INRIA Non-Commercial", "LicenseRef-INRIA-Non-Commercial"),
        (r"Apache License,? Version 2\.0", "Apache-2.0"),
        (r"GNU LESSER GENERAL PUBLIC LICENSE Version 2\.1", "LGPL-2.1"),
        (r"GNU LESSER GENERAL PUBLIC LICENSE Version 3", "LGPL-3.0"),
        (r"GNU GENERAL PUBLIC LICENSE Version 2", "GPL-2.0"),
        (r"GNU GENERAL PUBLIC LICENSE Version 3", "GPL-3.0"),
        (r"Mozilla Public License,? (?:Version|v\.) ?2\.0", "MPL-2.0"),
        (r"CeCILL-B", "CECILL-B"),
        (r"CeCILL-C", "CECILL-C"),
        (r"CeCILL", "CECILL-2.1"),
        (r"Attribution-ShareAlike 4\.0", "CC-BY-SA-4.0"),
        (r"Attribution-NonCommercial", "LicenseRef-CC-BY-NC"),
        (r"Attribution 4\.0 International", "CC-BY-4.0"),
        (r"Permission is hereby granted, free of charge", "MIT"),
        (r"Redistribution and use in source and binary forms.*Neither the name", "BSD-3-Clause"),
        (r"Redistribution and use in source and binary forms", "BSD-2-Clause"),
        (r"Boost Software License", "BSL-1.0"),
    ]
    for pat, spdx in rules:
        if re.search(pat, t, flags=re.I):
            return spdx
    return "LicenseRef-unknown"


def register(url: str, sid: str, language: str, ref: str, how_found: str,
             note: str, repin: bool) -> None:
    if not re.fullmatch(r"[a-z0-9][a-z0-9._-]*", sid):
        die(f"bad source id '{sid}': lowercase letters, digits, . _ - only")
    d = SOURCES / sid
    if (d / "source.json").exists() and not repin:
        print(f"skip {sid}: already registered (use --repin to pin again)")
        return
    u = parse_url(url)
    sha = ls_remote(url if url.endswith(".git") else url + ".git", ref)
    src = {"source_id": sid, "url": url, "host": u["host"], "base": u["base"],
           "repo_path": u["path"], "commit": sha, "ref": ref, "language": language,
           "pinned_at": now(), "how_found": how_found, "note": note,
           "licence": "LicenseRef-unknown", "licence_files": []}
    d.mkdir(parents=True, exist_ok=True)
    texts = []
    for name in [n for n in root_files(src) if LICENCE_RE.match(n)]:
        try:
            b = http_get(raw_url(src, name))
        except FileNotFoundError:
            continue
        except Exception as e:  # network trouble: record and move on
            print(f"warn {sid}: {name}: {e}")
            continue
        (d / f"upstream-{name}").write_bytes(b)
        src["licence_files"].append(name)
        texts.append(b.decode("utf-8", "replace"))
    if texts:
        ids = sorted({detect_spdx(t) for t in texts})
        known = [i for i in ids if i != "LicenseRef-unknown"]
        src["licence"] = " AND ".join(known) if known else "LicenseRef-unknown"
    write_json(d / "source.json", src)
    write_note(d, src)
    rec = dict(src)
    rec["event"] = "repin" if repin else "register"
    rec["at"] = now()
    append_jsonl(LEDGER / "sources.jsonl", rec)
    print(f"ok {sid} {sha[:12]} {src['licence']}")


def copy_name(path: str) -> str:
    """The local name of a copied licence file; a file below the root keeps its path, flattened."""
    return "upstream-" + path.replace("/", "--")


def write_note(d, src: dict) -> None:
    """SOURCE.md from source.json."""
    sha = src["commit"]
    lic_links = "\n".join(f"- [{n}]({permalink(src, n)}) (copied here as `{copy_name(n)}`)"
                          for n in src["licence_files"]) or "- no licence file found at the root"
    lang = src["language"] + (f" (registered as {src['language_registered']}; {src.get('language_note', '')})"
                              if src.get("language_registered") else "")
    if src.get("licence_detected"):
        lic = (f"- Licence: `{src['licence']}`, read from the licence files by {src.get('licence_set_by', 'hand')} "
               f"({src.get('licence_note', '')}); the detector had `{src['licence_detected']}`. "
               f"The licence text below governs.\n")
    else:
        lic = f"- Licence (detected): `{src['licence']}`; the licence text below governs.\n"
    (d / "SOURCE.md").write_text(
        f"# Source: {src['source_id']}\n\n"
        f"- Repository: {src['url']}\n"
        f"- Commit (pinned {src['pinned_at']}): `{sha}`\n"
        f"- Browse at this commit: {src['base']}/{src['repo_path']}"
        f"{'/tree/' if src['host'] == 'github' else '/-/tree/'}{sha}\n"
        f"- Language: {lang}\n"
        + lic +
        f"- How found: {src.get('how_found') or 'start set'}\n\n"
        f"## Licence files\n\n{lic_links}\n\n"
        f"## Attribution\n\n"
        f"Code under `library/entries/*/code/` whose entry names this source is copied "
        f"verbatim from the repository above at the pinned commit, under its licence. "
        f"Copyright remains with its authors.\n"
        + (f"\n## Note\n\n{src['note']}\n" if src.get("note") else ""),
        encoding="utf-8")


def set_licence(sid: str, expr: str, why: str, by: str, files: list[str] = ()) -> None:
    """Correct a detected licence after reading the copied licence files. The detected value is
    kept in source.json (licence_detected) and the change is appended to ledger/sources.jsonl.
    FILES are further licence files below the root (a vendored tree's own licence, say), copied
    verbatim at the pinned commit like the root ones."""
    d = SOURCES / sid
    if not (d / "source.json").exists():
        die(f"no source {sid}")
    if not why:
        die("--why is required: say which licence file shows the licence")
    src = read_json(d / "source.json")
    for name in files:
        if name not in src["licence_files"]:
            (d / copy_name(name)).write_bytes(http_get(raw_url(src, name)))
            src["licence_files"].append(name)
    src.setdefault("licence_detected", src["licence"])
    src.update(licence=expr, licence_note=why, licence_set_by=by)
    write_json(d / "source.json", src)
    write_note(d, src)
    append_jsonl(LEDGER / "sources.jsonl", {**src, "event": "licence", "at": now()})
    print(f"ok {sid} licence {expr} (detected {src['licence_detected']})")


def set_language(sid: str, lang: str, why: str, by: str) -> None:
    """Correct the language a source was registered under (the locator's guess), keeping the
    old value in source.json (language_registered) and appending the change to the ledger."""
    d = SOURCES / sid
    if not (d / "source.json").exists():
        die(f"no source {sid}")
    if not why:
        die("--why is required: say what at the pinned commit shows the language")
    src = read_json(d / "source.json")
    src.setdefault("language_registered", src["language"])
    src.update(language=lang, language_note=why, language_set_by=by)
    write_json(d / "source.json", src)
    write_note(d, src)
    append_jsonl(LEDGER / "sources.jsonl", {**src, "event": "language", "at": now()})
    print(f"ok {sid} language {lang} (registered as {src['language_registered']})")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("url", nargs="?")
    ap.add_argument("--id")
    ap.add_argument("--language", default="mixed")
    ap.add_argument("--ref", default="HEAD")
    ap.add_argument("--how-found", default="")
    ap.add_argument("--note", default="")
    ap.add_argument("--repin", action="store_true")
    ap.add_argument("--start-set")
    ap.add_argument("--batch", type=int, action="append", default=[])
    ap.add_argument("--set-licence", metavar="SPDX_EXPRESSION",
                    help="with --id: correct the detected licence of a registered source")
    ap.add_argument("--licence-file", action="append", default=[], metavar="PATH",
                    help="with --set-licence: also copy this licence file below the root")
    ap.add_argument("--set-language", choices=["lean", "rocq", "isabelle", "mixed"],
                    help="with --id: correct the language a source was registered under")
    ap.add_argument("--why", default="", help="with --set-licence or --set-language: the evidence")
    ap.add_argument("--by", default="hand", help="with --set-licence or --set-language: who read it")
    a = ap.parse_args()
    if a.set_licence or a.set_language:
        if not a.id:
            die("--set-licence and --set-language need --id")
        if a.set_language:
            set_language(a.id, a.set_language, a.why, a.by)
        if a.set_licence:
            set_licence(a.id, a.set_licence, a.why, a.by, a.licence_file)
        return
    if a.start_set:
        for s in read_json(__import__("pathlib").Path(a.start_set))["sources"]:
            if a.batch and s.get("batch") not in a.batch:
                continue
            try:
                register(s["url"], s["id"], s["language"], s.get("ref", "HEAD"),
                         "start set", s.get("note", ""), a.repin)
            except SystemExit:
                print(f"FAILED {s['id']}")
        return
    if not (a.url and a.id):
        die("give URL and --id, or --start-set FILE")
    register(a.url, a.id, a.language, a.ref, a.how_found, a.note, a.repin)


if __name__ == "__main__":
    main()
