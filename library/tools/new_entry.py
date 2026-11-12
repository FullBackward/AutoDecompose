"""Create a library entry: copy whole files verbatim and scaffold its record.

  py.sh new_entry.py --source SOURCE_ID --kind instance|skill|anti-pattern \
        --move MOVE --title "..." \
        --site PATH:A-B:ROLE[:NAME] [--site ...] [--file PATH ...] [--run RUN_ID]

ROLE is parent, child, skeleton, skill-text or context. Every file named by a
site or by --file is fetched at the source's pinned commit and stored whole,
byte for byte, under entries/<id>/code/<original path>. The excerpt of each
site is inserted into README.md by this tool, so that no agent retypes code.
The analyst then fills the TODO parts of README.md and entry.json.
Prints the new entry id.
"""
from __future__ import annotations

import argparse
import re

from common import (ENTRIES, KINDS, MOVES, die, fetch_at_commit, language_of,
                    load_source, normalised_hash, now, permalink, sha256_bytes,
                    write_json)

FENCE = {"lean": "lean", "rocq": "coq", "isabelle": "isabelle", "isabelle-ml": "sml",
         "markdown": "markdown", "latex": "latex", "python": "python"}
ROLES = ["parent", "child", "skeleton", "skill-text", "context"]


def parse_site(s: str) -> dict:
    m = re.fullmatch(r"(.+?):(\d+)-(\d+):([a-z-]+)(?::(.+))?", s)
    if not m:
        die(f"bad --site '{s}', expected PATH:A-B:ROLE[:NAME]")
    a, b = int(m[2]), int(m[3])
    if a < 1 or b < a:
        die(f"bad line range in --site '{s}'")
    if m[4] not in ROLES:
        die(f"bad role '{m[4]}' in --site; one of {ROLES}")
    return {"path": m[1], "lines": [a, b], "role": m[4], "name": m[5] or ""}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", required=True)
    ap.add_argument("--kind", required=True, choices=KINDS)
    ap.add_argument("--move", required=True, choices=MOVES)
    ap.add_argument("--title", required=True)
    ap.add_argument("--site", action="append", default=[], required=True)
    ap.add_argument("--file", action="append", default=[])
    ap.add_argument("--run", default="manual")
    ap.add_argument("--agent", default="extractor")
    a = ap.parse_args()

    src = load_source(a.source)
    sites = [parse_site(s) for s in a.site]
    paths = list(dict.fromkeys([s["path"] for s in sites] + a.file))
    blobs = {}
    for p in paths:
        try:
            blobs[p] = fetch_at_commit(src, p)
        except FileNotFoundError:
            die(f"{p} does not exist at {src['commit'][:12]} in {a.source}")

    lang = language_of(sites[0]["path"])
    excerpts = []
    for s in sites:
        lines = blobs[s["path"]].decode("utf-8").splitlines()
        if s["lines"][1] > len(lines):
            die(f"{s['path']} has {len(lines)} lines; site asks for {s['lines']}")
        text = "\n".join(lines[s["lines"][0] - 1:s["lines"][1]])
        s["excerpt_sha256"] = sha256_bytes(text.encode("utf-8"))
        s["permalink"] = permalink(src, s["path"], s["lines"])
        excerpts.append(text)

    key = normalised_hash("\n".join(excerpts), lang)
    eid = f"{lang}-{a.move}-{a.source}-{key[:8]}"
    d = ENTRIES / eid
    if d.exists():
        die(f"entry {eid} already exists (same content from the same source)")
    files = []
    for p, b in blobs.items():
        dest = d / "code" / p
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(b)
        files.append({"path": p, "bytes": len(b), "sha256": sha256_bytes(b),
                      "permalink": permalink(src, p)})

    entry = {
        "id": eid, "kind": a.kind, "status": "draft", "title": a.title,
        "intent": "TODO", "move": a.move, "also_known_as": [], "language": lang,
        "source": {"source_id": a.source, "url": src["url"], "commit": src["commit"],
                   "licence": src["licence"]},
        "files": files, "sites": sites,
        "parent": {"name": "TODO", "statement": "TODO"} if a.kind != "skill" else None,
        "children": [],
        "applicability": {"goal_shape": "TODO", "use_when": "TODO", "avoid_when": "TODO"},
        "claims": [],
        "metrics": {}, "consequences": "TODO", "known_uses": [], "related": [],
        "rule": {"f10_rule": None, "relation": "none"},
        "content_key": key,
        "provenance_log": [{"field": "files,sites", "agent_role": a.agent,
                            "run": a.run, "at": now()}],
    }
    write_json(d / "entry.json", entry)

    short = src["commit"][:12]
    out = [f"# {a.title}", "",
           "| | |", "|---|---|",
           f"| Kind | {a.kind} |", f"| Move | {a.move} |", f"| Language | {lang} |",
           f"| Status | draft |",
           f"| Source | [{a.source}](../../sources/{a.source}/SOURCE.md) at `{short}` |",
           f"| Licence | `{src['licence']}` |", "",
           "## Intent", "", "TODO: one or two sentences on what this decomposition achieves.", "",
           "## The decomposition", ""]
    for s, text in zip(sites, excerpts):
        name = f" `{s['name']}`" if s["name"] else ""
        ticks = "`" * max(3, 1 + max((len(r) for r in re.findall(r"`+", text)), default=0))
        out += [f"### {s['role']}{name}: [`{s['path']}` lines {s['lines'][0]}-{s['lines'][1]}]"
                f"({s['permalink']}) ([local copy](code/{s['path']}))", "",
                f"{ticks}{FENCE.get(language_of(s['path']), '')}", text, ticks, ""]
    out += ["TODO: explain how the parts fit: which child closes which obligation, "
            "and how each child was closed.", "",
            "## Why it is good", "",
            "TODO: numbered claims, each matching one entry of `claims` in entry.json, "
            "with its kind of evidence and a pointer.", "",
            "## When to use it, and when not", "", "TODO", "",
            "## Consequences", "", "TODO: obligations created, failure modes.", "",
            "## Verification", "", "<!-- verification:start -->",
            "Not yet verified.", "<!-- verification:end -->", "",
            "## Source and licence", "",
            f"Every file under [`code/`](code/) is copied whole and unmodified from "
            f"{src['url']} at commit `{src['commit']}`, under `{src['licence']}`; "
            f"see the [source note](../../sources/{a.source}/SOURCE.md) for the licence text "
            f"and attribution.", ""]
    (d / "README.md").write_text("\n".join(out), encoding="utf-8")
    print(eid)


if __name__ == "__main__":
    main()
