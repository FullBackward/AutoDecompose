"""Build a page for browsing the declaration graph of every entry.

  py.sh features/graph_viewer.py [--out PATH] [--fragment PATH]

Reads features/graphs.jsonl and features/graph-features.jsonl (written by
feature_graph.py), features/term-features.jsonl (written by feature_terms.py,
for the count of children closed by automation alone), and for each entry its
entry.json (title, move, status,
intent, claims, the parent's permalink) and the latest verdict on each claim
from checks/<id>.json. Writes one self-contained HTML file, by default
features/graph-viewer.html, which opens in a browser without a server: pick an
entry, see its parent, children and the declarations between them, which
names which, and why the entry is recorded as a good decomposition (its
intent and its claims with their verdicts).

--fragment writes the same page without the document skeleton, for hosts that
add their own. The page is a pure function of its inputs: no clock, no
network. It is generated, so it is git-ignored; rebuild it after
feature_graph.py --all or after claims change. Standard library only.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))   # library/tools, for the two modules below
from common import ENTRIES, LIB, read_json  # noqa: E402
from record_verdict import latest  # noqa: E402

FEATURES = LIB / "features"
TEMPLATE = Path(__file__).with_name("graph_viewer_template.html")
ROLE = ["parent", "child", "skeleton", "context", "other"]
TYPE = ["decl", "local", "region", "external", "subgoal"]
KIND = {"uses": 0, "contains": 1, "subgoal": 2}
WHERE = {"body": 0, "statement": 1, "both": 2, None: 3}
SKELETON = ('<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
            '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n'
            "<style>body{margin:0}img{max-width:100%}[hidden]{display:none!important}</style>\n"
            "</head>\n<body>\n__PAGE__\n</body>\n</html>\n")


def load(p: Path) -> list[dict]:
    return [json.loads(line) for line in p.read_text(encoding="utf-8").splitlines()]


def slim_node(n: dict, file_index: dict[str, int]) -> dict:
    d = {"y": TYPE.index(n["type"]), "r": ROLE.index(n["role"]), "s": n.get("short") or n.get("name") or "(unnamed)"}
    if n.get("name") and n["name"] != d["s"]:
        d["f"] = n["name"]
    for key, src in (("c", "cls"), ("k", "kind"), ("u", "n_users"), ("d", "n_deps"), ("h", "depth"), ("q", "resolution")):
        if n.get(src) is not None:
            d[key] = n[src]
    if n.get("path"):
        d["p"] = file_index[n["path"]]
    if n.get("lines"):
        d["a"], d["b"] = n["lines"]
    if n.get("flags"):
        d["g"] = n["flags"]
    if n.get("recursive"):
        d["rec"] = 1
    if n.get("on_cycle"):
        d["cyc"] = 1
    return d


def build() -> tuple[str, dict]:
    graphs = load(FEATURES / "graphs.jsonl")
    flat = {r["id"]: r for r in load(FEATURES / "graph-features.jsonl")}
    terms = {r["id"]: r["flat"] for r in load(FEATURES / "term-features.jsonl")}
    entries, n_nodes, n_edges = [], 0, 0
    for g in graphs:
        if g["graph_status"] != "ok":
            continue
        e = read_json(ENTRIES / g["id"] / "entry.json")
        f = flat[g["id"]]
        verdicts = latest(g["id"])
        files = sorted({n["path"] for n in g["nodes"] if n.get("path")})
        index = {p: i for i, p in enumerate(files)}
        nodes = [slim_node(n, index) for n in g["nodes"]]
        edges = [[x["s"], x["t"], KIND[x["kind"]], WHERE[x.get("where")], x.get("n_stmt") or 0,
                  x.get("n_body") or 0, x.get("match") or "", x.get("line") or 0] for x in g["edges"]]
        parent_site = next((s for s in e["sites"] if s.get("role") == "parent"), None)
        claims = [[c.get("n"), c.get("evidence_kind"), c.get("claim") or "", str(c.get("evidence") or ""),
                   (verdicts.get(("claim", str(c.get("n")))) or {}).get("value", "unverified")] for c in e["claims"]]
        entries.append({
            "id": g["id"], "t": e["title"], "l": g["language"], "m": e["move"], "s": e["status"],
            "src": e["source"]["source_id"], "u": (parent_site or {}).get("permalink"),
            "w": e.get("intent") or "", "cl": claims,
            "fx": {"named": f.get("n_children_named"), "sub": f.get("n_children_subgoal"), "fan": f.get("fanout_cited"),
                   "depth": f.get("depth_below_parent"), "glue": f.get("glue_share_lines"),
                   "reused": f.get("children_reused"), "decl": f.get("n_children_decl"),
                   "auto": terms[g["id"]].get("d_n_children_automation_alone"),
                   "proofs": terms[g["id"]].get("d_n_child_proofs")},
            "files": files, "n": nodes, "e": edges,
        })
        n_nodes += len(nodes)
        n_edges += len(edges)
    meta = {"graphs": len(entries), "entries": len(graphs), "nodes": n_nodes, "edges": n_edges,
            "version": graphs[0]["extractor_version"]}
    blob = json.dumps({"entries": entries, "meta": meta}, ensure_ascii=False, separators=(",", ":")).replace("<", "\\u003c")
    html = TEMPLATE.read_text(encoding="utf-8")
    if html.count("__DATA__") != 1:
        raise SystemExit("graph_viewer_template.html must hold the marker __DATA__ exactly once")
    return html.replace("__DATA__", blob), meta


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", type=Path, default=FEATURES / "graph-viewer.html", help="the standalone page")
    ap.add_argument("--fragment", type=Path, help="also write the page without its document skeleton")
    a = ap.parse_args()
    page, meta = build()
    a.out.write_text(SKELETON.replace("__PAGE__", page), encoding="utf-8", newline="\n")
    print(f"wrote {a.out}: {meta['graphs']} graphs, {meta['nodes']} nodes, {meta['edges']} edges, "
          f"{a.out.stat().st_size / 1e6:.2f} MB")
    if a.fragment:
        a.fragment.write_text(page, encoding="utf-8", newline="\n")
        print(f"wrote {a.fragment}")


if __name__ == "__main__":
    main()
