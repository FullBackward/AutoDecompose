"""ta_graph.py DIR [--dump OUT.json] : graph measures and effort figures from the Turing Agent trace files.
The .js files are data; they are parsed as JSON text and never executed."""
import json
import pathlib
import re
import statistics as st
import sys
from collections import Counter, defaultdict

d = pathlib.Path(sys.argv[1])
dump = {}


def q(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(round(p * (len(xs) - 1))))] if xs else None


def spearman(a, b):
    def rank(x):
        o = sorted(range(len(x)), key=lambda i: x[i])
        r = [0.0] * len(x)
        i = 0
        while i < len(o):
            j = i
            while j + 1 < len(o) and x[o[j + 1]] == x[o[i]]:
                j += 1
            for k in range(i, j + 1):
                r[o[k]] = (i + j) / 2 + 1
            i = j + 1
        return r
    ra, rb = rank(a), rank(b)
    ma, mb = st.mean(ra), st.mean(rb)
    num = sum((x - ma) * (y - mb) for x, y in zip(ra, rb))
    den = (sum((x - ma) ** 2 for x in ra) * sum((y - mb) ** 2 for y in rb)) ** 0.5
    return num / den if den else float("nan")


for p in sorted(d.glob("data_traces_openai-math-*.js")):
    t = p.read_text(encoding="utf-8")
    m = re.search(r'TA\.traceData\["[^"]+"\]\s*=\s*', t)
    obj, _ = json.JSONDecoder().raw_decode(t[m.end():])
    meta, nodes = obj["meta"], obj["nodes"]
    by = {n["id"]: n for n in nodes}
    proved = [n for n in nodes if n.get("status") == "proved"]
    dropped = [n for n in nodes if n.get("status") == "dropped"]
    deps = {n["id"]: [x for x in (n.get("deps") or [])] for n in nodes}
    users = defaultdict(list)
    for a, bs in deps.items():
        for b in bs:
            users[b].append(a)
    root = "root" if "root" in by else None
    # reachability from the root along deps
    seen, stack = set(), [root] if root else []
    while stack:
        x = stack.pop()
        if x in seen or x not in by:
            continue
        seen.add(x)
        stack.extend(deps.get(x, []))
    depth = {}

    def dp(x, path=()):
        if x in depth:
            return depth[x]
        if x in path:
            return 0
        ch = [c for c in deps.get(x, []) if c in by]
        depth[x] = 0 if not ch else 1 + max(dp(c, path + (x,)) for c in ch)
        return depth[x]

    print("=" * 96)
    print(meta["id"], "|", meta["title"], "|", meta["model"])
    print(f" wall {meta['duration']} s = {meta['duration'] / 3600:.1f} h; active {meta['active']} s = {meta['active'] / 3600:.1f} h")
    print(" stats:", meta["stats"])
    print(f" nodes {len(nodes)}: proved {len(proved)}, dropped {len(dropped)}; root present: {bool(root)}")
    pr_ids = {n["id"] for n in proved}
    n_edges = sum(len([c for c in deps[n["id"]] if c in by]) for n in nodes)
    dangling = sorted({c for n in nodes for c in deps[n["id"]] if c not in by})
    print(f" edges (deps inside the node set) {n_edges}; deps that name no node: {len(dangling)} {dangling[:6]}")
    if root:
        print(f" root: direct deps {len(deps[root])}; height of the graph below the root {dp(root)}")
        reach = seen - {root}
        aux = pr_ids - {root}
        print(f" proved auxiliary nodes {len(aux)}; reachable from the root {len(aux & reach)}; not reachable {len(aux - reach)}")
        print("   not reachable:", sorted(aux - reach))
    no_users = sorted(n["id"] for n in proved if n["id"] != root and not users.get(n["id"]))
    print(f" proved nodes that no node lists as a dep: {len(no_users)}", no_users[:20])
    print(" flag used:", dict(Counter(str(n.get("used")) for n in proved)), "| used=False:", sorted(n["id"] for n in proved if n.get("used") is False))
    print(" flag reviewed:", dict(Counter(str(n.get("reviewed")) for n in proved)), "| risk:", dict(Counter(str(n.get("risk")) for n in proved)),
          "| route:", dict(Counter(str(n.get("route")) for n in proved)))
    fo = [len([c for c in deps[n["id"]] if c in by]) for n in proved]
    fi = [len(users.get(n["id"], [])) for n in proved if n["id"] != root]
    leaves = [n for n in proved if not [c for c in deps[n["id"]] if c in by]]
    print(f" fan-out (deps per proved node): max {max(fo)}, mean {st.mean(fo):.2f}; leaves {len(leaves)} of {len(proved)}")
    if fi:
        print(f" users per proved auxiliary node: max {max(fi)}, mean {st.mean(fi):.2f}; used by 2 or more nodes: {sum(1 for x in fi if x >= 2)}")
    dur = [(n["id"], n["t_ok"] - n["t_in"]) for n in proved if n.get("t_ok") is not None and n.get("t_in") is not None]
    ds = [x for _, x in dur]
    if ds:
        print(f" time from entry to proof, s: n {len(ds)}, median {st.median(ds):.0f}, p90 {q(ds, .9):.0f}, max {max(ds):.0f}, sum {sum(ds):.0f} ({sum(ds) / 3600:.1f} h)")
        top = sorted(dur, key=lambda x: -x[1])[:5]
        print("   slowest:", [(i, round(x)) for i, x in top])
    pb = [n.get("probes") or 0 for n in proved]
    fl = [n.get("fails") or 0 for n in proved]
    print(f" probes per proved node: median {st.median(pb)}, max {max(pb)}, sum {sum(pb)}; fails: median {st.median(fl)}, max {max(fl)}, sum {sum(fl)}")
    print(f" proved nodes with 0 fails: {sum(1 for x in fl if x == 0)} of {len(fl)}; with 5 or more fails: {sum(1 for x in fl if x >= 5)}")
    sl = [len(n.get("statement") or "") for n in proved]
    bl = [len((n.get("body") or "").splitlines()) for n in proved]
    print(f" statement chars: median {st.median(sl)}, max {max(sl)}; proof body lines: median {st.median(bl)}, max {max(bl)}, sum {sum(bl)}")
    if len(proved) > 5:
        pairs = [(len(n.get("statement") or ""), n.get("fails") or 0, len((n.get("body") or "").splitlines()),
                  (n["t_ok"] - n["t_in"]) if n.get("t_ok") is not None else 0, len([c for c in deps[n["id"]] if c in by])) for n in proved if n["id"] != root]
        S, F, B, T, D = zip(*pairs)
        print(f" Spearman over {len(pairs)} auxiliary nodes: statement length vs fails {spearman(S, F):+.2f}; body lines vs fails {spearman(B, F):+.2f}; "
              f"statement length vs time {spearman(S, T):+.2f}; deps vs fails {spearman(D, F):+.2f}")
    print(" dropped nodes:", [(n["id"], n.get("t_in"), n.get("t_out")) for n in dropped][:10])
    tl = obj.get("timeline") or []
    print(" timeline:", len(tl), "items; first:", json.dumps(tl[0], ensure_ascii=False)[:260] if tl else None)
    dump[meta["id"]] = {"meta": {k: meta[k] for k in ("id", "title", "model", "duration", "active", "stats")},
                        "nodes": [{"id": n["id"], "status": n.get("status"), "deps": deps[n["id"]], "used": n.get("used"),
                                   "reviewed": n.get("reviewed"), "risk": n.get("risk"), "route": n.get("route"),
                                   "t_in": n.get("t_in"), "t_ok": n.get("t_ok"), "t_out": n.get("t_out"),
                                   "probes": n.get("probes"), "fails": n.get("fails"),
                                   "statement_chars": len(n.get("statement") or ""),
                                   "body_lines": len((n.get("body") or "").splitlines())} for n in nodes]}

if "--dump" in sys.argv:
    out = pathlib.Path(sys.argv[sys.argv.index("--dump") + 1])
    out.write_text(json.dumps(dump, ensure_ascii=False, indent=1, sort_keys=True), encoding="utf-8", newline="\n")
    print("wrote", out)
