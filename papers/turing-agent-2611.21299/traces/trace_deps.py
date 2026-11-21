"""ta_graph2.py DIR : second pass over the Turing Agent traces: declared deps against deps that the proof body names,
concentration of failures, growth of the graph over time, level widths. Data is parsed, never executed."""
import json
import pathlib
import re
import sys
from collections import Counter, defaultdict

d = pathlib.Path(sys.argv[1])
FIG = {  # nodes drawn grey ("not referenced") in the paper's figures 7 and 9, read by the reviewer
    "openai-math-186-ds": ["low_degree_fourier_bound", "completion_high_degree_div"],
    "openai-math-235": ["clause_kill_probability", "cap_removal_error_bound", "delay_sq_le_cap_sq", "duration_pivot_rpow",
                        "sum_duration_pivot_le", "residual_filter_commute", "blockKill_zero_baseline",
                        "blockKill_increment_jensen_bridge", "occupation_reward_expected_drift", "occupation_reward_sum_bound",
                        "occupation_reward_sum_linear_horizon", "favg_pi_prod"],
}
for p in sorted(d.glob("data_traces_openai-math-*.js")):
    t = p.read_text(encoding="utf-8")
    m = re.search(r'TA\.traceData\["[^"]+"\]\s*=\s*', t)
    obj, _ = json.JSONDecoder().raw_decode(t[m.end():])
    meta, nodes = obj["meta"], obj["nodes"]
    by = {n["id"]: n for n in nodes}
    proved = [n for n in nodes if n.get("status") == "proved"]
    if len(proved) < 2:
        continue
    print("=" * 96)
    print(meta["id"])
    ids = sorted(by, key=len, reverse=True)

    def named(body):
        toks = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", body or ""))
        parts = {x.split(".")[-1] for x in toks} | toks
        return {i for i in ids if i in parts}

    declared = {n["id"]: [c for c in (n.get("deps") or []) if c in by] for n in nodes}
    cited = {n["id"]: sorted(named(n.get("body")) - {n["id"]}) for n in proved}
    n_decl = sum(len(declared[n["id"]]) for n in proved)
    both = sum(len(set(declared[n["id"]]) & set(cited[n["id"]])) for n in proved)
    only_decl = [(n["id"], sorted(set(declared[n["id"]]) - set(cited[n["id"]]))) for n in proved if set(declared[n["id"]]) - set(cited[n["id"]])]
    only_cited = [(n["id"], sorted(set(cited[n["id"]]) - set(declared[n["id"]]))) for n in proved if set(cited[n["id"]]) - set(declared[n["id"]])]
    print(f" declared deps {n_decl}; of these the proof body names {both}; declared but not named: {n_decl - both} in {len(only_decl)} nodes; named but not declared: {sum(len(x) for _, x in only_cited)} in {len(only_cited)} nodes")
    print("   declared, not named (first 6):", only_decl[:6])
    print("   named, not declared (first 6):", only_cited[:6])

    def reach(edges):
        seen, stack = set(), ["root"]
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            stack.extend(edges.get(x, []))
        return seen

    aux = {n["id"] for n in proved} - {"root"}
    r_decl, r_cit = reach(declared), reach(cited)
    print(f" auxiliary proved {len(aux)}; not reachable by declared deps {len(aux - r_decl)}; not reachable by named deps {len(aux - r_cit)}")
    print("   not reachable by named deps:", sorted(aux - r_cit))
    root_cited = set(cited.get("root", []))
    print(f" root: declared deps {len(declared['root'])}, named in the root body {len(root_cited)}")
    grey = FIG.get(meta["id"], [])
    miss = [g for g in grey if g not in by]
    print(f" figure grey nodes {len(grey)} (ids not found in the trace: {miss})")
    print("   grey nodes not reachable by named deps:", sorted(set(grey) & (aux - r_cit)))
    users_c = defaultdict(set)
    for a, bs in cited.items():
        for b in bs:
            users_c[b].add(a)
    print("   grey nodes -> who names them:", {g: sorted(users_c.get(g, [])) for g in grey if g in by})
    print("   grey nodes -> used flag:", {g: by[g].get("used") for g in grey if g in by})
    # concentration of failures
    fl = sorted(((n.get("fails") or 0, n["id"]) for n in proved), reverse=True)
    tot = sum(x for x, _ in fl) or 1
    k = max(1, round(0.1 * len(fl)))
    print(f" failures: total {tot}; top {k} nodes (10 %) hold {sum(x for x, _ in fl[:k]) / tot:.0%}; top 3: {fl[:3]}")
    pb = sorted(((n.get("probes") or 0, n["id"]) for n in proved), reverse=True)
    totp = sum(x for x, _ in pb) or 1
    print(f" probes: total {totp}; top {k} nodes hold {sum(x for x, _ in pb[:k]) / totp:.0%}")
    rv = [n for n in proved if n.get("reviewed")]
    print(" reviewed nodes:", [(n["id"], n.get("fails"), n.get("probes"), n.get("route")) for n in rv])
    # growth of the graph over time
    dur = meta["duration"]
    tin = sorted(n.get("t_in") or 0 for n in nodes)
    print(f" node entry times: distinct {len(set(tin))}; entered in the first 10 % of the run {sum(1 for x in tin if x <= 0.1 * dur)} of {len(tin)}; "
          f"in the first half {sum(1 for x in tin if x <= 0.5 * dur)}; quartiles of entry time as share of run "
          f"{tin[len(tin) // 4] / dur:.2f} {tin[len(tin) // 2] / dur:.2f} {tin[3 * len(tin) // 4] / dur:.2f}")
    big = max(proved, key=lambda n: len(declared[n["id"]]))
    print(f" largest declared fan-out: {big['id']} with {len(declared[big['id']])} deps; names {len(cited[big['id']])} of them in its body ({len((big.get('body') or '').splitlines())} lines)")
    # level widths by height above the leaves, on named deps restricted to reachable nodes
    h = {}

    def height(x, path=()):
        if x in h:
            return h[x]
        ch = [c for c in declared.get(x, []) if c in aux and c not in path]
        h[x] = 0 if not ch else 1 + max(height(c, path + (x,)) for c in ch)
        return h[x]

    for x in aux | {"root"}:
        height(x)
    w = Counter(h[x] for x in aux | {"root"})
    print(" nodes by height above the leaves:", [w[i] for i in range(max(w) + 1)])
    dr = [n for n in nodes if n.get("status") == "dropped"]
    for n in dr:
        print("  dropped:", n["id"], "| deps", n.get("deps"), "| in", n.get("t_in"), "out", n.get("t_out"), "|", (n.get("claim") or "")[:150])
    print(" node 'reason' sample:", (proved[3].get("reason") or "")[:260])
    print(" node 'lessons' sample:", (proved[3].get("lessons") or [""])[0][:260] if proved[3].get("lessons") else None)
