"""Measures of the public Formalpedia export of Prove2Me, and the same measures for the library.

  python -I -X utf8 formalpedia_measures.py RAW_DIR [--library GRAPH_FEATURES_JSONL] [--out measures.json]

RAW_DIR holds graph-*.jsonl and index-*.jsonl of one environment of
https://github.com/prove2me/formalpedia (see README.md in this folder for the commit and the hashes).

graph-*.jsonl : one line per arrow, {"parent", "child", "via"}; via is a list out of "statement", "solution".
index-*.jsonl : one line per card: theorem_name, status (Definition, Proved, Open, Disproved), lean_lines,
                created_at, author, source, solutions [{status, proof_type, lean_lines, created_at, author}].

Terms used in the output.
  split      : a theorem with one or more accepted proofs, together with the theorem cards that its proofs import.
  fan-out    : the number of theorem cards that the proofs of one theorem import (arrows with "solution").
  height     : the longest chain of such arrows below a theorem.
  users      : the number of theorems whose proofs import a given theorem card.

The file is a pure function of its inputs: no clock, no network, no randomness; a sample is every n-th node in
name order. Authors are counted, never written out. Python 3.13 standard library only.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, deque
from datetime import datetime
from pathlib import Path


def quantiles(xs: list) -> dict | None:
    xs = sorted(xs)
    if not xs:
        return None
    q = lambda p: xs[min(len(xs) - 1, int(round(p * (len(xs) - 1))))]
    return {"n": len(xs), "min": xs[0], "q1": q(.25), "median": q(.5), "q3": q(.75), "p90": q(.9), "p99": q(.99),
            "max": xs[-1], "mean": round(sum(xs) / len(xs), 3)}


def buckets(xs: list, edges=(0, 1, 2, 3, 4, 8, 16, 32)) -> dict:
    """Counts in [e_i, e_{i+1}) with the last bucket open."""
    out = {}
    for i, lo in enumerate(edges):
        hi = edges[i + 1] if i + 1 < len(edges) else None
        label = str(lo) if hi == lo + 1 else (f"{lo}-{hi - 1}" if hi else f"{lo}+")
        out[label] = sum(1 for x in xs if x >= lo and (hi is None or x < hi))
    return out


def share(a: int, b: int) -> float | None:
    return round(a / b, 4) if b else None


def ts(s: str | None) -> float | None:
    if not s:
        return None
    try:
        return datetime.fromisoformat(s).timestamp()
    except ValueError:
        m = re.match(r"(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)(\.\d+)?(.*)", s)
        frac = (m.group(2) or ".0")[:7].ljust(7, "0")
        return datetime.fromisoformat(m.group(1) + frac + m.group(3)).timestamp()


def source_kind(src: str) -> str:
    s = (src or "").lower()
    if re.search(r"github\.com/[^/\s]+/[^/\s]+/(blob|tree)/", s):
        return "file in a code repository"
    if "arxiv" in s or "doi.org" in s or re.search(r"\b(theorem|lemma|proposition|corollary|section|chapter|p\.|pp\.)\s*\d", s):
        return "paper or book"
    if "http" in s:
        return "other web address"
    return "none or free text" if s.strip() else "empty"


def load(raw: Path):
    names, recs = [], []
    for p in sorted(raw.glob("index-*.jsonl")):
        with open(p, encoding="utf-8") as fh:
            for line in fh:
                r = json.loads(line)
                names.append(r["theorem_name"])
                recs.append(r)
    idx = {n: i for i, n in enumerate(names)}
    sol_e, stm_e, dangling, via_count = [], [], 0, Counter()
    for p in sorted(raw.glob("graph-*.jsonl")):
        with open(p, encoding="utf-8") as fh:
            for line in fh:
                e = json.loads(line)
                via = tuple(sorted(e["via"]))
                via_count["+".join(via)] += 1
                a, b = idx.get(e["parent"]), idx.get(e["child"])
                if a is None or b is None:
                    dangling += 1
                    continue
                if "solution" in via:
                    sol_e.append((a, b))
                if "statement" in via:
                    stm_e.append((a, b))
    return names, recs, sol_e, stm_e, dangling, via_count


def scc_heights(n: int, adj: list[list[int]]):
    """Iterative Tarjan; returns (component of each node, sizes, height of each node in the condensation)."""
    index = [-1] * n
    low = [0] * n
    on = [False] * n
    comp = [-1] * n
    stack, sizes, counter = [], [], 0
    for root in range(n):
        if index[root] != -1:
            continue
        work = [(root, 0)]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on[root] = True
        while work:
            v, i = work[-1]
            if i < len(adj[v]):
                work[-1] = (v, i + 1)
                w = adj[v][i]
                if index[w] == -1:
                    index[w] = low[w] = counter
                    counter += 1
                    stack.append(w)
                    on[w] = True
                    work.append((w, 0))
                elif on[w]:
                    low[v] = min(low[v], index[w])
            else:
                work.pop()
                if work:
                    u = work[-1][0]
                    low[u] = min(low[u], low[v])
                if low[v] == index[v]:
                    c = len(sizes)
                    k = 0
                    while True:
                        w = stack.pop()
                        on[w] = False
                        comp[w] = c
                        k += 1
                        if w == v:
                            break
                    sizes.append(k)
    # Tarjan numbers components in reverse topological order: a component only points to earlier ones.
    ch = [0] * len(sizes)
    members = [[] for _ in sizes]
    for v in range(n):
        members[comp[v]].append(v)
    for c in range(len(sizes)):
        best = -1
        for v in members[c]:
            for w in adj[v]:
                if comp[w] != c and ch[comp[w]] > best:
                    best = ch[comp[w]]
        ch[c] = best + 1
    return comp, sizes, [ch[comp[v]] for v in range(n)]


def cone(start: int, adj: list[list[int]], seen_stamp: list[int], stamp: int) -> int:
    dq, count = deque([start]), 0
    seen_stamp[start] = stamp
    while dq:
        v = dq.popleft()
        for w in adj[v]:
            if seen_stamp[w] != stamp:
                seen_stamp[w] = stamp
                count += 1
                dq.append(w)
    return count


def formalpedia(raw: Path) -> dict:
    names, recs, sol_e, stm_e, dangling, via_count = load(raw)
    n = len(names)
    is_def = [r["status"] == "Definition" for r in recs]
    status = Counter(r["status"] for r in recs)
    out: dict = {"cards": n, "status": dict(sorted(status.items())),
                 "arrows_by_via": dict(sorted(via_count.items())), "arrows_total": sum(via_count.values()),
                 "arrows_with_a_name_outside_the_index": dangling}

    # solutions
    sol_kind = Counter()
    n_prove = [0] * n
    has_sketch = [False] * n
    first_ok, first_lines = [None] * n, [None] * n
    authors_stmt, authors_sol, other_author = set(), set(), 0
    for i, r in enumerate(recs):
        authors_stmt.add(r.get("author"))
        for s in r["solutions"]:
            sol_kind[f"{s.get('status')} / {s.get('proof_type')}"] += 1
            authors_sol.add(s.get("author"))
            if s.get("proof_type") in ("prove", "sketch") and s.get("status") in ("ACCEPTED", "SKETCH_ACCEPTED"):
                n_prove[i] += 1
                has_sketch[i] = has_sketch[i] or s.get("status") == "SKETCH_ACCEPTED"
                t = ts(s.get("created_at"))
                if first_ok[i] is None or (t is not None and t < first_ok[i][0]):
                    first_ok[i] = (t, s.get("author"))
                    first_lines[i] = s.get("lean_lines")
        if first_ok[i] is not None and first_ok[i][1] != r.get("author"):
            other_author += 1
    thm = [i for i in range(n) if not is_def[i]]
    out["solutions_by_kind"] = dict(sorted(sol_kind.items()))
    out["solutions_total"] = sum(sol_kind.values())
    out["theorems"] = len(thm)
    out["definitions"] = n - len(thm)
    out["theorems_by_number_of_accepted_proofs"] = buckets([n_prove[i] for i in thm], (0, 1, 2, 3, 4, 8))
    out["distinct_authors_of_statements"] = len(authors_stmt)
    out["distinct_authors_of_proofs"] = len(authors_sol)
    proved_any = [i for i in thm if n_prove[i] > 0]
    out["theorems_with_an_accepted_proof"] = len(proved_any)
    out["first_proof_by_a_different_author_share"] = share(other_author, len(proved_any))
    top = Counter(r.get("author") for r in recs).most_common(5)
    out["share_of_cards_from_the_5_most_active_statement_authors"] = [share(c, n) for _, c in top]
    out["source_field_kind_theorems"] = dict(Counter(source_kind(recs[i].get("source")) for i in thm).most_common())

    # adjacency: proof arrows to theorem cards
    kids_thm = [[] for _ in range(n)]
    kids_def_sol = [0] * n
    users = [[] for _ in range(n)]
    seen = set()
    for a, b in sol_e:
        if (a, b) in seen:
            continue
        seen.add((a, b))
        if is_def[b]:
            kids_def_sol[a] += 1
        else:
            kids_thm[a].append(b)
            users[b].append(a)
    stmt_defs, stmt_thms = [0] * n, [0] * n
    for a, b in set(stm_e):
        if is_def[b]:
            stmt_defs[a] += 1
        else:
            stmt_thms[a] += 1
    out["proof_arrows_to_theorem_cards"] = sum(len(k) for k in kids_thm)
    out["proof_arrows_to_definition_cards"] = sum(kids_def_sol)
    out["self_arrows"] = sum(1 for a in range(n) if a in kids_thm[a])

    fan = [len(kids_thm[i]) for i in proved_any]
    out["fan_out_all_proved_theorems"] = {"buckets": buckets(fan), "quantiles": quantiles(fan)}
    split = [i for i in proved_any if kids_thm[i]]
    out["theorems_with_a_split"] = len(split)
    out["share_of_proved_theorems_with_a_split"] = share(len(split), len(proved_any))
    out["fan_out_of_splits"] = quantiles([len(kids_thm[i]) for i in split])

    # cycles and height
    comp, sizes, height = scc_heights(n, kids_thm)
    big = sorted((s for s in sizes if s > 1), reverse=True)
    in_cycle = {}
    for v in range(n):
        if sizes[comp[v]] > 1:
            in_cycle.setdefault(comp[v], []).append(v)
    single = [ms for ms in in_cycle.values() if all(n_prove[v] < 2 for v in ms)]
    out["cycles"] = {
        "components_with_2_or_more_cards": len(big), "cards_in_them": sum(big), "largest": big[:5],
        "status_of_the_cards_in_them": dict(sorted(Counter(recs[v]["status"] for ms in in_cycle.values() for v in ms).items())),
        "components_in_which_no_card_has_2_or_more_proofs": len(single),
        "cards_in_those": sum(len(ms) for ms in single),
        "status_of_the_cards_in_those": dict(sorted(Counter(recs[v]["status"] for ms in single for v in ms).items())),
    }
    out["height_of_splits"] = {"buckets": buckets([height[i] for i in split], (1, 2, 3, 4, 6, 9, 13, 21, 41)),
                               "quantiles": quantiles([height[i] for i in split])}

    # status of children
    open_child = sum(1 for i in split if any(recs[c]["status"] == "Open" for c in kids_thm[i]))
    out["splits_with_an_open_child"] = open_child
    out["proved_status_with_an_open_child"] = sum(
        1 for i in split if recs[i]["status"] == "Proved" and any(recs[c]["status"] == "Open" for c in kids_thm[i]))
    out["proved_status_with_an_open_child_and_one_proof"] = sum(
        1 for i in split if recs[i]["status"] == "Proved" and n_prove[i] < 2
        and any(recs[c]["status"] == "Open" for c in kids_thm[i]))
    out["theorems_with_a_sketch_accepted_proof"] = sum(1 for i in thm if has_sketch[i])
    out["status_of_theorems_with_a_sketch_accepted_proof"] = dict(sorted(Counter(recs[i]["status"] for i in thm if has_sketch[i]).items()))
    out["cards_by_month_of_creation"] = dict(sorted(Counter((r.get("created_at") or "")[:7] for r in recs).items()))
    tn = {names[i] for i in thm}
    out["theorem_names_equal_to_another_theorem_name_plus_one_leading_part"] = sum(
        1 for x in tn if "." in x and x.split(".", 1)[1] in tn)
    by_src = {}
    for kind in sorted({source_kind(recs[i].get("source")) for i in thm}):
        ids = [i for i in proved_any if source_kind(recs[i].get("source")) == kind]
        sp = [i for i in ids if kids_thm[i]]
        by_src[kind] = {
            "proved_theorems": len(ids), "share_with_a_split": share(len(sp), len(ids)),
            "fan_out_of_splits": quantiles([len(kids_thm[i]) for i in sp]),
            "height_of_splits": quantiles([height[i] for i in sp]),
            "first_proof_lines": quantiles([first_lines[i] for i in ids if isinstance(first_lines[i], int)]),
        }
    out["by_kind_of_source_field"] = by_src

    # reuse
    nu = [len(users[i]) for i in thm]
    out["users_of_a_theorem_card"] = {"buckets": buckets(nu), "quantiles": quantiles(nu)}
    used = [i for i in thm if users[i]]
    out["theorem_cards_that_a_proof_imports"] = len(used)
    out["of_these_used_by_2_or_more"] = sum(1 for i in used if len(users[i]) >= 2)
    reused_in_split = [sum(1 for c in kids_thm[i] if len(users[c]) >= 2) for i in split]
    out["splits_with_a_child_that_another_theorem_uses"] = sum(1 for x in reused_in_split if x > 0)
    out["share_of_children_that_another_theorem_uses"] = share(sum(reused_in_split), sum(len(kids_thm[i]) for i in split))
    roots = [i for i in split if not users[i]]
    out["splits_that_no_theorem_uses"] = len(roots)
    proved_never_used_no_split = sum(1 for i in proved_any if not users[i] and not kids_thm[i])
    out["proved_theorems_with_no_split_and_no_user"] = proved_never_used_no_split

    # statements and proofs
    out["statement_lines_theorems"] = quantiles([recs[i].get("lean_lines") or 0 for i in thm])
    out["definitions_that_a_statement_imports"] = quantiles([stmt_defs[i] for i in thm])
    out["theorem_cards_that_a_statement_imports"] = buckets([stmt_thms[i] for i in thm], (0, 1, 2))
    fl = [(len(kids_thm[i]), first_lines[i]) for i in proved_any if isinstance(first_lines[i], int)]
    out["first_proof_lines"] = quantiles([x for _, x in fl])
    by = {}
    for lab, lo, hi in (("0", 0, 0), ("1", 1, 1), ("2-3", 2, 3), ("4-7", 4, 7), ("8-15", 8, 15), ("16+", 16, 10 ** 9)):
        xs = [x for k, x in fl if lo <= k <= hi]
        by[lab] = quantiles(xs)
    out["first_proof_lines_by_fan_out"] = by
    nosplit = [x for k, x in fl if k == 0]
    out["first_proofs_with_no_theorem_card_child"] = len(nosplit)
    out["of_these_with_1000_or_more_lines"] = sum(1 for x in nosplit if x >= 1000)
    wait, wait_by = [], {}
    for i in proved_any:
        t0, t1 = ts(recs[i].get("created_at")), first_ok[i][0]
        if t0 is not None and t1 is not None:
            wait.append((len(kids_thm[i]), max(0.0, t1 - t0)))
    out["seconds_from_statement_to_first_proof"] = quantiles([round(x) for _, x in wait])
    for lab, lo, hi in (("0", 0, 0), ("1", 1, 1), ("2-3", 2, 3), ("4-7", 4, 7), ("8+", 8, 10 ** 9)):
        wait_by[lab] = quantiles([round(x) for k, x in wait if lo <= k <= hi])
    out["seconds_from_statement_to_first_proof_by_fan_out"] = wait_by
    out["open_theorems"] = status.get("Open", 0)
    out["open_theorems_that_a_proof_imports"] = sum(1 for i in thm if recs[i]["status"] == "Open" and users[i])

    # cones on a fixed sample: every n-th card in name order
    order = sorted(range(n), key=lambda i: names[i])
    all_users = [[] for _ in range(n)]
    all_kids = [[] for _ in range(n)]
    for a, b in set(sol_e) | set(stm_e):
        all_kids[a].append(b)
        all_users[b].append(a)
    stamp_arr = [0] * n
    step = max(1, n // 600)
    sample = order[::step]
    stamp = 0
    dep_cone, user_cone = [], []
    for v in sample:
        stamp += 1
        dep_cone.append(cone(v, all_kids, stamp_arr, stamp))
        stamp += 1
        user_cone.append(cone(v, all_users, stamp_arr, stamp))
    out["cones_on_a_sample"] = {
        "sample": f"every {step}-th card in name order", "cards_in_sample": len(sample),
        "cards_below (what a card rests on)": quantiles(dep_cone),
        "cards_above (what a change to the statement reaches)": quantiles(user_cone),
        "share_with_no_card_above": share(sum(1 for x in user_cone if x == 0), len(user_cone)),
    }
    root_cones = []
    for v in sorted(roots, key=lambda i: names[i])[:: max(1, len(roots) // 400)]:
        stamp += 1
        root_cones.append(cone(v, kids_thm, stamp_arr, stamp))
    out["theorem_cards_below_a_split_that_no_theorem_uses (sample)"] = quantiles(root_cones)
    return out


def library(path: Path) -> dict:
    rows = [json.loads(line) for line in open(path, encoding="utf-8")]
    ok = [r for r in rows if r.get("code_null_reason") is None and (r.get("graph_nodes") or 0) > 0]

    def block(rs):
        col = lambda k: [r[k] for r in rs if isinstance(r.get(k), (int, float))]
        reused = [r for r in rs if isinstance(r.get("children_reused"), int)]
        return {
            "entries": len(rs),
            "theorems_in_the_copied_files_that_the_parent_proof_names": quantiles(col("parent_body_deps_theorem")),
            "listed_children_that_the_parent_proof_names": quantiles(col("fanout_cited")),
            "height_below_the_parent_through_theorems": quantiles(col("depth_below_parent_theorems")),
            "definitions_that_the_parent_statement_names": quantiles(col("parent_stmt_deps_definition")),
            "parent_statement_lines": quantiles(col("parent_stmt_lines")),
            "parent_proof_lines": quantiles(col("parent_body_lines")),
            "entries_with_a_child_that_another_declaration_uses": sum(1 for r in reused if r["children_reused"] > 0),
            "entries_where_reuse_is_defined": len(reused),
        }

    out = {"all": block(ok)}
    for lang in sorted({r["language"] for r in ok}):
        out[lang] = block([r for r in ok if r["language"] == lang])
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("raw", type=Path)
    ap.add_argument("--library", type=Path)
    ap.add_argument("--out", type=Path)
    a = ap.parse_args()
    res = {"formalpedia": formalpedia(a.raw)}
    if a.library:
        res["library"] = library(a.library)
    text = json.dumps(res, ensure_ascii=False, indent=1)
    if a.out:
        a.out.write_text(text + "\n", encoding="utf-8", newline="\n")
    sys.stdout.write(text + "\n")


if __name__ == "__main__":
    main()
