"""Measure the Lean graph of feature_graph.py against dependency data that the Lean compiler produced.

  py.sh features/feature_gold.py --nodes METRICS_CSV --edges EDGES_CSV --src MATHLIB_ROOT [--step N] [--out FILE]
                        [--examples K]

The gold data is the public dataset MathlibGraph (Apache 2.0): Mathlib at one commit, with one row
for each dependency of each declaration, made with the tool `lean-training-data`.

  METRICS_CSV   v2/declaration/metrics.csv   columns used: name, kind, file_module
  EDGES_CSV     mathlib_edges.csv            columns: source, target, is_explicit, is_simplifier
  MATHLIB_ROOT  the checkout of Mathlib at the same commit (the directory that holds `Mathlib/`)

An edge `source -> target` says that the checked proof or statement of `source` contains the
constant `target`. `is_explicit` says that the user wrote the constant in the source text; the
other edges come from the elaborator (instances, coercions, numerals, what a tactic found).

What is compared. For each sampled file the tool builds the same graph as for a library entry
that copies exactly that one file: the declaration table, then one edge for each name that the
text of a declaration mentions and that the resolver matches to a declaration of the file. Gold
edges are kept when source and target are in that file. Gold names are mapped to rows of the
table: a constructor or a field maps to the row of its type, an auxiliary constant
(`foo._proof_1`, `foo.match_1`, `foo.eq_1`) maps to the row of `foo`, a private name loses its
`_private.<module>.0.` prefix.

  precision          of the edges the lexer gives, the share that the compiler also has
  recall, explicit   of the compiler's explicit edges, the share that the lexer gives
  recall, all        the same for all compiler edges inside the file

A missed explicit edge is put in one of two classes: the last part of the target's name is a
token in the text of the source declaration ("name in the text": the resolver could have found
it), or it is not ("no token": notation, anonymous constructor, a name made by an attribute).

Standard library only. No network, no clock, no randomness: `--step N` takes every N-th module in
name order. The gold files are large and are not in the repository; library/features/gold-lean.md
says where they come from and gives their hashes.
"""
from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import feature_graph as FG  # noqa: E402
import feature_graph_lex as X  # noqa: E402

GOLD_VERSION = "feature_gold 1.0.0"
PRIVATE = re.compile(r"^_private\.(?:.+?)\.0\.")
AUX_NUM = re.compile(r"^(?:_?proof|match|eq|_simp|_sunfold|_unary|_mutual|_unsafe_rec|_lambda|_closed|_spec|_cstage\d|_rarg|"
                     r"_boxed|_elam|_redArg|_auxLemma|_nativeDecide|_impl|_neutral|_lam|_jp|_f)(?:_\d+)*$")
AUX_NAMES = frozenset("""rec recOn casesOn noConfusion noConfusionType below brecOn binductionOn ibelow injEq inj
    sizeOf_spec eq_def eq_unfold congr_simp ctorIdx toCtorIdx ofNat ext_iff ext mk induct induct_unfolding
    fun_cases fun_cases_unfolding elim ctorElim ctorElimType noConfusion_eq hcongr_simp mk_inj mkSizeOf
    """.split())
USER_KINDS = frozenset(("theorem", "definition", "abbrev", "inductive", "opaque", "axiom"))


def norm_private(name: str) -> str:
    return PRIVATE.sub("", name)


def is_aux(comp: str) -> bool:
    return comp.startswith("_") or bool(AUX_NUM.match(comp)) or comp in AUX_NAMES


def share(a: int, b: int):
    return round(a / b, 4) if b else None


def quantiles(xs: list):
    xs = sorted(xs)
    if not xs:
        return None
    q = lambda p: xs[min(len(xs) - 1, int(round(p * (len(xs) - 1))))]
    return {"n": len(xs), "min": xs[0], "q1": q(.25), "median": q(.5), "q3": q(.75), "max": xs[-1]}


def load_nodes(path: Path):
    file_of, kind, by_file = {}, {}, {}
    with open(path, encoding="utf-8", newline="") as fh:
        for r in csv.DictReader(fh):
            fm = r.get("file_module") or ""
            kind[r["name"]] = r["kind"]
            if fm:
                file_of[r["name"]] = fm
                by_file.setdefault(fm, []).append(r["name"])
    return file_of, kind, by_file


def folded_file(name: str, file_of: dict, cache: dict):
    """The file of NAME; an auxiliary constant (`foo._proof_1`, `foo.match_1`) that the node table
    does not list gets the file of the declaration it belongs to."""
    f = file_of.get(name)
    if f is not None:
        return f
    if name in cache:
        return cache[name]
    comps = norm_private(name).split(".")
    f = None
    while len(comps) > 1 and is_aux(comps[-1]):
        comps = comps[:-1]
        f = file_of.get(".".join(comps))
        if f is not None:
            break
    cache[name] = f
    return f


def load_edges(path: Path, file_of: dict, sample: set):
    """Edges whose source is in a sampled file. Returns the edges inside one file and counts of the others."""
    intra = {}
    where = Counter()
    cache = {}
    with open(path, encoding="utf-8", newline="") as fh:
        rd = csv.reader(fh)
        head = next(rd)
        i_s, i_t, i_e = head.index("source"), head.index("target"), head.index("is_explicit")
        for row in rd:
            fs = folded_file(row[i_s], file_of, cache)
            if fs not in sample:
                continue
            exp = row[i_e] == "True"
            ft = folded_file(row[i_t], file_of, cache)
            place = "same file" if ft == fs else ("other Mathlib file" if ft else "outside Mathlib or no file known")
            where[("explicit" if exp else "not explicit", place)] += 1
            if ft == fs:
                intra.setdefault(fs, []).append((row[i_s], row[i_t], exp))
    return intra, where


class Run:
    def __init__(self, examples: int):
        self.k = examples
        self.c = Counter()
        self.level = Counter()
        self.level_ok = Counter()
        self.level_ok_exp = Counter()
        self.src, self.src_ok, self.src_gold, self.src_gold_ok = Counter(), Counter(), Counter(), Counter()
        self.unmatched_last = Counter()
        self.no_row_examples = {"name is in the file": [], "name is not in the file": []}
        self.miss_examples = {"name in the text": [], "no token": []}
        self.wrong_examples = {}
        self.per_file_recall, self.per_file_precision = [], []
        self.failed = []

    def one_file(self, module: str, path: Path, gold_names: list, kind: dict, intra: list):
        raw = path.read_bytes()
        try:
            t, _ = FG.table_for(raw, "lean")
            R = X.Resolver([(path.name, t)])
            E, _notes = FG.full_graph(R)
        except Exception as exc:  # noqa: BLE001  a failure of the lexer is a result, not a crash of the run
            self.failed.append((module, type(exc).__name__))
            return
        c = self.c
        c["files"] += 1
        c["lines"] += t["n_lines"]
        items = [it[1] for it in R.items]
        name2row = {}
        for g, d in enumerate(items):
            if d["dup"] or "aborted" in d["flags"]:
                continue
            if d["name"]:
                name2row.setdefault(d["name"], g)
            for nm in d["provides"]:
                name2row.setdefault(".".join(d["scope"] + [nm]), g)

        def row_of(name: str):
            n = norm_private(name)
            g = name2row.get(n)
            if g is not None:
                return g, "direct"
            comps = n.split(".")
            while len(comps) > 1 and is_aux(comps[-1]):
                comps = comps[:-1]
                g = name2row.get(".".join(comps))
                if g is not None:
                    return g, "folded"
            return None, None

        gold_row, rows_hit = {}, set()
        file_parts = None
        for n in gold_names:
            g, how = row_of(n)
            last = norm_private(n).split(".")[-1]
            user = kind.get(n) in USER_KINDS and not is_aux(last) and not last.startswith("inst")
            if user:
                c["gold declarations that a user wrote (by name pattern)"] += 1
            if g is None:
                if user:
                    c["  of these with no row"] += 1
                    self.unmatched_last[kind.get(n, "?")] += 1
                    if file_parts is None:
                        file_parts = {x for tok, _o, _h in X.range_tokens(t, 0, len(t["masked"]))
                                      for x in tok.lstrip(".").split(".")}
                    cls = "name is in the file" if last in file_parts else "name is not in the file"
                    c["  no row: " + cls] += 1
                    if len(self.no_row_examples[cls]) < self.k:
                        self.no_row_examples[cls].append([module, n])
                continue
            gold_row[n] = g
            rows_hit.add(g)
            if user and how == "direct":
                c["  of these with a row of the same name"] += 1
        named_rows = [g for g, d in enumerate(items) if d["name"] and not d["dup"]]
        c["lexer rows with a name"] += len(named_rows)
        c["  of these with a gold declaration"] += sum(1 for g in named_rows if g in rows_hit)

        def row_cached(n: str):
            if n not in gold_row:
                gold_row[n] = row_of(n)[0]      # an auxiliary constant that the node table does not list
            return gold_row[n]

        gold_all, gold_exp = set(), set()
        for s, tg, exp in intra:
            a, b = row_cached(s), row_cached(tg)
            if a is None or b is None:
                c["gold edges in the file with an end that has no row"] += 1
                continue
            if a == b:
                continue
            gold_all.add((a, b))
            if exp:
                gold_exp.add((a, b))
        lex = {}
        for (a, b), val in E.items():
            if a != b and a in rows_hit:
                lex[(a, b)] = val[4]
        ok_all = set(lex) & gold_all
        ok_exp = set(lex) & gold_exp
        c["lexer edges"] += len(lex)
        c["lexer edges that the compiler has"] += len(ok_all)
        c["lexer edges that the compiler has as explicit"] += len(ok_exp)
        c["compiler edges, explicit"] += len(gold_exp)
        c["compiler edges, all"] += len(gold_all)
        c["compiler explicit edges that the lexer gives"] += len(ok_exp)
        c["compiler edges that the lexer gives"] += len(ok_all)
        thm = {g for g, d in enumerate(items) if d["cls"] == X.THEOREM}
        for (a0, _b0) in lex:
            self.src["theorem" if a0 in thm else "other"] += 1
        for (a0, _b0) in ok_all:
            self.src_ok["theorem" if a0 in thm else "other"] += 1
        for (a0, _b0) in gold_exp:
            self.src_gold["theorem" if a0 in thm else "other"] += 1
        for (a0, _b0) in ok_exp:
            self.src_gold_ok["theorem" if a0 in thm else "other"] += 1
        for e, lv in lex.items():
            self.level[lv] += 1
            if e in gold_all:
                self.level_ok[lv] += 1
            if e in gold_exp:
                self.level_ok_exp[lv] += 1
        if gold_exp:
            self.per_file_recall.append(round(len(ok_exp) / len(gold_exp), 4))
        if lex:
            self.per_file_precision.append(round(len(ok_all) / len(lex), 4))

        # missed explicit edges: is the name in the text of the source declaration?
        toks_of = {}
        for a, b in sorted(gold_exp - set(lex)):
            if a not in toks_of:
                d = items[a]
                toks_of[a] = {x for tok, _off, _h in X.range_tokens(t, d["kw"], d["end"]) for x in tok.lstrip(".").split(".")}
            db = items[b]
            lasts = {db["name"].split(".")[-1]} | {nm.split(".")[-1] for nm in db["provides"]}
            cls = "name in the text" if lasts & toks_of[a] else "no token"
            c["missed explicit edges: " + cls] += 1
            ex = self.miss_examples[cls]
            if len(ex) < self.k:
                ex.append([module, items[a]["name"], db["name"]])
        for (a, b), lv in sorted(lex.items()):
            if (a, b) not in gold_all:
                ex = self.wrong_examples.setdefault(lv, [])
                if len(ex) < self.k:
                    ex.append([module, items[a]["name"], items[b]["name"]])

    def summary(self, where: Counter) -> dict:
        c = self.c
        out = {"version": GOLD_VERSION, "files": c["files"], "lines": c["lines"], "files_the_lexer_failed_on": self.failed}
        out["nodes"] = {
            "gold declarations that a user wrote (by name pattern)": c["gold declarations that a user wrote (by name pattern)"],
            "with a row of the same name": c["  of these with a row of the same name"],
            "with no row": c["  of these with no row"],
            "share with a row of the same name": share(c["  of these with a row of the same name"],
                                                       c["gold declarations that a user wrote (by name pattern)"]),
            "with no row, by kind": dict(self.unmatched_last.most_common()),
            "with no row, and the last part of the name is in the file": c["  no row: name is in the file"],
            "with no row, and the last part of the name is not in the file": c["  no row: name is not in the file"],
            "lexer rows with a name": c["lexer rows with a name"],
            "lexer rows with a gold declaration": c["  of these with a gold declaration"],
            "share of lexer rows with a gold declaration": share(c["  of these with a gold declaration"], c["lexer rows with a name"]),
        }
        out["edges"] = {
            "lexer edges": c["lexer edges"],
            "compiler edges inside the file, explicit": c["compiler edges, explicit"],
            "compiler edges inside the file, all": c["compiler edges, all"],
            "precision (the compiler has the edge)": share(c["lexer edges that the compiler has"], c["lexer edges"]),
            "precision against explicit edges only": share(c["lexer edges that the compiler has as explicit"], c["lexer edges"]),
            "recall of explicit edges": share(c["compiler explicit edges that the lexer gives"], c["compiler edges, explicit"]),
            "recall of all edges": share(c["compiler edges that the lexer gives"], c["compiler edges, all"]),
            "missed explicit edges, name in the text": c["missed explicit edges: name in the text"],
            "missed explicit edges, no token": c["missed explicit edges: no token"],
            "gold edges in the file with an end that has no row": c["gold edges in the file with an end that has no row"],
            "per file, recall of explicit edges": quantiles(self.per_file_recall),
            "per file, precision": quantiles(self.per_file_precision),
        }
        out["by_level"] = {lv: {"edges": n, "the compiler has the edge": self.level_ok[lv],
                                "precision": share(self.level_ok[lv], n),
                                "explicit in the compiler data": self.level_ok_exp[lv]}
                           for lv, n in sorted(self.level.items(), key=lambda kv: -kv[1])}
        out["by_class_of_the_source"] = {k: {"lexer edges": self.src[k], "precision": share(self.src_ok[k], self.src[k]),
                                             "compiler explicit edges": self.src_gold[k],
                                             "recall of explicit edges": share(self.src_gold_ok[k], self.src_gold[k])}
                                         for k in ("theorem", "other")}
        tot_exp = sum(v for (e, _), v in where.items() if e == "explicit")
        out["where_the_compiler_edges_of_these_files_go"] = {
            f"{e}, {p}": v for (e, p), v in sorted(where.items())}
        out["share_of_explicit_compiler_edges_that_stay_in_the_file"] = share(where[("explicit", "same file")], tot_exp)
        out["examples"] = {"gold declaration with no row, name is in the file": self.no_row_examples["name is in the file"],
                           "gold declaration with no row, name is not in the file": self.no_row_examples["name is not in the file"],
                           "missed, name in the text": self.miss_examples["name in the text"],
                           "missed, no token": self.miss_examples["no token"],
                           "lexer edge that the compiler does not have": self.wrong_examples}
        return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--nodes", type=Path, required=True)
    ap.add_argument("--edges", type=Path, required=True)
    ap.add_argument("--src", type=Path, required=True)
    ap.add_argument("--step", type=int, default=1, help="take every N-th module in name order (default: all)")
    ap.add_argument("--examples", type=int, default=8)
    ap.add_argument("--out", type=Path)
    a = ap.parse_args()
    file_of, kind, by_file = load_nodes(a.nodes)
    mods = sorted(m for m in by_file if m.startswith("Mathlib.") and (a.src / (m.replace(".", "/") + ".lean")).is_file())
    sample = mods[:: max(1, a.step)]
    intra, where = load_edges(a.edges, file_of, set(sample))
    run = Run(a.examples)
    for m in sample:
        run.one_file(m, a.src / (m.replace(".", "/") + ".lean"), by_file[m], kind, intra.get(m, []))
    res = run.summary(where)
    res["sample"] = {"modules with declarations and a source file": len(mods), "step": a.step, "modules read": len(sample)}
    text = json.dumps(res, ensure_ascii=False, indent=1)
    if a.out:
        a.out.write_text(text + "\n", encoding="utf-8", newline="\n")
    sys.stdout.write(text + "\n")


if __name__ == "__main__":
    main()
