"""Decomposition and dependency graph of each library entry, and features computed from it.

  py.sh features/feature_graph.py --all              write library/features/graphs.jsonl and graph-features.jsonl
  py.sh features/feature_graph.py ENTRY_ID           print the two records of one entry (writes nothing)
  py.sh features/feature_graph.py --check            recompute everything; exit 1 if a committed file differs
  py.sh features/feature_graph.py --self-test        run the built-in cases of the declaration finders
  py.sh features/feature_graph.py --decls ENTRY_ID   print the declaration table of the entry's copied files
  py.sh features/feature_graph.py --explain ENTRY_ID print the entry's graph in readable form
  py.sh features/feature_graph.py --report NAME      coverage | glue | shape | audit-ids | sizes  (validation tables)

Standard library only. No network, no model, no randomness, no clock. The output is a
function of the entry directories alone: records are sorted by entry id, keys are sorted,
files are UTF-8 with \\n line ends, no absolute path and no time appears in them.

Tiers. T0: read from entry.json. T1: computed from the copied source text by the lexer in
feature_graph_lex.py. Everything here is T0 or T1. A T1 edge `A uses B` says that an
identifier token in the text of A matches the declared name B under the resolver's rules.
It is a syntactic mention. It is not a dependency recorded by the prover (that would be
T2, which needs the toolchain; see library/features/graph.md).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import feature_graph_lex as X  # noqa: E402

EXTRACTOR_VERSION = "feature_graph 1.0.0 (lex " + X.LEX_VERSION + ")"
LIB = HERE.parent.parent        # library/
ENTRIES = LIB / "entries"
FEATURES = LIB / "features"
OUT_GRAPHS = FEATURES / "graphs.jsonl"
OUT_FEATURES = FEATURES / "graph-features.jsonl"
PROVER = ("lean", "rocq", "isabelle")
IDENT = re.compile(r"[^\s()\[\]{}:,⟨⟩]+")
ROLE_RANK = {"parent": 0, "child": 1, "skeleton": 2, "context": 3, "other": 4}
LEVELS = {k: i for i, k in enumerate(X.MATCH_LEVELS + ("local", "external"))}
WEAK = ("suffix", "field", "last")

for _s in (sys.stdout, sys.stderr):
    try:
        _s.reconfigure(encoding="utf-8", errors="replace", newline="\n")
    except Exception:
        pass


def entry_ids() -> list[str]:
    return sorted(p.name for p in ENTRIES.iterdir() if (p / "entry.json").is_file())


def dumps(obj) -> str:
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def input_digest(raw: bytes, e: dict) -> str:
    """SHA-256 over the bytes of entry.json (line ends normalised to \\n, so that a checkout
    with CRLF conversion gives the same digest), a newline, and the recorded SHA-256 of the
    copied files, sorted and joined by newlines."""
    h = hashlib.sha256()
    h.update(raw.replace(b"\r\n", b"\n"))
    h.update(b"\n")
    h.update("\n".join(sorted(f.get("sha256", "") for f in e.get("files") or [])).encode("utf-8"))
    return h.hexdigest()


_TABLES: dict = {}


def table_for(raw: bytes, lang: str):
    key = (hashlib.sha256(raw).hexdigest(), lang)
    t = _TABLES.get(key)
    if t is None:
        t = _TABLES[key] = X.file_table(X.normalise(raw), lang)
        t["mentions"] = {}
        t["bound"] = {}
    return t, key[0]


def is_ident(name) -> bool:
    return bool(name) and IDENT.fullmatch(name) is not None


def span(a_b) -> int:
    return a_b[1] - a_b[0] + 1


# ---------------------------------------------------------------- the graph of the copied files

def condense(n: int, adj: list[list[int]]):
    """Strongly connected components (iterative Tarjan). Components are numbered so that every
    component reachable from component c has a smaller number than c."""
    index, low, on, comp = [-1] * n, [0] * n, [False] * n, [-1] * n
    stack, counter, ncomp = [], 0, 0
    for root in range(n):
        if index[root] != -1:
            continue
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on[root] = True
        work = [(root, 0)]
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
                    while True:
                        w = stack.pop()
                        on[w] = False
                        comp[w] = ncomp
                        if w == v:
                            break
                    ncomp += 1
    return comp, ncomp


def longest_below(n: int, adj: list[list[int]]):
    """For each node the number of edges of the longest path leaving it, cycles contracted;
    and whether the node lies on a cycle."""
    comp, ncomp = condense(n, adj)
    members = [[] for _ in range(ncomp)]
    for v in range(n):
        members[comp[v]].append(v)
    depth = [0] * ncomp
    for c in range(ncomp):
        best = 0
        for v in members[c]:
            for w in adj[v]:
                if comp[w] != c and depth[comp[w]] + 1 > best:
                    best = depth[comp[w]] + 1
        depth[c] = best
    cyc = [len(members[comp[v]]) > 1 for v in range(n)]
    return [depth[comp[v]] for v in range(n)], cyc


def reach(start: list[int], adj: list[list[int]]) -> set[int]:
    seen, todo = set(start), list(start)
    while todo:
        v = todo.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                todo.append(w)
    return seen


def merge_edge(E: dict, key, n_stmt, s_off, n_body, b_off, level, via, amb):
    r = E.get(key)
    if r is None:
        E[key] = [n_stmt, s_off, n_body, b_off, level, via, amb]
        return
    r[0] += n_stmt
    r[2] += n_body
    if s_off >= 0 and (r[1] < 0 or s_off < r[1]):
        r[1] = s_off
    if b_off >= 0 and (r[3] < 0 or b_off < r[3]):
        r[3] = b_off
    if LEVELS[level] < LEVELS[r[4]] or (LEVELS[level] == LEVELS[r[4]] and (via or "") < (r[5] or "")):
        r[4], r[5] = level, via
    r[6] = max(r[6], amb)


def full_graph(R: X.Resolver):
    """Edges between all declarations of the entry's copied files."""
    E, notes = {}, {}
    for g, (fi, d, _) in enumerate(R.items):
        t = R.tables[fi][1]
        ment = t["mentions"].get(d["i"])
        if ment is None:
            ment = t["mentions"][d["i"]] = X.decl_mentions(t, d)
        note = {"recursive": False, "shadowed": 0, "tactic": 0}
        for tok in sorted(ment):
            ns, so, nb, bo, head = ment[tok]
            res, why = R.resolve(g, tok, head)
            if why == "self":
                note["recursive"] = True
            elif why in ("shadowed", "tactic"):
                note[why] += 1
            for g2, level, via, amb in res:
                merge_edge(E, (g, g2), ns, so, nb, bo, level, via, amb)
        notes[g] = note
    return E, notes


# ---------------------------------------------------------------- nodes of one entry

def name_candidates(R: X.Resolver, name: str):
    """Declarations an entry-level name may denote: (level, g, via), level 0 the full name,
    1 the declared name is longer, 2 the entry's name is longer, 3 only the last component."""
    if not is_ident(name):
        return []
    comps = tuple(name.split("."))
    if comps[0] == "_root_" and len(comps) > 1:
        comps = comps[1:]
    out = []
    for g, full, via, _ns in R.by_last.get(comps[-1], []):
        if full == comps:
            lvl = 0
        elif len(full) > len(comps) and full[-len(comps):] == comps:
            lvl = 1
        elif len(comps) > len(full) and comps[-len(full):] == full:
            lvl = 2
        else:
            lvl = 3
        out.append((lvl, g, via))
    return out


LEVEL_NAME = ("name-exact", "name-suffix", "name-prefix", "name-last")


class EntryGraph:
    def __init__(self, eid: str):
        self.eid = eid
        self.raw = (ENTRIES / eid / "entry.json").read_bytes()
        self.e = json.loads(self.raw.decode("utf-8"))
        self.lang = self.e.get("language")
        self.files = []
        self.tables = []
        self.nodes = {}          # key -> node
        self.edges = {}          # (key, key, kind) -> attrs
        self.parent_key = None
        self.child_keys = {}     # child index -> key
        self.notes = []

    # ------------------------------------------------------------ files
    def load_files(self):
        for f in sorted(self.e.get("files") or [], key=lambda f: f["path"]):
            p = ENTRIES / self.eid / "code" / Path(*f["path"].split("/"))
            flang = X.PROVER_EXT.get(Path(f["path"]).suffix)
            row = {"path": f["path"], "lang": flang, "used": False, "dialect": None, "lines": None,
                   "decls": None, "anomalies": [], "bytes_match_recorded": None}
            if p.is_file():
                raw = p.read_bytes()
                row["bytes_match_recorded"] = hashlib.sha256(raw).hexdigest() == f.get("sha256")
                if flang == self.lang and self.lang in PROVER:
                    t, _ = table_for(raw, flang)
                    row.update(used=True, dialect=t["dialect"], lines=t["n_lines"], decls=len(t["decls"]),
                               anomalies=list(t["anomalies"]))
                    self.tables.append((f["path"], t))
            else:
                row["anomalies"] = ["file-missing"]
            self.files.append(row)

    # ------------------------------------------------------------ helpers
    def fi_of(self, path):
        for i, (p, _) in enumerate(self.tables):
            if p == path:
                return i
        return None

    def overlapping(self, fi, a, b):
        return [g for g in self.by_file[fi] if self.R.items[g][1]["lines"][0] <= b and self.R.items[g][1]["lines"][1] >= a]

    def container(self, fi, a, b):
        for g in self.by_file[fi]:
            d = self.R.items[g][1]
            if d["lines"][0] <= a and d["lines"][1] >= b and not d["dup"]:
                return g
        return None

    def add_decl(self, g, role, resolution=None, site=None, child_index=None):
        key = ("decl", g)
        n = self.nodes.get(key)
        if n is None:
            fi, d, _ = self.R.items[g]
            n = self.nodes[key] = {
                "type": "decl", "roles": set(), "name": d["name"], "short": d["short"], "kind": d["kind"],
                "cls": d["cls"], "path": self.tables[fi][0], "lines": list(d["lines"]),
                "stmt_lines": list(d["stmt_lines"]), "body_lines": list(d["body_lines"]) if d["body_lines"] else None,
                "defined": True, "resolution": None, "site": None, "child_index": None, "container": None,
                "flags": list(d["flags"]), "g": g, "doc_lines": list(d["doc_lines"]) if d["doc_lines"] else None}
        n["roles"].add(role)
        if resolution and (n["resolution"] is None or role in ("parent", "child")):
            n["resolution"] = resolution
        if site and n["site"] is None:
            n["site"] = list(site)
        if child_index is not None and n["child_index"] is None:
            n["child_index"] = child_index
        return key

    def add_text(self, typ, path, a, b, name, role, resolution, child_index=None, defined=True):
        """A local step or a region: a line range named by the entry, not a declaration."""
        key = (typ, path, a, b, name or "")
        n = self.nodes.get(key)
        if n is None:
            fi = self.fi_of(path)
            cont = self.container(fi, a, b) if fi is not None else None
            n = self.nodes[key] = {
                "type": typ, "roles": set(), "name": name, "short": name, "kind": None, "cls": None,
                "path": path, "lines": [a, b], "stmt_lines": None, "body_lines": None, "defined": defined,
                "resolution": resolution, "site": [a, b], "child_index": None, "container": None, "flags": [],
                "g": None, "fi": fi, "cont_g": cont}
            if cont is not None:
                n["container"] = self.add_decl(cont, "other")
        n["roles"].add(role)
        if child_index is not None and n["child_index"] is None:
            n["child_index"] = child_index
        return key

    def add_external(self, name, role, child_index=None):
        key = ("external", name or "")
        n = self.nodes.get(key)
        if n is None:
            n = self.nodes[key] = {
                "type": "external", "roles": set(), "name": name, "short": name, "kind": None, "cls": None,
                "path": None, "lines": None, "stmt_lines": None, "body_lines": None, "defined": False,
                "resolution": "external", "site": None, "child_index": None, "container": None, "flags": [],
                "g": None}
        n["roles"].add(role)
        if child_index is not None and n["child_index"] is None:
            n["child_index"] = child_index
        return key

    def pick_named(self, name, sites):
        """Best declaration for an entry-level name, preferring one that overlaps SITES.
        Returns (g, level, overlaps, via, number of candidates at that level) or None."""
        cands = name_candidates(self.R, name)
        if not cands:
            return None
        scored = []
        for lvl, g, via in cands:
            fi, d, _ = self.R.items[g]
            ov = any(self.tables[fi][0] == s["path"] and d["lines"][0] <= s["lines"][1]
                     and d["lines"][1] >= s["lines"][0] for s in sites)
            scored.append((not ov, lvl, via is not None, d["cls"] != X.THEOREM, g, via))
        scored.sort(key=lambda x: x[:5])
        b = scored[0]
        same = sum(1 for x in scored if x[:2] == b[:2])
        return b[4], b[1], not b[0], b[5], same

    def site_node(self, s, role, child_index=None, name=None, single=False):
        """Node(s) for a site that no entry-level name resolved: the declarations it names,
        else the declarations that start inside it, else the local step or region it covers.
        With SINGLE, several declarations starting inside the site make it a region."""
        path, (a, b) = s["path"], s["lines"]
        nm = name if name is not None else s.get("name")
        fi = self.fi_of(path)
        if fi is None:
            return [self.add_text("region", path, a, b, nm, role, "site-not-in-prover-file", child_index, defined=False)]
        over = self.overlapping(fi, a, b)
        if is_ident(nm):
            cand = {g: lvl for lvl, g, via in name_candidates(self.R, nm)}
            named = [g for g in over if g in cand]
            if named:
                best = min(cand[g] for g in named)
                return [self.add_decl(g, role, LEVEL_NAME[best] + "+site", (a, b), child_index)
                        for g in named if cand[g] == best]
        inside = [g for g in over if a <= self.R.items[g][1]["line"] <= b and not self.R.items[g][1]["dup"]]
        if inside and single and len(inside) > 1:
            return [self.add_text("region", path, a, b, nm, role, "region-of-declarations", child_index)]
        if inside:
            return [self.add_decl(g, role, "site", (a, b), child_index) for g in inside]
        if self.container(fi, a, b) is not None:
            return [self.add_text("local", path, a, b, nm, role, "local", child_index)]
        return [self.add_text("region", path, a, b, nm, role, "region", child_index)]

    # ------------------------------------------------------------ build
    def build(self):
        e = self.e
        self.load_files()
        self.R = X.Resolver(self.tables)
        R = self.R
        self.by_file = [[] for _ in self.tables]
        for g, (fi, d, _) in enumerate(R.items):
            self.by_file[fi].append(g)
        self.E, self.gnotes = full_graph(R)
        sites = e.get("sites") or []
        by_role = {}
        for s in sites:
            by_role.setdefault(s.get("role"), []).append(s)

        # ---- parent
        par = e.get("parent")
        psites = by_role.get("parent", [])
        if par:
            name = par.get("name")
            pk = self.pick_named(name, psites)
            if pk and (pk[2] or not psites):
                self.parent_key = self.add_decl(pk[0], "parent", LEVEL_NAME[pk[1]] + ("+site" if pk[2] else ""),
                                                psites[0]["lines"] if psites else None)
            elif psites:
                keys = self.site_node(psites[0], "parent", name=name if is_ident(name) else None, single=True)
                keys.sort(key=lambda k: (self.nodes[k]["lines"][0], str(k)))
                for k in keys[1:]:                # the name matched several declarations in the site
                    self.nodes[k]["roles"].discard("parent")
                    self.nodes[k]["roles"].add("skeleton")
                self.parent_key = keys[0]
            elif pk:
                self.parent_key = self.add_decl(pk[0], "parent", LEVEL_NAME[pk[1]])
            else:
                self.parent_key = self.add_external(name, "parent")

        # ---- children
        csites = by_role.get("child", [])
        claimed = set()
        children = e.get("children") or []
        for i, c in enumerate(children):
            if c.get("subgoal"):
                continue
            name = c.get("name") or ""
            named = [k for k, s in enumerate(csites) if s.get("name") == name]
            ns = [csites[k] for k in named]
            pk = self.pick_named(name, ns)
            if pk and (pk[2] or not ns):
                claimed.update(named)
                self.child_keys[i] = self.add_decl(pk[0], "child", LEVEL_NAME[pk[1]] + ("+site" if pk[2] else ""),
                                                   ns[0]["lines"] if ns else None, i)
                if pk[4] > 1:
                    self.notes.append(f"child {i} has {pk[4]} candidate declarations")
            elif ns:
                claimed.update(named)
                s = ns[0]
                fi = self.fi_of(s["path"])
                a, b = s["lines"]
                if fi is not None and self.container(fi, a, b) is not None and self.binds(fi, a, b, name):
                    self.child_keys[i] = self.add_text("local", s["path"], a, b, name, "child", "local", i)
                else:                             # the site does not declare the name: it is declared elsewhere
                    k = self.add_external(name, "child", i)
                    self.nodes[k]["site"] = [a, b]
                    self.nodes[k]["path"] = s["path"]
                    self.child_keys[i] = k
            else:
                loc = self.local_binding(name)
                if loc is not None:
                    self.child_keys[i] = self.add_text("local", loc[0], loc[1], loc[1], name, "child",
                                                       "local-binding", i)
                    self.nodes[self.child_keys[i]]["flags"].append("extent-unknown")
                else:
                    self.child_keys[i] = self.add_external(name, "child", i)
        free = [k for k in range(len(csites)) if k not in claimed]
        subs = [i for i, c in enumerate(children) if c.get("subgoal")]
        for j, i in enumerate(subs):
            key = ("subgoal", i)
            n = self.nodes[key] = {
                "type": "subgoal", "roles": {"child"}, "name": children[i].get("name"), "short": None,
                "kind": None, "cls": None, "path": None, "lines": None, "stmt_lines": None, "body_lines": None,
                "defined": True, "resolution": "subgoal", "site": None, "child_index": i, "container": None,
                "flags": [], "g": None}
            if len(free) == len(subs):
                s = csites[free[j]]
                n["path"], n["lines"], n["site"] = s["path"], list(s["lines"]), list(s["lines"])
                n["resolution"] = "subgoal+site-by-order"
            self.child_keys[i] = key
        if len(free) != len(subs):
            for k in free:                         # a child site no child names
                for key in self.site_node(csites[k], "child"):
                    self.nodes[key]["flags"].append("site-without-child")

        # ---- skeleton and context sites
        for role in ("skeleton", "context"):
            for s in by_role.get(role, []):
                self.site_node(s, role)
        # a declaration that starts inside a parent site and is neither the parent nor a child
        # belongs to the glue the entry shows: role skeleton
        for s in psites:
            fi = self.fi_of(s["path"])
            if fi is None:
                continue
            a, b = s["lines"]
            for g in self.overlapping(fi, a, b):
                d = self.R.items[g][1]
                if a <= d["line"] <= b and not d["dup"] and ("decl", g) != self.parent_key \
                        and "child" not in self.nodes.get(("decl", g), {"roles": ()})["roles"]:
                    self.add_decl(g, "skeleton", "in-parent-site", (a, b))
        self.link()

    def binds(self, fi, a, b, name) -> bool:
        """Does the line range bind NAME (have, obtain, assert, ...)? True when NAME is a token
        of the range's first three lines."""
        if not is_ident(name):
            return False
        t = self.tables[fi][1]
        L = t["L"]
        lo, hi = L.start_of(a), L.end_of(min(b, a + 2), len(t["masked"]))
        last = name.split(".")[-1]
        for tok, off, _ in X.range_tokens(t, lo, hi):
            tk = tok[1:] if t["lang"] == "isabelle" else tok
            if tk.split(".")[0] == last or tk == name:
                return True
        return False

    def local_binding(self, name):
        """(path, line) of the first token NAME inside the parent declaration, when the parent
        binds NAME locally; else None."""
        if not is_ident(name) or self.parent_key is None or "." in name:
            return None
        pn = self.nodes[self.parent_key]
        if pn["type"] != "decl":
            return None
        g = pn["g"]
        fi, d, _ = self.R.items[g]
        t = self.tables[fi][1]
        f, tm, soft = self.R.bound(g)[:3]
        if name not in f and name not in soft and not (tm and name in tm):
            return None
        for tok, off, _ in X.range_tokens(t, d["kw"], d["end"]):
            tk = tok[1:] if t["lang"] == "isabelle" else tok
            if tk == name:
                return self.tables[fi][0], t["L"].line(off)
        return None

    # ------------------------------------------------------------ edges of the entry graph
    def link(self):
        R, E = self.R, self.E
        n = len(R.items)
        adj = [[] for _ in range(n)]
        radj = [[] for _ in range(n)]
        adj_thm = [[] for _ in range(n)]
        for (g, g2) in sorted(E):
            adj[g].append(g2)
            radj[g2].append(g)
            if E[(g, g2)][2] > 0 and R.items[g2][1]["cls"] == X.THEOREM:
                adj_thm[g].append(g2)
        self.adj, self.radj = adj, radj
        depth, cyc = longest_below(n, adj)
        # chains of theorems: the first step may leave any declaration, later steps leave theorems
        sub = [adj_thm[g] if R.items[g][1]["cls"] == X.THEOREM else [] for g in range(n)]
        dsub, _ = longest_below(n, sub)
        depth_thm = [max([1 + dsub[w] for w in adj_thm[g]], default=0) for g in range(n)]
        self.depth, self.depth_thm, self.cyc = depth, depth_thm, cyc

        # text nodes (local steps and regions): their own mentions
        text_keys = sorted((k for k, v in self.nodes.items() if v["type"] in ("local", "region") and v.get("fi") is not None),
                           key=lambda k: tuple(str(x) for x in k))
        local_named = [k for k in text_keys if is_ident(self.nodes[k]["name"])]
        for k in text_keys:
            v = self.nodes[k]
            t = self.tables[v["fi"]][1]
            a, b = v["lines"]
            lo, hi = t["L"].start_of(a), t["L"].end_of(b, len(t["masked"]))
            v["range"] = (lo, hi)
            src_g = v["cont_g"]
            outside = src_g is None               # the text is not inside one declaration
            if src_g is None:
                over = self.overlapping(v["fi"], a, b)
                before = [g for g in self.by_file[v["fi"]] if R.items[g][1]["lines"][1] < a]
                src_g = over[-1] if over else (before[-1] if before else None)
            if src_g is None:
                continue
            own = {R.items[g][1]["name_at"][0] for g in self.overlapping(v["fi"], a, b) if R.items[g][1]["name_at"]}
            for tok, off, head in X.range_tokens(t, lo, hi):
                if off in own:
                    continue                      # the declaring occurrence of a name inside a region
                res, _ = R.resolve(src_g, tok, head, allow_self=outside)
                for g2, level, via, amb in res:
                    if v["type"] == "local" and g2 == v["cont_g"]:
                        continue
                    k2 = self.add_decl(g2, "other")
                    merge_edge(self.edges, (k, k2, "uses"), 0, -1, 1, off, level, via, amb)

        # mentions of local steps by name, inside their container
        for k in local_named:
            v = self.nodes[k]
            if v["type"] != "local" or v["cont_g"] is None:
                continue
            cg = v["cont_g"]
            fi, d, _ = R.items[cg]
            t = self.tables[fi][1]
            nm = v["name"].split(".")[-1]
            lo, hi = v["range"]
            others = [k2 for k2 in text_keys if k2 != k and self.nodes[k2].get("cont_g") == cg]
            for tok, off, _ in X.range_tokens(t, d["kw"], d["end"]):
                tk = tok[1:] if t["lang"] == "isabelle" else tok
                if tk.startswith(".") or tk.split(".")[0] != nm or lo <= off < hi:
                    continue
                # the innermost named step that holds the mention uses the name; so does the
                # enclosing declaration, unless the mention lies inside another child's step
                # (a step that is only context or skeleton is part of the declaration's glue)
                owners = [k2 for k2 in others if self.nodes[k2]["range"][0] <= off < self.nodes[k2]["range"][1]]
                if owners:
                    owners.sort(key=lambda k2: (self.nodes[k2]["range"][1] - self.nodes[k2]["range"][0], str(k2)))
                    src = owners[0]
                    merge_edge(self.edges, (src, k, "uses"), 0, -1, 1, off, "local", None, 1)
                if not any("child" in self.nodes[k2]["roles"] for k2 in owners):
                    src = ("decl", cg)
                    sp = d["split"] if d["split"] is not None else d["end"]
                    if off < sp:
                        merge_edge(self.edges, (src, k, "uses"), 1, off, 0, -1, "local", None, 1)
                    else:
                        merge_edge(self.edges, (src, k, "uses"), 0, -1, 1, off, "local", None, 1)

        # the declarations the entry names, what they use, and what lies between them
        core = sorted(v["g"] for v in self.nodes.values() if v["type"] == "decl")
        keep = set(core)
        for g in core:
            keep.update(adj[g])
        fwd = reach(core, adj)
        bwd = reach(core, radj)
        keep.update(fwd & bwd)
        for g in sorted(keep):
            self.add_decl(g, "other")
        for (g, g2) in sorted(E):
            if g in keep and g2 in keep:
                r = E[(g, g2)]
                merge_edge(self.edges, (("decl", g), ("decl", g2), "uses"), *r)

        # names the entry gives that no copied file declares
        ext = sorted(k for k, v in self.nodes.items() if v["type"] == "external" and is_ident(v["name"]))
        if ext:
            want = [(k, tuple(self.nodes[k]["name"].split("."))) for k in ext]
            for k in sorted(self.nodes, key=lambda k: tuple(str(x) for x in k)):
                v = self.nodes[k]
                if v["type"] == "decl" and (v["roles"] - {"other"}):
                    fi, d, _ = R.items[v["g"]]
                    t = self.tables[fi][1]
                    lo, hi, sp, g = d["kw"], d["end"], (d["split"] if d["split"] is not None else d["end"]), v["g"]
                    skip = d["name_at"][0] if d["name_at"] else -1
                elif v["type"] in ("local", "region") and v.get("fi") is not None:
                    t = self.tables[v["fi"]][1]
                    (lo, hi), sp, g, skip = v["range"], -1, v["cont_g"], -1
                else:
                    continue
                bound = R.bound(g) if g is not None else (set(), set(), {})
                bset = set(bound[0]) | set(bound[1] or ())
                for tok, off, _ in X.range_tokens(t, lo, hi):
                    if off == skip:
                        continue
                    tk = tok[1:] if t["lang"] == "isabelle" else tok
                    if tk.startswith("."):
                        continue
                    tc = tuple(tk.split("."))
                    if len(tc) == 1 and tk in bset:
                        continue
                    for k2, nc in want:
                        if k2 == k:
                            continue
                        if tc == nc or (len(tc) > len(nc) and (tc[-len(nc):] == nc or tc[:len(nc)] == nc)) \
                                or (len(nc) > len(tc) and nc[-len(tc):] == tc):
                            if off < sp:
                                merge_edge(self.edges, (k, k2, "uses"), 1, off, 0, -1, "external", None, 1)
                            else:
                                merge_edge(self.edges, (k, k2, "uses"), 0, -1, 1, off, "external", None, 1)

        # structure edges: what a region holds
        for k in text_keys:
            v = self.nodes[k]
            if v["type"] != "region":
                continue
            a, b = v["lines"]
            for k2 in sorted(self.nodes, key=lambda x: tuple(str(y) for y in x)):
                v2 = self.nodes[k2]
                if k2 == k or v2["path"] != v["path"] or not v2["lines"] or v2["type"] not in ("decl", "local"):
                    continue
                start = R.items[v2["g"]][1]["line"] if v2["type"] == "decl" else v2["lines"][0]
                if a <= start <= b and v2["lines"][1] <= b and (v2["roles"] - {"other"}):
                    self.edges[(k, k2, "contains")] = None
        # structure edges: subgoals of the parent, local steps inside a node
        if self.parent_key is not None:
            for key, v in self.nodes.items():
                if v["type"] == "subgoal":
                    self.edges[(self.parent_key, key, "subgoal")] = None
        for k in text_keys:
            v = self.nodes[k]
            if v["type"] != "local":
                continue
            lo, hi = v["range"]
            holders = [k2 for k2 in text_keys if k2 != k and self.nodes[k2]["type"] == "local"
                       and self.nodes[k2].get("cont_g") == v["cont_g"]
                       and self.nodes[k2]["range"][0] <= lo and hi <= self.nodes[k2]["range"][1]
                       and self.nodes[k2]["range"] != (lo, hi)]
            if holders:
                holders.sort(key=lambda k2: (self.nodes[k2]["range"][1] - self.nodes[k2]["range"][0], str(k2)))
                self.edges[(holders[0], k, "contains")] = None
            else:
                self.edges[(("decl", v["cont_g"]), k, "contains")] = None

    # ------------------------------------------------------------ output record
    def record(self) -> dict:
        e = self.e
        rec = {"id": self.eid, "extractor_version": EXTRACTOR_VERSION, "input_digest": input_digest(self.raw, e),
               "language": self.lang, "graph_status": "ok", "files": [], "nodes": [], "edges": [], "stats": None,
               "notes": []}
        if self.lang not in PROVER:
            self.load_files()
            rec["graph_status"] = "not-prover-language"
            rec["files"] = self.files
            return rec
        self.build()
        R = self.R
        rec["files"] = self.files
        if not self.tables:
            rec["graph_status"] = "no-prover-file"
        elif not e.get("parent"):
            rec["graph_status"] = "no-parent"

        def rank(k):
            v = self.nodes[k]
            role = min(v["roles"], key=lambda r: ROLE_RANK[r])
            ci = v["child_index"] if v["child_index"] is not None else 10 ** 6
            return (ROLE_RANK[role], ci, v["path"] or "", (v["lines"] or [0])[0], v["name"] or "", v["type"],
                    str(v.get("g")))
        order = sorted(self.nodes, key=rank)
        idx = {k: i for i, k in enumerate(order)}
        users_in_graph = {}
        for k in order:
            v = self.nodes[k]
            role = min(v["roles"], key=lambda r: ROLE_RANK[r])
            if k == self.parent_key:
                role = "parent"
            out = {"n": idx[k], "type": v["type"], "role": role,
                   "roles": sorted(v["roles"] - {"other"} if len(v["roles"]) > 1 else v["roles"], key=lambda r: ROLE_RANK[r]),
                   "name": v["name"], "short": v["short"], "kind": v["kind"], "cls": v["cls"],
                   "defined": v["defined"], "path": v["path"], "lines": v["lines"], "stmt_lines": v["stmt_lines"],
                   "body_lines": v["body_lines"], "site": v["site"], "resolution": v["resolution"],
                   "child_index": v["child_index"], "child_indices": sorted(i for i, kk in self.child_keys.items() if kk == k),
                   "container": idx[v["container"]] if v["container"] is not None else None,
                   "flags": sorted(set(v["flags"])),
                   "depth": None, "depth_theorems": None, "n_desc": None, "n_users": None, "n_deps": None,
                   "recursive": None, "on_cycle": None, "scope": None, "doc_lines": v.get("doc_lines")}
            if v["type"] == "decl":
                g = v["g"]
                d = R.items[g][1]
                out.update(depth=self.depth[g], depth_theorems=self.depth_thm[g],
                           n_desc=len(reach([g], self.adj)) - 1, n_users=len({R.items[u][2] for u in self.radj[g]}),
                           n_deps=len(self.adj[g]),
                           recursive=self.gnotes[g]["recursive"], on_cycle=self.cyc[g], scope=list(d["scope"]))
            rec["nodes"].append(out)
        for (k, k2, kind) in sorted(self.edges, key=lambda x: (idx[x[0]], idx[x[1]], x[2])):
            r = self.edges[(k, k2, kind)]
            row = {"s": idx[k], "t": idx[k2], "kind": kind, "where": None, "n_stmt": None, "n_body": None,
                   "line": None, "col": None, "body_line": None, "body_col": None, "match": None, "via": None,
                   "amb": None}
            if r is not None:
                v = self.nodes[k]
                fi = R.items[v["g"]][0] if v["type"] == "decl" else v["fi"]
                L = self.tables[fi][1]["L"]
                first = min(x for x in (r[1], r[3]) if x >= 0)
                row.update(where="both" if r[0] and r[2] else ("statement" if r[0] else "body"),
                           n_stmt=r[0], n_body=r[2], line=L.line(first), col=L.col(first),
                           body_line=L.line(r[3]) if r[3] >= 0 else None, body_col=L.col(r[3]) if r[3] >= 0 else None,
                           match=r[4], via=r[5], amb=r[6])
            rec["edges"].append(row)
        pk = self.parent_key
        pn = self.nodes[pk] if pk is not None else None
        pfile = None
        if pn is not None and pn["path"] is not None:
            fi = self.fi_of(pn["path"])
            if fi is not None:
                gs = self.by_file[fi]
                pg = pn["g"] if pn["type"] == "decl" else pn.get("cont_g")
                pfile = {"decls": len(gs), "index": gs.index(pg) if pg in gs else None}
        rec["stats"] = {
            "decls_total": len(R.items), "edges_total": len(self.E),
            "parent_file": pfile,
            "edges_ambiguous": sum(1 for r in self.E.values() if r[6] > 1),
            "edges_by_match": {lv: sum(1 for r in self.E.values() if r[4] == lv) for lv in X.MATCH_LEVELS},
            "decls_by_class": {c: sum(1 for it in R.items if it[1]["cls"] == c)
                               for c in (X.THEOREM, X.DEFINITION, X.TYPE, X.INSTANCE, X.ASSUMPTION, X.OTHER)},
            "decls_anonymous": sum(1 for it in R.items if it[1]["name"] is None),
        }
        rec["notes"] = sorted(self.notes)
        return rec


# ---------------------------------------------------------------- features

def ratio(a, b):
    return None if not b else round(a / b, 6)


def features(e: dict, G: dict) -> dict:
    """Flat features of one entry from entry.json (T0) and its graph record (T1)."""
    sites = e.get("sites") or []
    children = e.get("children") or []
    shape = e.get("shape") or {}
    par = e.get("parent")
    psites = [s for s in sites if s.get("role") == "parent"]
    csites = [s for s in sites if s.get("role") == "child"]
    lang = e.get("language")
    ext = {"lean": ".lean", "rocq": ".v", "isabelle": ".thy"}.get(lang)
    F = {
        "id": e.get("id"), "extractor_version": G["extractor_version"], "input_digest": G["input_digest"],
        # ---- meta, T0
        "language": lang, "kind": e.get("kind"), "status": e.get("status"), "move": e.get("move"),
        "scale": shape.get("scale"),
        "n_files": len(e.get("files") or []),
        "n_prover_files": sum(1 for f in e.get("files") or [] if ext and f["path"].endswith(ext)),
        "n_sites": len(sites),
        "parent_statement_given": bool(par and par.get("statement")) if par is not None else None,
        # ---- decomposition, T0
        "n_children": len(children),
        "n_children_named": sum(1 for c in children if not c.get("subgoal")),
        "n_children_subgoal": sum(1 for c in children if c.get("subgoal")),
        "n_children_stmt_null": sum(1 for c in children if not c.get("subgoal") and c.get("statement") is None),
        "n_sites_child": len(csites),
        "n_sites_context": sum(1 for s in sites if s.get("role") == "context"),
        "n_sites_skeleton": sum(1 for s in sites if s.get("role") == "skeleton"),
        "site_parent_lines": span(psites[0]["lines"]) if psites else None,
        "site_child_lines": [span(s["lines"]) for s in csites],
        "shape_direct_lemmas": shape.get("direct_lemmas"), "shape_depth": shape.get("depth"),
    }
    cl = sum(F["site_child_lines"])
    F["site_glue_share"] = ratio(F["site_parent_lines"], F["site_parent_lines"] + cl) if psites and csites else None
    if psites:
        p = psites[0]
        F["site_children_same_file"] = sum(1 for s in csites if s["path"] == p["path"])
        F["site_children_before_parent"] = sum(1 for s in csites if s["path"] == p["path"] and s["lines"][1] < p["lines"][0])
        F["site_children_inside_parent"] = sum(1 for s in csites if s["path"] == p["path"]
                                               and p["lines"][0] <= s["lines"][0] and s["lines"][1] <= p["lines"][1])
    else:
        F["site_children_same_file"] = F["site_children_before_parent"] = F["site_children_inside_parent"] = None

    T1 = ["parent_node_type", "parent_resolution", "parent_kind", "parent_class", "parent_lines",
          "parent_stmt_lines", "parent_body_lines", "parent_doc_lines", "parent_stmt_deps", "parent_stmt_deps_definition",
          "parent_stmt_deps_type", "parent_stmt_dep_depth", "parent_users", "parent_deps",
          "parent_body_deps_theorem", "parent_body_deps_definition", "parent_body_deps_other",
          "parent_body_theorems_unlisted", "children_share_of_body_theorems", "parent_desc",
          "depth_below_parent", "depth_below_parent_theorems",
          "n_children_decl", "n_children_local", "n_children_external",
          "children_class_theorem", "children_class_definition", "children_class_other",
          "children_contained", "fanout_cited", "fanout_cited_with_skeleton", "fanout_cited_share", "child_cite_counts",
          "child_cite_total", "child_cite_where", "child_cite_order", "cite_order_matches_listing",
          "cite_order_matches_source", "children_in_parent_statement", "child_child_edges", "child_chain_depth",
          "child_other_users", "children_reused", "child_other_users_max",
          "children_same_file", "children_cross_file", "children_before_parent", "children_after_parent",
          "child_gap_lines", "child_gap_min", "child_gap_max",
          "child_lines", "child_body_lines", "glue_lines", "glue_share_lines", "glue_body_lines",
          "glue_share_body", "children_shared_deps", "stmt_shared_deps", "stmt_new_deps", "stmt_dep_jaccard",
          "graph_nodes", "graph_edges", "files_decls", "files_decl_edges", "parent_file_decls",
          "parent_file_index", "parent_edges_ambiguous", "parent_edges_weak", "files_anomalies"]
    for k in T1:
        F[k] = None
    F["code_null_reason"] = None
    if G["graph_status"] != "ok":
        F["code_null_reason"] = G["graph_status"]
        return F

    N, ED = G["nodes"], G["edges"]
    uses = {(x["s"], x["t"]): x for x in ED if x["kind"] == "uses"}
    out = {}
    for (s, t) in uses:
        out.setdefault(s, []).append(t)
    F["graph_nodes"], F["graph_edges"] = len(N), len(ED)
    F["files_decls"], F["files_decl_edges"] = G["stats"]["decls_total"], G["stats"]["edges_total"]
    F["files_anomalies"] = sum(len(f["anomalies"]) for f in G["files"])
    P = next((n for n in N if n["role"] == "parent"), None)
    kids = {}                                   # child index -> node
    for n in N:
        for i in n["child_indices"]:
            kids[i] = n
    named = [i for i, c in enumerate(children) if not c.get("subgoal")]
    F["n_children_decl"] = sum(1 for i in named if kids[i]["type"] == "decl")
    F["n_children_local"] = sum(1 for i in named if kids[i]["type"] == "local")
    F["n_children_external"] = sum(1 for i in named if kids[i]["type"] == "external")
    dk = [kids[i] for i in named if kids[i]["type"] == "decl"]
    F["children_class_theorem"] = sum(1 for n in dk if n["cls"] == "theorem")
    F["children_class_definition"] = sum(1 for n in dk if n["cls"] == "definition")
    F["children_class_other"] = sum(1 for n in dk if n["cls"] not in ("theorem", "definition"))
    if P is None:
        F["code_null_reason"] = "no-parent"
        return F
    F["parent_node_type"], F["parent_resolution"] = P["type"], P["resolution"]
    if P["type"] == "external" or (P["type"] == "region" and not P["defined"]):
        F["code_null_reason"] = "parent-not-in-copied-prover-files"
        return F
    p = P["n"]
    pdeps = sorted(out.get(p, []))
    if P["type"] == "decl":
        F["parent_kind"], F["parent_class"] = P["kind"], P["cls"]
        F["parent_stmt_lines"] = span(P["stmt_lines"])
        F["parent_doc_lines"] = span(P["doc_lines"]) if P["doc_lines"] else 0
        F["parent_body_lines"] = span(P["body_lines"]) if P["body_lines"] else 0
        F["parent_users"], F["parent_deps"], F["parent_desc"] = P["n_users"], P["n_deps"], P["n_desc"]
        F["depth_below_parent"], F["depth_below_parent_theorems"] = P["depth"], P["depth_theorems"]
        sd = [t for t in pdeps if N[t]["type"] == "decl" and uses[(p, t)]["n_stmt"] > 0]
        F["parent_stmt_deps"] = len(sd)
        F["parent_stmt_deps_definition"] = sum(1 for t in sd if N[t]["cls"] == "definition")
        F["parent_stmt_deps_type"] = sum(1 for t in sd if N[t]["cls"] == "type")
        F["parent_stmt_dep_depth"] = max([1 + N[t]["depth"] for t in sd], default=0)
        bd = [t for t in pdeps if N[t]["type"] == "decl" and uses[(p, t)]["n_body"] > 0]
        bt = [t for t in bd if N[t]["cls"] == "theorem"]
        F["parent_body_deps_theorem"] = len(bt)
        F["parent_body_deps_definition"] = sum(1 for t in bd if N[t]["cls"] == "definition")
        F["parent_body_deps_other"] = len(bd) - len(bt) - F["parent_body_deps_definition"]
        F["parent_body_theorems_unlisted"] = sum(1 for t in bt if N[t]["role"] == "other")
        F["children_share_of_body_theorems"] = ratio(sum(1 for t in bt if N[t]["role"] == "child"), len(bt))
        F["parent_file_decls"] = (G["stats"]["parent_file"] or {}).get("decls")
        F["parent_file_index"] = (G["stats"]["parent_file"] or {}).get("index")
    F["parent_lines"] = span(P["lines"])
    pe = [uses[(p, t)] for t in pdeps]
    F["parent_edges_ambiguous"] = sum(1 for x in pe if (x["amb"] or 1) > 1)
    F["parent_edges_weak"] = sum(1 for x in pe if x["match"] in WEAK)

    # ---- how the parent cites the children
    skel = [n["n"] for n in N if "skeleton" in n["roles"]]
    counts, where, firsts = [], [], []
    cited = cited_sk = in_stmt = 0
    for i, c in enumerate(children):
        if c.get("subgoal"):
            counts.append(None)
            where.append(None)
            continue
        k = kids[i]["n"]
        x = uses.get((p, k))
        counts.append((x["n_stmt"] + x["n_body"]) if x else 0)
        where.append(x["where"] if x else "none")
        if x:
            cited += 1
            in_stmt += 1 if x["n_stmt"] else 0
            firsts.append(((x["line"], x["col"]), i))
        if x or any((s, k) in uses for s in skel):
            cited_sk += 1
    F["fanout_cited"], F["fanout_cited_with_skeleton"] = cited, cited_sk
    holds = {x["t"] for x in ED if x["kind"] == "contains" and x["s"] == p}
    F["children_contained"] = sum(1 for i in named if kids[i]["n"] in holds)
    F["fanout_cited_share"] = ratio(cited, len(named))
    F["child_cite_counts"], F["child_cite_where"] = counts, where
    F["child_cite_total"] = sum(x for x in counts if x)
    F["children_in_parent_statement"] = in_stmt
    order = [i for _, i in sorted(firsts)]
    F["child_cite_order"] = order
    if len(order) >= 2:
        F["cite_order_matches_listing"] = order == sorted(order)
        src = [kids[i] for i in order]
        if all(n["type"] in ("decl", "local") for n in src) and len({n["path"] for n in src}) == 1:
            F["cite_order_matches_source"] = [n["lines"][0] for n in src] == sorted(n["lines"][0] for n in src)

    # ---- children among themselves
    kn = sorted({kids[i]["n"] for i in named})
    kset = set(kn)
    cc = [(s, t) for (s, t) in uses if s in kset and t in kset and s != t]
    F["child_child_edges"] = len(cc)
    cadj = {s: sorted(t for (s2, t) in cc if s2 == s) for s in kn}
    order_ix = {s: j for j, s in enumerate(kn)}
    dchain, _ = longest_below(len(kn), [[order_ix[t] for t in cadj[s]] for s in kn])
    F["child_chain_depth"] = max(dchain, default=0)

    # ---- reuse and position (declaration children only)
    pdecl = P["n"] if P["type"] == "decl" else P["container"]
    other_users, gaps = [], []
    same = cross = before = after = 0
    for i, c in enumerate(children):
        n = kids.get(i)
        if c.get("subgoal") or n is None or n["type"] != "decl":
            other_users.append(None)
            gaps.append(None)
            continue
        other_users.append(n["n_users"] - (1 if pdecl is not None and (pdecl, n["n"]) in uses else 0))
        if n["path"] == P["path"]:
            same += 1
            if n["lines"][1] < P["lines"][0]:
                before += 1
                gaps.append(P["lines"][0] - n["lines"][1] - 1)
            else:
                gaps.append(None)
                if n["lines"][0] > P["lines"][1]:
                    after += 1
        else:
            cross += 1
            gaps.append(None)
    F["child_other_users"] = other_users
    ou = [x for x in other_users if x is not None]
    F["children_reused"] = sum(1 for x in ou if x > 0) if ou else None
    F["child_other_users_max"] = max(ou) if ou else None
    F["children_same_file"], F["children_cross_file"] = same, cross
    F["children_before_parent"], F["children_after_parent"] = before, after
    F["child_gap_lines"] = gaps
    gs = [x for x in gaps if x is not None]
    F["child_gap_min"], F["child_gap_max"] = (min(gs), max(gs)) if gs else (None, None)

    # ---- glue against children, in lines
    def lines_of(n, body):
        r = n["body_lines"] if (body and n["type"] == "decl") else n["lines"]
        if body and n["type"] == "decl" and n["body_lines"] is None:
            return set()
        return {(n["path"], x) for x in range(r[0], r[1] + 1)} if r else set()
    F["child_lines"] = [span(kids[i]["lines"]) if (i in kids and kids[i]["lines"] and kids[i]["type"] in ("decl", "local"))
                        else None for i in range(len(children))]
    F["child_body_lines"] = [(span(kids[i]["body_lines"]) if kids[i]["body_lines"] else 0)
                             if (i in kids and kids[i]["type"] == "decl") else None for i in range(len(children))]
    have = [kids[i] for i in named if kids[i]["type"] in ("decl", "local")]
    if have:
        for body, a, b in ((False, "glue_lines", "glue_share_lines"), (True, "glue_body_lines", "glue_share_body")):
            CL = set()
            for n in have:
                CL |= lines_of(n, body)
            PL = lines_of(P, body)
            F[a] = len(PL - CL)
            F[b] = ratio(len(PL - CL), len(PL - CL) + len(CL))

    # ---- shared dependencies and statement overlap (declaration children)
    if dk:
        dep_count = {}
        for n in dk:
            for t in set(out.get(n["n"], [])):
                if N[t]["type"] == "decl" and t != p and t not in kset:
                    dep_count[t] = dep_count.get(t, 0) + 1
        F["children_shared_deps"] = sum(1 for v in dep_count.values() if v >= 2)
        if P["type"] == "decl":
            SP = {t for t in pdeps if N[t]["type"] == "decl" and uses[(p, t)]["n_stmt"] > 0}
            SC = set()
            for n in dk:
                SC |= {t for t in out.get(n["n"], []) if N[t]["type"] == "decl" and uses[(n["n"], t)]["n_stmt"] > 0}
            F["stmt_shared_deps"], F["stmt_new_deps"] = len(SP & SC), len(SC - SP)
            F["stmt_dep_jaccard"] = ratio(len(SP & SC), len(SP | SC))
    return F


# ---------------------------------------------------------------- driver

def compute(eid: str):
    eg = EntryGraph(eid)
    G = eg.record()
    return G, features(eg.e, G)


def compute_all(ids=None):
    graphs, feats = [], []
    for eid in ids or entry_ids():
        G, F = compute(eid)
        graphs.append(G)
        feats.append(F)
    return graphs, feats


def render(rows) -> bytes:
    return ("".join(dumps(r) + "\n" for r in rows)).encode("utf-8")


def write_all() -> None:
    graphs, feats = compute_all()
    FEATURES.mkdir(parents=True, exist_ok=True)
    for path, rows in ((OUT_GRAPHS, graphs), (OUT_FEATURES, feats)):
        data = render(rows)
        with open(path, "wb") as f:
            f.write(data)
        print(f"{path.relative_to(LIB.parent).as_posix()}  {len(rows)} records  sha256 {hashlib.sha256(data).hexdigest()}")


def check() -> int:
    graphs, feats = compute_all()
    bad = 0
    for path, rows in ((OUT_GRAPHS, graphs), (OUT_FEATURES, feats)):
        want = render(rows)
        rel = path.relative_to(LIB.parent).as_posix()
        if not path.is_file():
            print(f"MISSING {rel}")
            bad += 1
            continue
        got = path.read_bytes().replace(b"\r\n", b"\n")      # a checkout may have converted line ends
        if got != want:
            old = {json.loads(l)["id"]: l for l in got.decode("utf-8").splitlines() if l.strip()}
            new = {r["id"]: dumps(r) for r in rows}
            diff = sorted(k for k in set(old) | set(new) if old.get(k) != new.get(k))
            print(f"DIFFERS {rel}: {len(diff)} record(s), e.g. {', '.join(diff[:5])}")
            bad += 1
        else:
            print(f"ok      {rel}  sha256 {hashlib.sha256(want).hexdigest()}")
    return 1 if bad else 0


def decl_rows(eid: str):
    eg = EntryGraph(eid)
    if eg.lang not in PROVER:
        return []
    eg.load_files()
    rows = []
    for path, t in eg.tables:
        for d in t["decls"]:
            rows.append({"path": path, "name": d["name"], "short": d["short"], "kind": d["kind"], "cls": d["cls"],
                         "lines": d["lines"], "stmt_lines": d["stmt_lines"], "body_lines": d["body_lines"],
                         "doc_lines": d["doc_lines"],
                         "scope": d["scope"], "flags": d["flags"], "provides": d["provides"],
                         "shares_span": d["dup"]})
    return rows


def explain(eid: str) -> None:
    G, F = compute(eid)
    print(f"{eid}  status={G['graph_status']}  nodes={len(G['nodes'])} edges={len(G['edges'])}")
    for f in G["files"]:
        print(f"  file {f['path']} used={f['used']} decls={f['decls']} lines={f['lines']} {f['anomalies']}")
    for n in G["nodes"]:
        loc = f"{n['path']}:{n['lines'][0]}-{n['lines'][1]}" if n["lines"] else "-"
        print(f"  [{n['n']:3}] {n['role']:8} {n['type']:8} {str(n['kind']):12} {n['name']}  {loc}  "
              f"stmt={n['stmt_lines']} body={n['body_lines']} res={n['resolution']} users={n['n_users']} depth={n['depth']}")
    for x in G["edges"]:
        s, t = G["nodes"][x["s"]], G["nodes"][x["t"]]
        print(f"  {x['s']:3} -> {x['t']:3} {x['kind']:8} {str(x['where']):9} n={x['n_stmt']}+{x['n_body']} "
              f"line={x['line']} {x['match']}{'/' + x['via'] if x['via'] else ''}{' amb=' + str(x['amb']) if (x['amb'] or 1) > 1 else ''}"
              f"   {s['name']} -> {t['name']}")
    for k in sorted(F):
        print(f"  {k} = {F[k]}")


# ---------------------------------------------------------------- validation reports

def audit_ids(sample: str = "test") -> dict:
    """The fixed samples for the hand audit. Per prover language, of the n sorted ids:
    'dev'  the entries at positions floor(n * (2k + 1) / 8), k = 0..3 (read while the
           resolver was still being corrected);
    'test' the entries at positions floor(n * (4k + 1) / 16), k = 0..3 (read once, after the
           resolver was frozen; the reported precision and recall come from this sample)."""
    out = {}
    ids = entry_ids()
    for lang in PROVER:
        mine = [i for i in ids if i.startswith(lang + "-")]
        if sample == "dev":
            out[lang] = [mine[len(mine) * (2 * k + 1) // 8] for k in range(4)]
        else:
            out[lang] = [mine[len(mine) * (4 * k + 1) // 16] for k in range(4)]
    return out


def report_coverage() -> int:
    _, feats = compute_all()
    langs = ["lean", "rocq", "isabelle", "latex", "markdown", "python"]
    keys = [k for k in feats[0] if k not in ("id", "extractor_version", "input_digest", "code_null_reason")]
    n = {l: sum(1 for f in feats if f["language"] == l) for l in langs}
    print("| feature | " + " | ".join(f"{l} ({n[l]})" for l in langs) + " | all (%d) |" % len(feats))
    print("|---|" + "---|" * (len(langs) + 1))
    for k in keys:
        cells = []
        for l in langs:
            have = sum(1 for f in feats if f["language"] == l and f[k] is not None)
            cells.append("%d%%" % round(100 * have / n[l]) if n[l] else "-")
        have = sum(1 for f in feats if f[k] is not None)
        print(f"| `{k}` | " + " | ".join(cells) + " | %d%% |" % round(100 * have / len(feats)))
    return 0


def glue_rows():
    """One row per named child of a prover instance: what the library's glue check says and
    what the graph says. The glue rule is restated from validate_entry.glue_check with
    statements.cites and statements.site_text."""
    import statements as S
    rows = []
    for eid in entry_ids():
        eg = EntryGraph(eid)
        e = eg.e
        if e.get("language") not in PROVER or e.get("kind") != "instance" or not e.get("children"):
            continue
        G = eg.record()
        texts = S.load_texts(eid, e)
        gsites = [s for s in e["sites"] if s.get("role") in ("parent", "skeleton")]
        N = G["nodes"]
        P = next((x for x in N if x["role"] == "parent"), None)
        skel = [x["n"] for x in N if "skeleton" in x["roles"]]
        uses = {(x["s"], x["t"]): x for x in G["edges"] if x["kind"] == "uses"}
        kid = {}
        for x in N:
            for i in x["child_indices"]:
                kid[i] = x
        for i, c in enumerate(e["children"]):
            if c.get("subgoal"):
                continue
            name = c.get("name") or ""
            where = None
            for s in gsites:
                for k, line in enumerate(S.site_text(texts, s).splitlines()):
                    if S.cites(name, line):
                        where = (s["path"], s["lines"][0] + k)
                        break
                if where:
                    break
            k = kid[i]["n"]
            srcs = ([P["n"]] if P else []) + skel
            hits = sorted((N[s]["path"], uses[(s, k)]["line"]) for s in srcs if (s, k) in uses)
            mine = hits[0] if hits else None
            why = ""
            if where and not mine:
                fi = eg.fi_of(where[0])
                if fi is None:
                    why = "cited in a file that is not a prover file"
                else:
                    t = eg.tables[fi][1]
                    L = t["L"]
                    lo, hi = L.start_of(where[1]), L.end_of(where[1], len(t["masked"]))
                    code = t["masked"][lo:hi] + " " + (t["inner"][lo:hi] if t["inner"] else "")
                    in_parent = P and P["lines"] and P["path"] == where[0] and P["lines"][0] <= where[1] <= P["lines"][1]
                    in_skel = any(N[s]["path"] == where[0] and N[s]["lines"]
                                  and N[s]["lines"][0] <= where[1] <= N[s]["lines"][1] for s in skel)
                    kn = kid[i]
                    own = kn["lines"] and kn["path"] == where[0] and kn["lines"][0] <= where[1] <= kn["lines"][1]
                    if not S.cites(name, code):
                        why = "A: the name stands only in a comment, a string or document text"
                    elif own and kn["type"] == "local":
                        why = "B: the glue check counts the step's own binding line; no later use of the name"
                    elif own:
                        why = "C: the parent site contains the child's own declaration (contains, not uses)"
                    elif not in_parent and not in_skel:
                        why = "D: the citing line lies in the site but outside the parent declaration"
                    else:
                        why = "E: the token does not resolve to the child"
            elif mine and not where:
                why = "F: the citing line lies in the parent declaration but outside the parent and skeleton sites"
            elif where and mine and where not in hits:
                fi = eg.fi_of(where[0])
                t = eg.tables[fi][1] if fi is not None else None
                code = ""
                if t is not None:
                    lo, hi = t["L"].start_of(where[1]), t["L"].end_of(where[1], len(t["masked"]))
                    code = t["masked"][lo:hi] + " " + (t["inner"][lo:hi] if t["inner"] else "")
                kn = kid[i]
                own = kn["lines"] and kn["path"] == where[0] and kn["lines"][0] <= where[1] <= kn["lines"][1]
                if t is not None and not S.cites(name, code):
                    why = "line-A: the glue check's first line is a comment, a string or document text"
                elif own:
                    why = "line-B: the glue check's first line is the child's own declaration or binding"
                elif P and P["type"] == "decl" and P["path"] == where[0] and P["stmt_lines"][0] == where[1] \
                        and (P["name"] or "").split(".")[-1] == name.split(".")[-1]:
                    why = "line-C: the glue check's first line is the parent's header, whose own name ends with the child's name"
                elif re.search(r"(?<![\w'.])(?:have|let|set|obtain|suffices|assert|pose)\s+\(?\s*" + re.escape(name.split(".")[-1]) + r"(?![\w'.])", code):
                    why = "line-D: the glue check's first line binds a local name equal to the child's name"
                elif where[1] < mine[1]:
                    why = "line-E: an earlier line cites the name and the graph does not resolve it there"
                else:
                    why = "line-F: the graph's first line precedes the glue check's"
            rows.append({"id": eid, "status": e.get("status"), "child": name, "node": kid[i]["type"],
                         "glue": where, "graph": mine, "why": why})
    return rows


def report_glue() -> int:
    rows = glue_rows()
    total = len(rows)
    agree = sum(1 for r in rows if (r["glue"] is None) == (r["graph"] is None))
    both = [r for r in rows if r["glue"] and r["graph"]]
    print(f"named children of prover instances: {total}")
    print(f"agree on cited / not cited: {agree} ({100 * agree / total:.1f}%)")
    print(f"cited by both: {len(both)}; same first line: {sum(1 for r in both if not r['why'])}")
    print(f"cited by neither: {sum(1 for r in rows if not r['glue'] and not r['graph'])}")
    kinds = {}
    for r in rows:
        if r["why"]:
            kinds[r["why"]] = kinds.get(r["why"], 0) + 1
    for k in sorted(kinds):
        print(f"{kinds[k]:4}  {k}")
    for r in rows:
        if r["why"]:
            print("  " + " | ".join(str(r[k]) for k in ("id", "status", "child", "node", "glue", "graph", "why")))
    return 0


def report_shape() -> int:
    graphs, feats = compute_all()
    c = {"glue_eq": 0, "glue_n": 0, "child_eq": 0, "child_n": 0, "dl_eq": 0, "dl_lt": 0, "dl_gt": 0, "dl_n": 0,
         "depth_eq": 0, "depth_lt": 0, "depth_gt": 0, "depth_n": 0}
    rows = []
    for G, F in zip(graphs, feats):
        e = json.loads((ENTRIES / G["id"] / "entry.json").read_text(encoding="utf-8"))
        sh = e.get("shape") or {}
        if sh.get("scale") != "theorem" or G["graph_status"] != "ok":
            continue
        N = G["nodes"]
        P = next((x for x in N if x["role"] == "parent"), None)
        def why(node, site):
            a, b = site
            d0, d1 = node["lines"]
            doc = node["doc_lines"]
            out = []
            if a < d0:
                out.append("site starts at the doc comment" if doc and a == doc[0] else
                           ("site starts inside the doc comment" if doc and doc[0] < a <= doc[1] else
                            "site starts before the declaration"))
            elif a > d0:
                out.append("site starts after the attribute or prefix lines" if a <= node["stmt_lines"][0]
                           else "site starts inside the declaration")
            if b < d1:
                out.append("site ends inside the declaration")
            elif b > d1:
                out.append("site ends after the declaration")
            return "; ".join(out)
        if P and P["type"] == "decl":
            c["glue_n"] += 1
            if sh.get("glue_lines") == span(P["lines"]):
                c["glue_eq"] += 1
            else:
                w = why(P, P["site"]) if P["site"] else "no parent site"
                c["glue: " + w] = c.get("glue: " + w, 0) + 1
                rows.append((G["id"], "glue_lines", sh.get("glue_lines"), span(P["lines"]),
                             f"site {P['site']} declaration {P['lines']}: {w}"))
        csites = [s for s in e["sites"] if s.get("role") == "child"]
        for j, s in enumerate(csites):
            node = next((x for x in N if x["type"] == "decl" and x["site"] == s["lines"] and x["path"] == s["path"]
                         and "child" in x["roles"]), None)
            if node is None:
                continue
            c["child_n"] += 1
            if span(s["lines"]) == span(node["lines"]):
                c["child_eq"] += 1
            else:
                w = why(node, s["lines"])
                c["child: " + w] = c.get("child: " + w, 0) + 1
                rows.append((G["id"], f"child_lines[{j}]", span(s["lines"]), span(node["lines"]),
                             f"site {s['lines']} declaration {node['lines']} {node['name']}: {w}"))
        if F["parent_body_deps_theorem"] is not None and isinstance(sh.get("direct_lemmas"), int):
            c["dl_n"] += 1
            t1 = F["parent_body_deps_theorem"]
            k = "dl_eq" if t1 == sh["direct_lemmas"] else ("dl_lt" if t1 < sh["direct_lemmas"] else "dl_gt")
            c[k] += 1
            if k != "dl_eq":
                rows.append((G["id"], "direct_lemmas", sh["direct_lemmas"], t1,
                             f"fanout_cited {F['fanout_cited']} of {F['n_children_named']} named, external {F['n_children_external']}"))
        if F["depth_below_parent_theorems"] is not None and isinstance(sh.get("depth"), int):
            c["depth_n"] += 1
            t1 = F["depth_below_parent_theorems"]
            k = "depth_eq" if t1 == sh["depth"] else ("depth_lt" if t1 < sh["depth"] else "depth_gt")
            c[k] += 1
            if k != "depth_eq":
                rows.append((G["id"], "depth", sh["depth"], t1, ""))
    for k in sorted(c):
        print(f"{k} = {c[k]}")
    for r in rows:
        print("  " + " | ".join(str(x) for x in r))
    return 0


def report_sizes() -> int:
    graphs, _ = compute_all()
    ok = [g for g in graphs if g["graph_status"] == "ok"]
    for lang in PROVER:
        gs = [g for g in ok if g["language"] == lang]
        nodes = sorted(len(g["nodes"]) for g in gs)
        edges = sorted(len(g["edges"]) for g in gs)
        decls = sum(g["stats"]["decls_total"] for g in gs)
        full = sum(g["stats"]["edges_total"] for g in gs)
        by = {lv: sum(g["stats"]["edges_by_match"][lv] for g in gs) for lv in X.MATCH_LEVELS}
        print(f"{lang}: entries {len(gs)}; nodes median {nodes[len(nodes) // 2]} max {nodes[-1]}; "
              f"edges median {edges[len(edges) // 2]} max {edges[-1]}; declarations in copied files {decls}; "
              f"edges between them {full}; by match {by}; ambiguous {sum(g['stats']['edges_ambiguous'] for g in gs)}; "
              f"anomalies {sum(len(f['anomalies']) for g in gs for f in g['files'])}")
    return 0


def run_report(name: str) -> int:
    if name == "coverage":
        return report_coverage()
    if name == "glue":
        return report_glue()
    if name == "shape":
        return report_shape()
    if name == "sizes":
        return report_sizes()
    if name == "audit-ids":
        for sample in ("dev", "test"):
            for lang, ids in audit_ids(sample).items():
                for i in ids:
                    print(sample, lang, i)
        return 0
    print("unknown report; choose coverage, glue, shape, sizes or audit-ids", file=sys.stderr)
    return 2


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("entry", nargs="?", help="an entry id")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--decls", metavar="ENTRY_ID")
    ap.add_argument("--explain", metavar="ENTRY_ID")
    ap.add_argument("--report", metavar="NAME")
    a = ap.parse_args()
    if a.self_test:
        fails = X.self_test() + self_test()
        for f in fails:
            print("FAIL " + f)
        print("self-test: " + ("%d failure(s)" % len(fails) if fails else "all cases pass"))
        sys.exit(1 if fails else 0)
    if a.check:
        sys.exit(check())
    if a.decls:
        for r in decl_rows(a.decls):
            print(dumps(r))
        return
    if a.explain:
        explain(a.explain)
        return
    if a.report:
        sys.exit(run_report(a.report))
    if a.all:
        write_all()
        return
    if a.entry:
        if not (ENTRIES / a.entry / "entry.json").is_file():
            print(f"error: no entry {a.entry}", file=sys.stderr)
            sys.exit(1)
        G, F = compute(a.entry)
        print(dumps(G))
        print(dumps(F))
        return
    ap.print_help()


def self_test() -> list[str]:
    """Cases for the graph code itself (the lexer has its own)."""
    fails = []
    d, cyc = longest_below(5, [[1, 2], [2], [3], [], [4]])
    if d != [3, 2, 1, 0, 0] or cyc != [False] * 5:
        fails.append(f"longest_below chain: {d} {cyc}")
    d, cyc = longest_below(4, [[1], [2], [1, 3], []])
    if d != [2, 1, 1, 0] or cyc != [False, True, True, False]:
        fails.append(f"longest_below cycle: {d} {cyc}")
    E = {}
    merge_edge(E, "k", 1, 10, 0, -1, "scoped", None, 1)
    merge_edge(E, "k", 0, -1, 2, 30, "exact", "head", 2)
    if E["k"] != [1, 10, 2, 30, "exact", "head", 2]:
        fails.append(f"merge_edge: {E['k']}")
    return fails


if __name__ == "__main__":
    main()
