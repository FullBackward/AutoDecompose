"""Declaration finder and mention lexer for feature_graph.py.

Standard library only; imports no other library tool. Everything here is tier
T1: it reads characters and tokens of the copied source text. It never
elaborates a term, so a "mention" is an identifier token that matches a
declared name under the rules of `Resolver`, not a dependency the prover
recorded.

Per language the module provides
  * a masker that blanks comments and strings (offsets and lines unchanged),
  * a declaration finder: name, kind, class, span, statement span, body span,
    enclosing namespaces, names the declaration provides (constructors,
    fields, mutual partners), names it binds locally,
  * a tokenizer for the text of a declaration,
  * `Resolver`, which maps a token met inside a declaration to the
    declarations it may name.

Isabelle symbols `\\<name>` are opaque tokens named by their name. No symbol
table is used. The names given a meaning are: open and close (cartouche
delimiters); comment, ^marker, ^cancel (document markers); subseteq (in
`sublocale`); proof; the nine binder names in ISA_BINDERS; in and le as the
end of a binder list.
"""
from __future__ import annotations

import bisect
import re

LEX_VERSION = "1.1.0"

PROVER_EXT = {".lean": "lean", ".v": "rocq", ".thy": "isabelle"}

# declaration classes (the same six in the three languages)
THEOREM, DEFINITION, TYPE, INSTANCE, ASSUMPTION, OTHER = (
    "theorem", "definition", "type", "instance", "assumption", "other")

_NONNL = re.compile(r"[^\n]")
_WS = re.compile(r"\s*")


def _blank(s: str) -> str:
    return _NONNL.sub(" ", s)


def normalise(raw: bytes) -> str:
    """Bytes of a copied file -> text with \\n line ends (what the site line numbers count)."""
    return raw.decode("utf-8", "replace").replace("\r\n", "\n").replace("\r", "\n")


class Lines:
    """Offset -> 1-based line number."""

    def __init__(self, text: str):
        self.starts = [0]
        for m in re.finditer("\n", text):
            self.starts.append(m.end())
        self.n = len(self.starts)

    def line(self, off: int) -> int:
        return bisect.bisect_right(self.starts, off)

    def col(self, off: int) -> int:
        return off - self.starts[bisect.bisect_right(self.starts, off) - 1]

    def start_of(self, line: int) -> int:
        return self.starts[min(max(line, 1), self.n) - 1]

    def end_of(self, line: int, text_len: int) -> int:
        """Offset just past the last character of LINE (the newline excluded)."""
        return self.starts[line] - 1 if line < self.n else text_len


def _match_close(text: str, pos: int, opn: str, cls: str, limit: int | None = None) -> int:
    """Index of the bracket closing the one at POS, or -1."""
    depth, i, n = 0, pos, len(text) if limit is None else limit
    while i < n:
        c = text[i]
        if c == opn:
            depth += 1
        elif c == cls:
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def _rstrip_off(text: str, lo: int, hi: int) -> int:
    """Largest offset <= HI (and >= LO) such that text[off-1] is not white space."""
    while hi > lo and text[hi - 1] in " \t\n":
        hi -= 1
    return hi


def _decl(name, short, kind, cls, start, kw, end, scope):
    return {"name": name, "short": short, "kind": kind, "cls": cls, "start": start, "kw": kw,
            "name_at": None, "end": end, "split": None, "scope": list(scope), "flags": [],
            "provides": {}, "ns": "x", "vis_end": None, "dup": False}


# ============================================================================ Lean

_LEAN_OPEN = re.compile(r"--|/-|\"|'|«")
_LEAN_BLK = re.compile(r"/-|-/")
_LEAN_CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")


def mask_lean(text: str, docs: list | None = None) -> str:
    """Blank `--` comments, nested `/- -/` comments (doc comments included), the inside of
    string literals and character literals. `«..»` identifiers are kept. The spans of the
    doc comments `/-- .. -/` are appended to DOCS."""
    out, i, n, keep = [], 0, len(text), 0
    while i < n:
        m = _LEAN_OPEN.search(text, i)
        if not m:
            break
        s, t = m.start(), m.group()
        a = b = -1
        if t == "--":
            e = text.find("\n", s)
            a, b = s, (n if e < 0 else e)
            i = b
        elif t == "/-":
            depth, j = 1, s + 2
            while depth:
                m2 = _LEAN_BLK.search(text, j)
                if not m2:
                    j = n
                    break
                depth += 1 if m2.group() == "/-" else -1
                j = m2.end()
            a, b, i = s, j, j
            if docs is not None and text.startswith("/--", s):
                docs.append((s, j))
        elif t == '"':
            j = s + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j, n)
            a, b, i = s + 1, j, min(j + 1, n)
        elif t == "'":
            m3 = _LEAN_CHAR.match(text, s)
            prev = text[s - 1] if s else " "
            if m3 and not (prev.isalnum() or prev in "_'.!?»"):
                a, b, i = s + 1, m3.end() - 1, m3.end()
            else:
                i = s + 1
        else:
            e = text.find("»", s)
            i = e + 1 if e >= 0 else s + 1
        if a >= 0:
            out.append(text[keep:a])
            out.append(_blank(text[a:b]))
            keep = b
    out.append(text[keep:])
    return "".join(out)


_LID1 = r"(?:[^\W\dλΠΣ]|«[^»\n]*»)"
_LIDC = r"(?:[^\WλΠΣ]|'|«[^»\n]*»)"
_LNAME = re.compile(rf"{_LID1}{_LIDC}*(?:\.{_LID1}{_LIDC}*)*")
_LTOK = re.compile(rf"(?<![\w'.»]){_LID1}{_LIDC}*(?:\.{_LID1}{_LIDC}*)*")
_LDOT = re.compile(rf"(?<=[)\]}}⟩])\.({_LID1}{_LIDC}*)")
_LSIMPLE = re.compile(rf"(?<![\w'.»]){_LID1}{_LIDC}*(?![\w'.«])")

LEAN_MODS = frozenset("private protected public noncomputable unsafe partial nonrec meta scoped local".split())
LEAN_CORE = {
    "theorem": THEOREM, "lemma": THEOREM, "def": DEFINITION, "abbrev": DEFINITION,
    "abbreviation": DEFINITION, "instance": INSTANCE, "example": OTHER, "structure": TYPE,
    "class": TYPE, "inductive": TYPE, "coinductive": TYPE, "opaque": DEFINITION,
    "axiom": ASSUMPTION, "constant": ASSUMPTION,
}
LEAN_EXTRA = {"alias": OTHER, "problem": THEOREM, "determine": DEFINITION,
              "irreducible_def": DEFINITION, "proof_wanted": THEOREM}
LEAN_NO_BODY = frozenset(("structure", "class", "inductive", "coinductive", "axiom", "constant",
                          "proof_wanted", "class inductive"))
LEAN_OTHER = frozenset("""variable variables universe universes open export set_option attribute
include omit import module notation notation3 infix infixl infixr prefix postfix macro macro_rules
syntax elab elab_rules declare_syntax_cat initialize builtin_initialize run_cmd run_meta
library_note add_decl_doc assert_not_exists suppress_compilation unsuppress_compilation unseal seal
open_locale localized parameter parameters register_simp_attr register_option compile_inductive
theory precedence reserve binder_predicate unif_hint simproc simproc_decl dsimproc
blueprint_comment p2m_reactivate p2m_open p2m_export snip problem_file""".split())
LEAN_IN_PREFIX = frozenset("set_option open omit include variable attribute universe unseal seal".split())
# tactic and structural keywords: a one-component token in this list is read as a tactic, not as
# a name, when every occurrence of it in the declaration stands first on its line or right
# after `by`, `;`, `<;>`, `·`, `|`, `(`
LEAN_TACTICS = frozenset("""ext symm trans intro intros rfl exact apply refine constructor left right
use exists cases rcases obtain induction simp simpa rw rwa calc show from have let set suffices
congr gcongr funext subst trivial decide omega linarith nlinarith positivity ring field_simp
norm_num norm_cast push_cast exact_mod_cast split injection contradiction exfalso assumption
unfold delta change convert specialize generalize revert clear rename classical infer_instance
aesop tauto continuity measurability bound fun_prop grind lia first try repeat all_goals
any_goals case next conv at with then else do by fun match if in id mono abel group module
nontriviality lift choose filter_upwards refl split_ifs by_cases by_contra absurd swap rotate_left
rotate_right on_goal pick_goal done skip exacts and or not iff true false""".split())

_LEAN_LINE = re.compile(r"(?m)^[ \t]*(?=[@A-Za-z_#])")
_LEAN_WORD = re.compile(r"#?[A-Za-z_][\w']*")
_LEAN3 = re.compile(r"(?m)^[ \t]*begin[ \t]*$|:=[ \t]*begin\b")
_LEAN3_BE = re.compile(r"(?<![\w.'])(begin|match|end)(?![\w'])")
_LEAN_SPLIT = re.compile(r"[()\[\]{}⟨⟩⦃⦄]|:=|(?<![\w'.])where(?![\w'])|(?m:^[ \t]*\|(?:(?!:=)[^\n])*=>)")
_LEAN_LET = re.compile(r"\s*(?:let|letI|haveI|have)\s")
_LEAN_OPEN_CMD = re.compile(r"open\s+(?:scoped\s+)?([^\n]*)")


def _lean_prefix(masked: str, pos: int):
    """Read attributes and modifiers from POS; return (word, start, end, mods) or None."""
    p, mods, n = pos, [], len(masked)
    while True:
        p = _WS.match(masked, p).end()
        if masked.startswith("@[", p):
            q = _match_close(masked, p + 1, "[", "]", min(n, p + 4000))
            if q < 0:
                return None
            mods.append("@")
            p = q + 1
            continue
        m = _LEAN_WORD.match(masked, p)
        if not m:
            return None
        w = m.group()
        if w in LEAN_MODS:
            mods.append(w)
            p = m.end()
            continue
        return w, m.start(), m.end(), mods


def _lean_split(masked: str, a: int, b: int):
    """Offset where the statement of a Lean declaration ends and its body starts, or None."""
    depth = 0
    for m in _LEAN_SPLIT.finditer(masked, a, b):
        t = m.group()
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            depth = max(0, depth - 1)
        elif depth == 0:
            if t == ":=":
                ls = max(masked.rfind("\n", a, m.start()), masked.rfind(";", a, m.start())) + 1
                if _LEAN_LET.match(masked, max(ls, a)):
                    continue
            return m.start()
    return None


_LP_WHERE = re.compile(r"(?<![\w'.])where(?![\w'])|:=")
_LP_EXTENDS = re.compile(r"(?<![\w'.])extends(?![\w'])")
_LP_HEAD = re.compile(r"[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected)[ \t]+)*")
_LP_NAMES = re.compile(rf"\(?[ \t]*((?:{_LID1}{_LIDC}*[ \t]+)*{_LID1}{_LIDC}*)[ \t]*(::|:=|:|[({{\[⦃])")
_LP_GROUP = re.compile(rf"\([ \t]*((?:{_LID1}{_LIDC}*[ \t]+)*{_LID1}{_LIDC}*)[ \t]*:(?!=)")
_LP_ARM = re.compile(rf"\|[ \t]*(?:(?:private|protected)[ \t]+)?({_LID1}{_LIDC}*)")
_LP_ENUM = re.compile(rf"(?:[ \t]*\|[ \t]*{_LID1}{_LIDC}*)+[ \t]*$")
_LP_PARENT = re.compile(rf"\s*({_LID1}{_LIDC}*(?:\.{_LID1}{_LIDC}*)*)(?:\s+(?:[\w'.]+|\([^()]*\)|\{{[^{{}}]*\}}|\[[^\[\]]*\]))*\s*$")
_LP_STOP = frozenset("deriving instance end namespace open variable theorem lemma def section".split())


def _lean_provides(masked: str, d: dict) -> dict:
    """Names that a Lean `structure`, `class` or `inductive` brings with it, written relative to the
    namespace the declaration is in: `S.mk` (or the constructor the text names with `c ::`), `S.f`
    for each field, `S.toP` for each parent after `extends`, `T.c` for each constructor arm `| c`.
    The compiler makes one constant for each of them; without these names a use such as `x.f` or
    `T.c` has nothing to point at."""
    short = d["short"]
    if not short or short.startswith("_root_."):
        return {}
    a = d["name_at"][1] if d["name_at"] else d["kw"]
    seg = masked[a:d["end"]]
    out = {}
    if d["kind"] in ("structure", "class"):
        m = _LP_WHERE.search(seg)
        head = seg[:m.start()] if m else seg
        e = _LP_EXTENDS.search(head)
        if e:
            depth, start, stop, parts = 0, e.end(), len(head), []
            for i in range(e.end(), len(head)):
                ch = head[i]
                if ch in "([{⟨⦃":
                    depth += 1
                elif ch in ")]}⟩⦄":
                    depth -= 1
                elif ch == "," and depth == 0:
                    parts.append(head[start:i])
                    start = i + 1
                elif ch == ":" and depth == 0:               # `extends A, B : Type u`
                    stop = i
                    break
            parts.append(head[start:stop])
            for part in parts:
                pm = _LP_PARENT.match(part)                 # `A ≃ B` names no parent: no projection
                if pm:
                    out[short + ".to" + pm.group(1).split(".")[-1]] = "field"
        ctor = "mk"
        if m:
            first, _, rest = seg[m.end():].partition("\n")
            for g in _LP_GROUP.finditer(first):                  # Lean 3: `:= (a : T) (b : U)`
                for nm in g.group(1).split():
                    out[short + "." + nm] = "field"
            base = None
            for line in rest.split("\n"):
                if not line.strip():
                    continue
                indent = len(line) - len(line.lstrip(" \t"))
                if base is None:
                    base = indent
                if indent != base:
                    continue
                nm = _LP_NAMES.match(line, _LP_HEAD.match(line).end())
                if not nm:
                    continue
                names = nm.group(1).split()
                if names[0] in _LP_STOP:
                    break
                if nm.group(2) == "::":
                    ctor = names[-1]
                else:
                    for x in names:
                        out[short + "." + x] = "field"
        out[short + "." + ctor] = "constructor"
    else:
        lines = seg.split("\n")
        bar = lines[0].find("|")                              # `inductive E | a | b` on the header line
        for line in ([lines[0][bar:]] if bar >= 0 else []) + lines[1:]:
            st = line.lstrip(" \t")
            if not st.startswith("|"):
                continue
            arms = _LP_ARM.findall(st) if _LP_ENUM.match(st) else [x.group(1) for x in [_LP_ARM.match(st)] if x]
            for x in arms:
                out[short + "." + x] = "constructor"
    return out


def lean_table(text: str) -> dict:
    docs = []
    masked = mask_lean(text, docs)
    L = Lines(masked)
    n = len(masked)
    lean3 = bool(_LEAN3.search(masked))
    proof_ends = set()
    if lean3:
        depth = 0
        for m in _LEAN3_BE.finditer(masked):
            if m.group() == "end":
                if depth > 0:
                    depth -= 1
                    proof_ends.add(m.start())
            else:
                depth += 1
    decls, stack, opens, anomalies = [], [], [], []
    variables = []             # [name, offset of the command, offset where its scope ends or None, type head]
    open_vars = []             # per open scope: indices into variables
    cur = None
    cur_indent = 0
    consumed = 0
    pending = None

    def close(off):
        nonlocal cur
        if cur is not None:
            end = _rstrip_off(masked, cur["kw"], off)
            for d in reversed(decls):              # every row of the command that just ended
                if d["kw"] != cur["kw"]:
                    break
                d["end"] = end
            cur = None

    for lm in _LEAN_LINE.finditer(masked):
        pos = lm.end()
        if pos < consumed:
            continue
        indent = pos - lm.start()
        r = _lean_prefix(masked, pos)
        if r is None:
            continue
        w, ks, ke, mods = r
        shallow = cur is None or indent <= cur_indent
        if w == "class":
            m2 = _LEAN_WORD.match(masked, _WS.match(masked, ke).end())
            if m2 and m2.group() in ("inductive", "abbrev"):
                w, ke = "class " + m2.group(), m2.end()
        if w == "deriving":
            m2 = _LEAN_WORD.match(masked, _WS.match(masked, ke).end())
            if not (m2 and m2.group() == "instance"):
                continue
        kind_cls = LEAN_CORE.get(w)
        if w == "class inductive":
            kind_cls = TYPE
        elif w == "class abbrev":
            kind_cls = DEFINITION
        if kind_cls is None and shallow:
            kind_cls = LEAN_EXTRA.get(w)
        if kind_cls is not None:
            close(lm.start() if pending is None else pending)
            start = lm.start() if pending is None else pending
            pending = None
            p = _WS.match(masked, ke).end()
            names = []
            if w == "instance":
                while masked.startswith("(", p):
                    q = _match_close(masked, p, "(", ")", min(n, p + 400))
                    if q < 0 or "priority" not in masked[p:q]:
                        break
                    p = _WS.match(masked, q + 1).end()
            name_at = None
            if w == "alias":
                if masked.startswith("⟨", p):
                    q = masked.find("⟩", p)
                    names = [x for x in _LNAME.findall(masked, p, q if q > 0 else p) if x != "_"]
                else:
                    m2 = _LNAME.match(masked, p)
                    names = [m2.group()] if m2 else []
                    name_at = (m2.start(), m2.end()) if m2 else None
            elif w != "example":
                m2 = _LNAME.match(masked, p)
                if m2 and m2.group() not in ("where", "extends"):
                    names = [m2.group()]
                    name_at = (m2.start(), m2.end())
            ns = ".".join(x[1] for x in stack if x[0] == "namespace" and x[1])
            first = True
            for short in names or [None]:
                full = None
                if short is not None:
                    full = short[7:] if short.startswith("_root_.") else (ns + "." + short if ns else short)
                d = _decl(full, short, w, kind_cls, start, ks, n, [x[1] for x in stack if x[0] == "namespace" and x[1]])
                d["flags"] = sorted(set(x for x in mods if x != "@")) + (["attr"] if "@" in mods else [])
                d["name_at"] = name_at
                d["dup"] = not first
                first = False
                decls.append(d)
            cur = decls[-1]
            cur_indent = indent
            consumed = ke
            continue
        if not shallow:
            continue
        if w == "end":
            if ks in proof_ends:
                continue
            close(lm.start())
            pending = None
            m2 = _LNAME.match(masked, _WS.match(masked, ke).end()) if masked[ke:ke + 1] in (" ", "\t") else None
            nm = m2.group() if m2 and L.line(m2.start()) == L.line(ks) else ""
            if not stack:
                anomalies.append(f"end-without-scope@{L.line(ks)}")
            else:
                k = max(1, len(nm.split("."))) if nm else 1
                top = stack[-1]
                if nm and top[1] == nm:
                    stack.pop()
                elif nm and k > 1 and len(stack) >= k and ".".join(x[1] for x in stack[-k:]) == nm:
                    del stack[-k:]
                elif nm and top[1].endswith("." + nm):          # `namespace A.B` closed by `end B`, `end A`
                    stack[-1] = (top[0], top[1][:-len(nm) - 1])
                else:
                    if nm != top[1]:
                        anomalies.append(f"end-name-mismatch@{L.line(ks)}")
                    stack.pop()
                while len(open_vars) > len(stack):
                    for vi in open_vars.pop():
                        variables[vi][2] = ks
            consumed = ke
            continue
        if w in ("namespace", "section", "mutual"):
            close(lm.start())
            pending = None
            nm = ""
            if w != "mutual":
                m2 = _LNAME.match(masked, _WS.match(masked, ke).end())
                if m2 and L.line(m2.start()) == L.line(ks) and m2.group() not in LEAN_OTHER:
                    nm = m2.group()                  # Lean 3 writes `section open foo` on one line
            stack.append((w, nm))
            while len(open_vars) < len(stack):
                open_vars.append([])
            consumed = ke
            continue
        if w in LEAN_OTHER or w.startswith("#"):
            close(lm.start())
            eol = masked.find("\n", ks)
            eol = n if eol < 0 else eol
            line_text = masked[ks:eol]
            if w in ("variable", "variables", "parameter", "parameters"):
                seg = masked[ke:_layout_end(masked, ks)]
                names = []
                for m2 in _LB_GROUP.finditer(seg):
                    names += [(x, m2.group(2)) for x in m2.group(1).split()]
                while len(open_vars) < len(stack):
                    open_vars.append([])
                for x, ty in names:
                    variables.append([x, ks, None, ty])
                    if open_vars:
                        open_vars[-1].append(len(variables) - 1)
            if w == "open":
                m2 = _LEAN_OPEN_CMD.match(line_text)
                if m2:
                    for x in _LNAME.findall(re.split(r"\b(?:in|hiding|renaming)\b|\(", m2.group(1))[0]):
                        opens.append(x)
            if w.endswith("_open"):                  # a project macro `xyz_open "A B~c"`: read as `open A B`
                q = text.find('"', ks, eol)
                q2 = text.find('"', q + 1, eol) if q >= 0 else -1
                if q2 > q >= 0:
                    for part in text[q + 1:q2].split():
                        opens.append(part.split("~")[0])
            if w in LEAN_IN_PREFIX and re.search(r"(?<![\w'])in\s*$", line_text):
                if pending is None:
                    pending = lm.start()
            else:
                pending = None
            consumed = ke
            continue
    close(n)                 # a namespace or section left open at the end of a file is legal Lean
    for d in decls:
        a = d["name_at"][1] if d["name_at"] else d["kw"]
        if d["kind"] not in LEAN_NO_BODY:
            d["split"] = _lean_split(masked, a, d["end"])
        if d["kind"] == "alias":
            d["split"] = None
        if d["kind"] in ("structure", "class", "inductive", "coinductive", "class inductive") and not d["dup"]:
            d["provides"] = _lean_provides(masked, d)
    return {"lang": "lean", "dialect": "lean3" if lean3 else "lean4", "masked": masked, "inner": None,
            "L": L, "decls": decls, "opens": sorted(set(opens)), "interps": {}, "anomalies": anomalies,
            "variables": variables, "docs": docs}


def _pattern_names(s: str, simple: re.Pattern) -> list[str]:
    """Identifiers in binding position at the start of S: stops at `:=`, `=>`, `;`, a comma
    or colon outside brackets; skips a type ascription inside brackets."""
    out, depth, i, n = [], 0, 0, len(s)
    while i < n:
        c = s[i]
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            if depth == 0:
                break
            depth -= 1
        elif c == ":":
            if s.startswith(":=", i) or depth == 0:
                break
            j, d2 = i, 0                       # skip the ascription up to the closing bracket
            while j < n:
                if s[j] in "([{⟨⦃":
                    d2 += 1
                elif s[j] in ")]}⟩⦄":
                    if d2 == 0:
                        break
                    d2 -= 1
                j += 1
            i = j
            continue
        elif c in ";\n" or (c == "," and depth == 0) or s.startswith("=>", i) or s.startswith("<;>", i) \
                or s.startswith("↦", i):
            break
        else:
            m = simple.match(s, i)
            if m:
                w = m.group()
                if w in ("at", "using", "generalizing", "from", "then", "do", "in", "with", "by"):
                    break
                out.append(w)
                i = m.end()
                continue
        i += 1
    return out


_LB_GROUP = re.compile(rf"[(\[{{⦃]\s*((?:{_LID1}{_LIDC}*\s+)*{_LID1}{_LIDC}*)\s*:(?!=)"
                       rf"(?:\s*({_LID1}{_LIDC}*(?:\.{_LID1}{_LIDC}*)*))?")
_LB_BINDER = re.compile(r"(?:(?<![\w'.])(?:fun|assume)(?![\w'])|λ|∀|∃!?|∑|∏|⋃|⋂|⨆|⨅)(?=([^\n]{0,160}))")
_LB_TAC = re.compile(r"(?<![\w'.])(intro|intros|rintro|rintros|introv|ext|funext|by_contra!?|rename_i|next|"
                     r"choose|case'?|with|have|haveI|let|letI|set|suffices|obtain|replace|by_cases|wlog|"
                     r"generalize|rsuffices)(?![\w'])(?=([^\n]{0,200}))")
_LB_BARE = re.compile(rf"[{{⦃]\s*((?:{_LID1}{_LIDC}*\s+)*{_LID1}{_LIDC}*)\s*[}}⦄]")
LEAN_SOFT = frozenset(("have", "haveI", "let", "letI", "set", "suffices", "replace", "rsuffices"))
_LB_ARM = re.compile(r"(?m)^[ \t]*\|([^\n]*?)=>")
_LB_STOP = re.compile(r"∈|∉|<|≤|>|≥|≠|⊆|⊂|=(?!>)")
_HDR = re.compile(r"[()\[\]{}⟨⟩⦃⦄]|:=|:|(?<![\w'.])where(?![\w'])|\.(?=\s|$)")


def _header_end(text: str, stops: tuple) -> int:
    """Offset of the first of STOPS outside brackets: where the binders of a declaration end."""
    depth = 0
    for m in _HDR.finditer(text):
        t = m.group()
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            depth = max(0, depth - 1)
        elif depth == 0 and t in stops:
            return m.start()
    return len(text)


def _binder_groups(seg: str, group: re.Pattern) -> list[str]:
    """Names of the bracketed binder groups that open SEG one after another: `(x y : T) {z : U}`."""
    out, i, n = [], 0, len(seg)
    while True:
        i = _WS.match(seg, i).end()
        if i >= n or seg[i] not in "([{⦃":
            return out
        m = group.match(seg, i)
        if m:
            out += m.group(1).split()
        close = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}[seg[i]]
        j = _match_close(seg, i, seg[i], close)
        if j < 0:
            return out
        i = j + 1


def _layout_end(text: str, at: int) -> int:
    """End of the block that starts at offset AT in an indentation-sensitive text: the end of
    the last following line indented deeper than the column of AT (blank lines included)."""
    ls = text.rfind("\n", 0, at) + 1
    col = at - ls
    end = text.find("\n", at)
    if end < 0:
        return len(text)
    pos = end
    while pos < len(text):
        nl = text.find("\n", pos + 1)
        line = text[pos + 1:nl if nl >= 0 else len(text)]
        if line.strip():
            if len(line) - len(line.lstrip(" \t")) <= col:
                break
            end = nl if nl >= 0 else len(text)
        if nl < 0:
            break
        pos = nl
    return end


def lean_bound(text: str):
    """Names bound inside a Lean declaration: (hard, soft).

    hard: names bound for the whole declaration as far as this lexer knows. Read from the
    binder groups `(x y : T)` of the header (before the colon of the statement); the binders
    after fun/∀/∃/∑, bare or in groups; the names introduced by intro/rintro/obtain/with/
    case/by_cases; the patterns of match arms. A bracket `(e : T)` elsewhere is a type
    ascription and binds nothing. The set is flat: it has no scopes.
    soft: name -> (offset of the binding, offset where its own definition ends) for the first
    `have`/`let`/`set`/`suffices`/`replace` of each name. Such a name is local only after its
    definition: in `have foo := foo x` the second `foo` is not the local one. The definition
    ends with the last following line indented deeper than the keyword.
    types: header binder name -> first identifier of its written type, `(m : FreeMagma α)`
    gives m -> FreeMagma. Used only to choose among several candidates of a field token."""
    hard, soft, types = set(), {}, {}
    hend = _header_end(text, (":", ":=", "where"))
    for m in _LB_GROUP.finditer(text, 0, hend):
        hard.update(m.group(1).split())
        if m.group(2):
            for nm in m.group(1).split():
                types.setdefault(nm, m.group(2))
    for m in _LB_BARE.finditer(text, 0, hend):         # `{x y}`: binders written without a type
        hard.update(m.group(1).split())
    for m in _LB_BINDER.finditer(text):
        seg = m.group(1)
        hard.update(_binder_groups(seg, _LB_GROUP))
        hard.update(_pattern_names(_LB_STOP.split(seg)[0], _LSIMPLE))
    for m in _LB_TAC.finditer(text):
        names = _pattern_names(m.group(2), _LSIMPLE)
        if m.group(1) in LEAN_SOFT:
            zone = None
            for nm in names:
                if nm == "_" or nm in soft:
                    continue
                k = _LSIMPLE.search(text, m.end(1))
                while k and k.group() != nm:
                    k = _LSIMPLE.search(text, k.end())
                if k:
                    zone = _layout_end(text, m.start(1)) if zone is None else zone
                    soft[nm] = (k.start(), zone)
        else:
            hard.update(names)
    for m in _LB_ARM.finditer(text):
        hard.update(_LSIMPLE.findall(m.group(1)))
    hard.discard("_")
    for nm in hard:
        soft.pop(nm, None)
    return hard, soft, types


_LEAN_HEAD = re.compile(r"(?:^|[;·|(]|<;>|(?<![\w'.])by)[ \t]*$")


_LEAN_BY = re.compile(r"(?<![\w'.])(?:by|begin)(?![\w'])")


def lean_tokens(masked: str, a: int, b: int):
    """Yield (token, offset, tactic_head) for identifier tokens in masked[a:b]; a token that
    follows a closing bracket and a dot is yielded as '.name'."""
    for m in _LTOK.finditer(masked, a, b):
        s = m.start()
        ls = masked.rfind("\n", 0, s) + 1
        yield m.group(), s, bool(_LEAN_HEAD.search(masked[max(ls, s - 12):s])) or not masked[ls:s].strip()
    for m in _LDOT.finditer(masked, a, b):
        yield "." + m.group(1), m.start(1), False


# ============================================================================ Rocq

_ROCQ_OPEN = re.compile(r'\(\*|"')
_ROCQ_CMT = re.compile(r'\(\*|\*\)|"')


def mask_rocq(text: str, docs: list | None = None) -> str:
    """Blank nested `(* *)` comments (a string inside a comment hides `*)`, as in Rocq) and the
    inside of string literals. The spans of the coqdoc comments `(** .. *)` are appended to DOCS."""
    out, i, n, keep = [], 0, len(text), 0
    while i < n:
        m = _ROCQ_OPEN.search(text, i)
        if not m:
            break
        s = m.start()
        if m.group() == '"':
            j = text.find('"', s + 1)
            j = n if j < 0 else j
            a, b, i = s + 1, j, min(j + 1, n)
        else:
            depth, j = 1, s + 2
            while depth:
                m2 = _ROCQ_CMT.search(text, j)
                if not m2:
                    j = n
                    break
                t = m2.group()
                if t == '"':
                    k = text.find('"', m2.end())
                    j = n if k < 0 else k + 1
                    if k < 0:
                        break
                    continue
                depth += 1 if t == "(*" else -1
                j = m2.end()
            a, b, i = s, j, j
            if docs is not None and text.startswith("(**", s) and not text.startswith("(***", s):
                docs.append((s, j))
        out.append(text[keep:a])
        out.append(_blank(text[a:b]))
        keep = b
    out.append(text[keep:])
    return "".join(out)


_RID = r"[^\W\d][\w']*"
_RNAME = re.compile(rf"{_RID}(?:\.{_RID})*")
_RTOK = re.compile(rf"(?<![\w'.]){_RID}(?:\.{_RID})*")
_RSIMPLE = re.compile(rf"(?<![\w'.]){_RID}(?![\w']|\.[^\W\d])")
_RDOT = re.compile(r"\.(?=\s|$)")
_RATTR = re.compile(r"(?:#\[[^\]]*\]\s*)+")
_RWORD = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")

ROCQ_QUAL = frozenset("Local Global Polymorphic Monomorphic Cumulative NonCumulative Private Program "
                      "Time Fail Succeed".split())
ROCQ_THM = frozenset("Theorem Lemma Corollary Proposition Fact Remark Property Goal".split())
ROCQ_DEF = frozenset("Definition Example Fixpoint CoFixpoint Let Instance Function Equations".split())
ROCQ_TYP = frozenset("Inductive CoInductive Variant Record Structure Class".split())
ROCQ_ASM = frozenset("Axiom Axioms Parameter Parameters Conjecture Conjectures Hypothesis Hypotheses "
                     "Variable Variables Context".split())
ROCQ_NAMED_OTHER = frozenset("Notation Abbreviation Ltac Ltac2".split())
ROCQ_END = frozenset("Qed Defined Admitted Abort Save".split())
# a sentence starting with one of these cannot stand inside a proof
ROCQ_TOPLEVEL = (ROCQ_THM | ROCQ_DEF | ROCQ_TYP | ROCQ_ASM
                 | frozenset("Section Module End Require From".split())) - {"Let"}


def _rocq_sentences(masked: str):
    """(start, end) of each sentence; END is just past the terminating dot."""
    out, pos, n = [], 0, len(masked)
    for m in _RDOT.finditer(masked):
        i = m.start()
        if i > 0 and masked[i - 1] == "." and not (i > 1 and masked[i - 2] == "."):
            continue
        s = _WS.match(masked, pos).end()
        if s <= i:
            out.append((s, i + 1))
        pos = i + 1
    s = _WS.match(masked, pos).end()
    if s < n:
        out.append((s, n))
    return out


def _rocq_assign(masked: str, a: int, b: int):
    """Offset of the first `:=` outside brackets in masked[a:b], or None."""
    depth = 0
    for m in re.compile(r"[()\[\]{}]|:=").finditer(masked, a, b):
        t = m.group()
        if t in "([{":
            depth += 1
        elif t in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0:
            return m.start()
    return None


def _rocq_binder_names(seg: str) -> list[str]:
    """Names declared by `x y : T`, `(x : T) (y z : U)`, `{x} `{C x}`."""
    names = []
    s = seg.strip()
    if s[:1] in "({[`":
        depth, start = 0, None
        for i, c in enumerate(s):
            if c in "({[":
                depth += 1
                if depth == 1:
                    start = i + 1
            elif c in ")}]":
                depth -= 1
                if depth == 0 and start is not None:
                    grp = s[start:i]
                    if s[max(0, start - 2):start - 1] == "`":
                        head = grp.split(":")[0] if ":" in grp else ""
                    else:
                        head = re.split(r":=?", grp)[0]
                    names += _RSIMPLE.findall(head)
                    start = None
    else:
        names += _RSIMPLE.findall(s.split(":")[0])
    return [x for x in names if x != "_"]


def _rocq_provides(masked: str, a: int, b: int, kind: str, name: str | None) -> dict:
    """Constructor, field and mutual-partner names of a type or fixpoint sentence."""
    out = {}
    seg = masked[a:b]
    depth = mdepth = 0
    marks = []                                    # ('with'|'|'|':=', offset) outside brackets and matches
    for m in re.compile(r"[()\[\]{}]|:=|\||(?<![\w'.])(?:match|end|with)(?![\w'])").finditer(seg):
        t = m.group()
        if t in "([{":
            depth += 1
        elif t in ")]}":
            depth = max(0, depth - 1)
        elif t == "match":
            mdepth += 1
        elif t == "end":
            mdepth = max(0, mdepth - 1)
        elif t == "with":
            if mdepth == 0 and depth == 0:
                marks.append(("with", m.end()))
        elif depth == 0 and mdepth == 0:
            marks.append((t, m.end()))
    for t, off in marks:
        if t == "with":
            m = _RNAME.match(seg, _WS.match(seg, off).end())
            if m:
                out[m.group()] = "mutual"
    if kind in ("Inductive", "CoInductive", "Variant"):
        seen = False
        # a `|` inside a constructor's type (`#|l|`, a notation) is not a separator: when some
        # bar stands first on its line, only such bars separate constructors
        first_on_line = [(t, off) for t, off in marks if t == "|" and not seg[seg.rfind("\n", 0, off - 1) + 1:off - 1].strip()]
        if first_on_line:
            marks = [(t, off) for t, off in marks if t != "|" or (t, off) in first_on_line]
        for i, (t, off) in enumerate(marks):
            if t == ":=":
                seen = True
                p = _WS.match(seg, off).end()
                if seg[p:p + 1] != "|":
                    m = _RNAME.match(seg, p)
                    if m:
                        out.setdefault(m.group(), "constructor")
            elif t == "|" and seen:
                m = _RNAME.match(seg, _WS.match(seg, off).end())
                if m:
                    out.setdefault(m.group(), "constructor")
            elif t == "with":
                seen = False
    elif kind in ("Record", "Structure", "Class"):
        asg = [off for t, off in marks if t == ":="]
        if asg:
            p = _WS.match(seg, asg[0]).end()
            m = _RNAME.match(seg, p)
            if m:
                out.setdefault(m.group(), "constructor")
                p = _WS.match(seg, m.end()).end()
            elif name:
                out.setdefault("Build_" + name, "constructor")
            if seg[p:p + 1] == "{":
                q = _match_close(seg, p, "{", "}")
                body = seg[p + 1:q if q > 0 else len(seg)]
                d2, start = 0, 0
                parts = []
                for i, c in enumerate(body):
                    if c in "([{":
                        d2 += 1
                    elif c in ")]}":
                        d2 -= 1
                    elif c == ";" and d2 == 0:
                        parts.append(body[start:i])
                        start = i + 1
                parts.append(body[start:])
                for part in parts:
                    m = _RNAME.match(part, _WS.match(part, 0).end())
                    if m and m.group() != "_":
                        out.setdefault(m.group(), "field")
    if name:
        out.pop(name, None)
    return out


def rocq_table(text: str) -> dict:
    docs = []
    masked = mask_rocq(text, docs)
    L = Lines(masked)
    sents = _rocq_sentences(masked)
    decls, stack, opens, anomalies = [], [], [], []
    aliases = {}
    section_local = []         # per open scope: the section-local declarations made in it
    cur = None                 # declaration whose proof is open
    last = None                # most recent declaration (for obligations and a late `Proof.`)

    def module_path():
        return [x[1] for x in stack if x[0] == "Module" and x[1]]

    for s, e in sents:
        if cur is not None:
            p = s
            while p < e and masked[p] in "-+*{} \t\n":
                p += 1
            m = _RWORD.match(masked, p)
            w = m.group() if m else ""
            if w in ROCQ_END:
                cur["end"] = e
                if w == "Abort":
                    cur["flags"].append("aborted")
                cur = None
                continue
            if w == "Proof" and re.match(r"Proof\s+(?!using\b|with\b)[^\s.]", masked[p:e]):
                cur["end"] = e
                cur = None
                continue
            if w not in ROCQ_TOPLEVEL and w not in ROCQ_QUAL and not masked.startswith("#[", p):
                cur["end"] = e
                continue
            if w in ROCQ_QUAL or masked.startswith("#[", p):
                # a qualifier inside a proof ends it only when a declaration keyword follows
                tail = _RATTR.sub("", masked[p:e], 1)
                ws = tail.split()
                k = 0
                while k < len(ws) and ws[k] in ROCQ_QUAL:
                    k += 1
                if not (k < len(ws) and ws[k] in ROCQ_TOPLEVEL):
                    cur["end"] = e
                    continue
            anomalies.append(f"proof-not-closed@{L.line(cur['kw'])}")
            cur["flags"].append("unterminated")
            cur = None
        # ---- top level
        p = s
        m = _RATTR.match(masked, p)
        if m:
            p = m.end()
        quals = []
        while True:
            m = _RWORD.match(masked, p)
            if not m:
                break
            w = m.group()
            if w in ROCQ_QUAL:
                quals.append(w)
                p = _WS.match(masked, m.end()).end()
            elif w == "Timeout":
                p = _WS.match(masked, m.end()).end()
                m2 = re.compile(r"\d+\s*").match(masked, p)
                p = m2.end() if m2 else p
            elif w.startswith("HB.") and w not in ("HB.end", "HB.export", "HB.reexport", "HB.about", "HB.status"):
                quals.append(w)
                p = _WS.match(masked, m.end()).end()
            else:
                break
        if not m:
            continue
        w, ks, ke = m.group(), m.start(), m.end()
        p = _WS.match(masked, ke).end()
        if w == "Let":
            m2 = _RWORD.match(masked, p)
            if m2 and m2.group() in ("Fixpoint", "CoFixpoint"):
                p = _WS.match(masked, m2.end()).end()
        if w == "Canonical":
            m2 = _RWORD.match(masked, p)
            if m2 and m2.group() == "Structure":
                p = _WS.match(masked, m2.end()).end()
        scope = module_path()

        def full(nm):
            return ".".join(scope + [nm]) if nm else None

        def name_here(pp):
            mm = _RNAME.match(masked, pp)
            if mm and mm.group() != "_" and mm.end() <= e:
                return mm.group(), (mm.start(), mm.end())
            return None, None

        if w in ("Section", "Module"):
            if w == "Module":
                while True:
                    m2 = _RWORD.match(masked, p)
                    if m2 and m2.group() in ("Type", "Import", "Export"):
                        p = _WS.match(masked, m2.end()).end()
                    else:
                        break
                nm, _ = name_here(p)
                asg = _rocq_assign(masked, p, e)
                if asg is not None:                            # `Module M := N.` opens nothing
                    m2 = _RNAME.match(masked, _WS.match(masked, asg + 2).end())
                    if nm and m2:
                        aliases[nm] = m2.group()
                    continue
                stack.append(("Module", nm or ""))
            else:
                nm, _ = name_here(p)
                stack.append(("Section", nm or ""))
            section_local.append([])
            continue
        if w == "End" or w == "HB.end":
            if stack:
                kind_closed = stack.pop()[0]
                for x in section_local.pop():
                    if kind_closed == "Section":
                        x["vis_end"] = s          # a section variable is not visible after its section
            else:
                anomalies.append(f"end-without-scope@{L.line(ks)}")
            continue
        if w in ("Import", "Export", "Require", "From"):
            seg = masked[ks:e - 1]
            if w in ("Require", "From") and not re.search(r"\b(?:Import|Export)\b", seg):
                continue
            seg = re.split(r"\b(?:Import|Export)\b", seg, 1)[-1]
            for x in _RNAME.findall(seg):
                opens.append(x)
                opens.append(x.split(".")[-1])
            continue
        if w in ("Next", "Obligation", "Final", "Proof"):
            if w == "Proof" and re.match(r"Proof\s+(?!using\b|with\b)[^\s.]", masked[ks:e]):
                if last is not None:
                    last["end"] = e
                continue
            if last is None:
                last = _decl(None, None, "Obligation", OTHER, s, ks, e, scope)
                last["split"] = ks
                decls.append(last)
                anomalies.append(f"proof-without-declaration@{L.line(ks)}")
            elif last["split"] is None:
                last["split"] = s
            last["end"] = e
            cur = last
            continue
        cls = None
        if w in ROCQ_THM:
            cls = THEOREM
        elif w in ROCQ_DEF:
            cls = INSTANCE if w == "Instance" else DEFINITION
        elif w in ROCQ_TYP:
            cls = TYPE
        elif w in ROCQ_ASM:
            cls = ASSUMPTION
        elif w in ROCQ_NAMED_OTHER:
            cls = OTHER
        elif w in ("Canonical", "Coercion"):
            cls = INSTANCE if _rocq_assign(masked, p, e) is not None else None
        elif w == "Declare":
            m2 = _RWORD.match(masked, p)
            if m2 and m2.group() == "Instance":
                p = _WS.match(masked, m2.end()).end()
                cls, w = ASSUMPTION, "Declare Instance"
        elif w == "Add" and re.search(r"\bMorphism\b", masked[ks:e]):
            m2 = re.search(r"\bas\s+(" + _RID + r")\s*\.?$", masked[ks:e])
            d = _decl(full(m2.group(1)) if m2 else None, m2.group(1) if m2 else None, "Add Morphism",
                      THEOREM, s, ks, e, scope)
            d["split"] = e
            decls.append(d)
            cur = last = d
            continue
        elif w == "Derive" and re.search(r"\bSuchThat\b", masked[ks:e]):
            cls = THEOREM                              # `Derive x SuchThat P As H.` opens a proof
        if cls is None:
            continue
        kind = w
        if cls == ASSUMPTION and w != "Declare Instance":
            names = _rocq_binder_names(masked[p:e - 1])
            first = True
            for nm in names or [None]:
                d = _decl(full(nm), nm, kind, cls, s, ks, e, scope)
                d["dup"] = not first
                first = False
                decls.append(d)
                if section_local and kind not in ("Axiom", "Axioms", "Parameter", "Parameters", "Conjecture", "Conjectures"):
                    section_local[-1].append(d)
            last = decls[-1]
            continue
        if w == "Goal":
            nm, at = None, None
        elif w in ("Notation", "Abbreviation") and masked[p:p + 1] == '"':
            continue
        else:
            nm, at = name_here(p)
            if w == "Ltac2":
                while nm in ("mutable", "rec", "Type", "Notation", "Set", "external"):
                    if nm in ("Notation", "Type", "Set", "external"):
                        nm = None
                        break
                    nm, at = name_here(_WS.match(masked, at[1]).end())
        if w in ROCQ_NAMED_OTHER and nm is None:
            continue
        d = _decl(full(nm), nm, kind, cls, s, ks, e, scope)
        d["name_at"] = at
        d["flags"] = sorted(set(quals))
        a0 = at[1] if at else p
        asg = _rocq_assign(masked, a0, e)
        if cls == TYPE:
            d["provides"] = _rocq_provides(masked, a0, e, kind, nm)
        elif w in ("Fixpoint", "CoFixpoint", "Function", "Let"):
            d["provides"] = {k: v for k, v in _rocq_provides(masked, a0, e, kind, nm).items() if v == "mutual"}
        decls.append(d)
        last = d
        if kind in ("Let", "Notation", "Abbreviation") and section_local:
            section_local[-1].append(d)            # gone when its section closes
        if cls == THEOREM:
            d["split"] = e
            cur = d
        elif cls in (DEFINITION, INSTANCE) and kind != "Declare Instance":
            if asg is not None:
                d["split"] = asg
            else:
                d["split"] = e
                cur = d
                if kind == "Example":
                    d["cls"] = THEOREM
        elif cls == OTHER:
            d["split"] = asg
    if cur is not None:
        anomalies.append(f"proof-open-at-eof@{L.line(cur['kw'])}")
    if stack:
        anomalies.append("scope-open-at-eof:" + str(len(stack)))
    for d in decls:
        d["end"] = _rstrip_off(masked, d["kw"], d["end"])
        if d["split"] is not None and d["split"] >= d["end"]:
            d["split"] = None
    return {"lang": "rocq", "dialect": "rocq", "masked": masked, "inner": None, "L": L, "decls": decls,
            "opens": sorted(set(opens)), "interps": {}, "aliases": aliases, "anomalies": anomalies,
            "docs": docs}


_RB_GROUP = re.compile(rf"(?<![\w'])[(\[{{]\s*((?:{_RID}\s+)*{_RID})\s*:")
_RB_BINDER = re.compile(r"(?:(?<![\w'.])(?:forall|exists2?|fun)(?![\w'])|λ|∀|∃|∏|∑)(?=([^\n]{0,200}))")
_RB_BEND = re.compile(r",|=>|\.(?=\s|$)|;|:=")
_RB_NAMED = re.compile(rf"(?<![\w'.])(?:set|pose|evar|assert|enough|cut|have|suff|suffices)\s*\(\s*({_RID})\s*:")
_RB_SETPOSE = re.compile(rf"(?<![\w'.])(?:set|pose)\s+({_RID})(?![\w'.])[^:=.;\n]{{0,60}}:=")
_RB_TAC = re.compile(r"(?<![\w'.])(intros?|as|have|suff|suffices|wlog|into)(?![\w'])(?=([^\n]{0,200}))")
ROCQ_SOFT = frozenset(("as", "have", "suff", "suffices"))
_RB_ARROW = re.compile(r"=>(?=([^\n]{0,200}))")
_RB_STOP = re.compile(r"\.(?=\s|$)|;|,|:=|=>|\bin\b|\busing\b|\bby\b|\beqn\b|\bwith\b")
_RB_BARE = re.compile(rf"(?<![\w'])[({{]\s*((?:{_RID}\s+)*{_RID})\s*[)}}]")       # not the `[R]` of 'M[R]_n
_RB_BRANCH = re.compile(r"(?:(?<![\w'.])with(?![\w'])|(?m:^))[ \t]*\|([^\n=]{1,160})=>")
_RB_PATCHARS = re.compile(r"[\w'\s&,_?\[\]|()]*")


def _rocq_pat(seg: str) -> list[str]:
    """Names of an intro pattern at the start of SEG. A name after `/` is a view, not a
    binder. A parenthesis binds its leading names when it has a colon, or all its names when
    it holds only names joined by `&` or `,`; any other parenthesis is a term."""
    seg = _RB_STOP.split(seg)[0]
    out, i, n = [], 0, len(seg)
    while i < n:
        c = seg[i]
        if c == "(":
            j = _match_close(seg, i, "(", ")")
            if j < 0:
                break
            inner = seg[i + 1:j]
            m = re.match(rf"\s*((?:{_RID}\s+)*{_RID})\s*:", inner)
            if m:
                out += m.group(1).split()
            elif ("&" in inner or "," in inner) and _RB_PATCHARS.fullmatch(inner):
                out += _RSIMPLE.findall(inner)
            i = j + 1
            continue
        if c == ":":
            break
        if c == "/":
            m = _RTOK.match(seg, i + 1)
            if m:
                i = m.end()
                continue
        m = _RSIMPLE.match(seg, i)
        if m:
            out.append(m.group())
            i = m.end()
            continue
        i += 1
    return out


def rocq_bound(text: str, skip: int = 0):
    """Names bound inside a Rocq declaration: (hard, soft).

    hard: read from the header after the declared name and before the colon of the
    statement, bare names and groups `(x y : T)`; the binders after forall/exists/fun, bare
    or in groups, when a comma or `=>` closes them; the names after intros/wlog; SSReflect
    intro patterns after a tactic's `=>`. A bracket `(t : T)` elsewhere is a cast and binds
    nothing. SKIP is the offset just past the declared name. The set is flat.
    soft: name -> (offset of the binding, end of its sentence) for the first `have x`,
    `set (x := ..)`, `pose x := ..`, `assert (H : ..)`, `.. as x` of each name: the name is
    local only after that sentence (`pose proof (foo a) as foo`)."""
    hard, soft = set(), {}

    def add_soft(nm, at):
        if nm != "_" and nm not in soft:
            m = _RDOT.search(text, at)
            soft[nm] = (at, m.end() if m else len(text))

    hend = _header_end(text, (":", ":=", "."))
    head = text[skip:hend] if skip < hend else ""
    for m in _RB_GROUP.finditer(head):
        hard.update(m.group(1).split())
    for m in _RB_BARE.finditer(head):                  # `{P Q}`: binders written without a type
        hard.update(m.group(1).split())
    for m in _RB_BRANCH.finditer(text):                # variables of a match branch `| C x y =>`
        prev = "("
        for x in re.finditer(r"[(|,]|" + _RSIMPLE.pattern, m.group(1)):
            if x.group() in "(|,":
                prev = x.group()
            else:
                if prev not in "(|":                   # the first name of a pattern is its constructor
                    hard.add(x.group())
                prev = "x"
    depth = 0
    for m in re.finditer(r"[(\[{]|[)\]}]|" + _RSIMPLE.pattern, head):
        t = m.group()
        if t in "([{":
            depth += 1
        elif t in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0:
            hard.add(t)
    for m in _RB_BINDER.finditer(text):
        e = _RB_BEND.search(m.group(1))
        if not e or e.group() not in (",", "=>"):
            continue                                   # `exists x.` is the tactic, not a binder
        seg = m.group(1)[:e.start()]
        d2 = 0
        for x in re.finditer(r"[(\[{]|[)\]}]|:|" + _RSIMPLE.pattern, seg):
            t = x.group()
            if t in "([{":
                d2 += 1
                g = _RB_GROUP.match(seg, x.start())
                if g:
                    hard.update(g.group(1).split())
            elif t in ")]}":
                d2 = max(0, d2 - 1)
            elif t == ":":
                if d2 == 0:
                    break
            elif d2 == 0:
                hard.add(t)
    for rx in (_RB_NAMED, _RB_SETPOSE):
        for m in rx.finditer(text):
            add_soft(m.group(1), m.start(1))
    for m in _RB_TAC.finditer(text):
        names = _rocq_pat(m.group(2))
        if m.group(1) in ROCQ_SOFT:
            for nm in names:
                k = _RSIMPLE.search(text, m.end(1))
                while k and k.group() != nm:
                    k = _RSIMPLE.search(text, k.end())
                if k:
                    add_soft(nm, k.start())
        else:
            hard.update(names)
    for m in _RB_ARROW.finditer(text):
        before = text[max(0, m.start() - 200):m.start()]
        k = max(before.rfind("=>"), before.rfind(". "), before.rfind(".\n"), before.rfind(";"))
        tail = before[k + 1:]
        if re.search(r"(?<![\w'.])(?:fun|match|with)(?![\w'])|λ|\|", tail):
            continue                                   # the arrow of a fun or of a match branch
        hard.update(_rocq_pat(m.group(1)))
    hard.discard("_")
    for nm in hard:
        soft.pop(nm, None)
    return hard, soft


ROCQ_TACTICS = frozenset("""set pose have suff suffices move case elim apply exact rewrite split left
right exists intros intro destruct induction inversion unfold fold simpl cbn auto eauto trivial
assumption reflexivity symmetry transitivity constructor econstructor generalize clear subst
replace assert enough cut exfalso contradiction discriminate injection congruence lia omega ring
field now by do try repeat first last done congr wlog without pattern change red hnf compute
specialize rename remember revert refine eapply erewrite instantiate exploit absurd firstorder
tauto intuition decide easy idtac fail solve progress abstract under over""".split())
_ROCQ_HEAD = re.compile(r"(?:^|[.;|\[(]|(?<![\w'.])(?:by|try|do|repeat|first|last|now|progress|abstract|solve))\s*$")


def rocq_tokens(masked: str, a: int, b: int):
    """Yield (token, offset, tactic_head): tactic_head when the token opens a sentence or
    follows `;`, `|`, `[`, `(`, `by`, `try`, `do`, `repeat`, `first`, `now`."""
    for m in _RTOK.finditer(masked, a, b):
        s = m.start()
        yield m.group(), s, bool(_ROCQ_HEAD.search(masked[max(a, s - 14):s]))


# ============================================================================ Isabelle

_ISA_OPEN = re.compile(r'\(\*|\\<open>|"|`|\{\*')
_ISA_CMT = re.compile(r"\(\*|\*\)")
_ISA_CART = re.compile(r"\\<open>|\\<close>")
_ISA_PREV = re.compile(r"(\\<comment>|\\<\^marker>|\\<\^cancel>|--|[A-Za-z_]+)[ \t\n]*(?:\([^()\"]*\)[ \t\n]*)?"
                       r"(?:%[A-Za-z_]+[ \t\n]*)?$")
ISA_DOC = frozenset(("text", "txt", "text_raw", "section", "subsection", "subsubsection", "chapter",
                     "paragraph", "subparagraph", "header", "\\<comment>", "\\<^marker>", "\\<^cancel>", "--"))
ISA_ML = frozenset("""ML ML_val ML_prf ML_command ML_file SML_file setup local_setup method_setup
attribute_setup simproc_setup parse_translation print_translation typed_print_translation
parse_ast_translation print_ast_translation declaration syntax_declaration oracle ML_export
imports keywords abbrevs""".split())
# the only symbol names given a meaning: they bind the identifiers that follow them
ISA_BINDERS = ("forall", "exists", "nexists", "lambda", "And", "Sum", "Prod", "Union", "Inter")


def scan_isabelle(text: str, tspans: list | None = None) -> tuple[str, str]:
    """(outer, inner), both as long as TEXT. The spans of the inner strings that follow `::`
    in the outer syntax (they hold a type) are appended to TSPANS.

    outer: the Isar outer syntax. Comments, document text and ML text are blank; each inner
           string or cartouche is kept as a pair of double quotes with blanks between.
    inner: only the content of inner strings and cartouches (terms, types, propositions).
    A string or cartouche that follows a document command (text, section, \\<comment>, ...)
    is document text; one that follows an ML command is ML text; any other is inner syntax."""
    outer, inner, i, n, keep = [], [], 0, len(text), 0

    def emit(a, b, how, ks=None):
        nonlocal keep
        if how == "doc" and ks is not None and ks >= keep:
            outer.append(text[keep:ks])
            outer.append(_blank(text[ks:a]))
        else:
            outer.append(text[keep:a])
        inner.append(_blank(text[keep:a]))
        seg = text[a:b]
        if how == "inner":
            ld = 7 if seg.startswith("\\<open>") else 1
            rd = 8 if seg.endswith("\\<close>") and ld == 7 else (1 if len(seg) > ld else 0)
            mid = seg[ld:len(seg) - rd] if rd else seg[ld:]
            outer.append('"' + " " * (ld - 1) + _blank(mid) + (" " * (rd - 1) + '"' if rd else ""))
            inner.append(" " * ld + mid + " " * rd)
        else:
            outer.append(_blank(seg))
            inner.append(_blank(seg))
        keep = b

    while i < n:
        m = _ISA_OPEN.search(text, i)
        if not m:
            break
        s, t = m.start(), m.group()
        if t == "(*":
            depth, j = 1, s + 2
            while depth:
                m2 = _ISA_CMT.search(text, j)
                if not m2:
                    j = n
                    break
                depth += 1 if m2.group() == "(*" else -1
                j = m2.end()
            emit(s, j, "comment")
            i = j
            continue
        if t == "\\<open>":
            depth, j = 1, m.end()
            while depth:
                m2 = _ISA_CART.search(text, j)
                if not m2:
                    j = n
                    break
                depth += 1 if m2.group() == "\\<open>" else -1
                j = m2.end()
        elif t == "{*":
            k = text.find("*}", s + 2)
            j = n if k < 0 else k + 2
        else:
            j = s + 1
            while j < n and text[j] != t:
                j += 2 if (text[j] == "\\" and text[j + 1:j + 2] in ('"', "\\", "`")) else 1
            j = min(j + 1, n)
        pm = _ISA_PREV.search(text, max(keep, s - 160), s)
        word = pm.group(1) if pm else ""
        if word in ISA_DOC:
            emit(s, j, "doc", pm.start(1))
        elif word in ISA_ML or t == "{*":
            emit(s, j, "ml")
        else:
            if tspans is not None and text[max(0, s - 40):s].rstrip().endswith("::"):
                tspans.append((s, j))
            emit(s, j, "inner")
        i = j
    outer.append(text[keep:])
    inner.append(_blank(text[keep:]))
    return "".join(outer), "".join(inner)


_IID = r"[^\W\d][\w']*"
_ISYM = r"\\<\^?[A-Za-z0-9_]+>"
_INAME = re.compile(rf"(?:{_ISYM}|[\w'.])+")
_SYMS = re.compile(_ISYM)
_ISYMRUN = re.compile(rf"(?:{_ISYM}|[\w'])+(?:\.(?:{_ISYM}|[\w'])+)*")
_ITOK = re.compile(rf"{_ISYM}|(?<![\w'.?]){_IID}(?:\.{_IID})*")
_ISIMPLE = re.compile(rf"(?<![\w'.?\\<]){_IID}(?![\w'.>])")

ISA_THM = frozenset("lemma theorem corollary proposition schematic_goal".split())
ISA_DECL = {
    "lemma": THEOREM, "theorem": THEOREM, "corollary": THEOREM, "proposition": THEOREM,
    "schematic_goal": THEOREM, "lemmas": THEOREM, "theorems": THEOREM,
    "definition": DEFINITION, "abbreviation": DEFINITION, "fun": DEFINITION, "function": DEFINITION,
    "primrec": DEFINITION, "primcorec": DEFINITION, "primcorecursive": DEFINITION, "corec": DEFINITION,
    "corecursive": DEFINITION, "partial_function": DEFINITION, "lift_definition": DEFINITION,
    "nominal_function": DEFINITION, "nominal_primrec": DEFINITION, "quotient_definition": DEFINITION,
    "sepref_def": DEFINITION, "sepref_definition": DEFINITION, "inductive": DEFINITION,
    "coinductive": DEFINITION, "inductive_set": DEFINITION, "coinductive_set": DEFINITION,
    "datatype": TYPE, "codatatype": TYPE, "old_datatype": TYPE, "nominal_datatype": TYPE,
    "type_synonym": TYPE, "typedef": TYPE, "typedecl": TYPE, "record": TYPE, "quotient_type": TYPE,
    "alphabet": TYPE, "defs": DEFINITION,
    "locale": TYPE, "class": TYPE,
    "instantiation": INSTANCE, "instance": INSTANCE, "interpretation": INSTANCE,
    "global_interpretation": INSTANCE, "sublocale": INSTANCE, "subclass": INSTANCE,
    "consts": ASSUMPTION, "axiomatization": ASSUMPTION,
    "named_theorems": OTHER, "method": OTHER, "termination": OTHER, "crunch": OTHER, "crunches": OTHER,
    "declare": OTHER, "bundle": OTHER,
}
ISA_OTHER_CMDS = frozenset("""theory begin end context experiment notepad overloading notation no_notation
syntax no_syntax translations no_translations hide_const hide_fact hide_type hide_class unbundle
open_bundle ML ML_val ML_file SML_file setup local_setup method_setup attribute_setup simproc_setup
setup_lifting lifting_update lifting_forget export_code code_printing code_identifier code_reserved
value term thm typ prop print_theorems print_locale print_statement find_theorems find_consts
declaration syntax_declaration type_notation no_type_notation default_sort adhoc_overloading
no_adhoc_overloading alias type_alias sepref_register export_llvm llvm_deps arch_requalify_facts
arch_requalify_consts arch_requalify_types requalify_facts requalify_consts requalify_types derive
free_constructors bnf copy_bnf lift_bnf inductive_cases inductive_simps code_datatype
code_pred values parse_translation print_translation typed_print_translation oracle nitpick_params
print_bundles print_classes thy_deps unused_thms lemmas_with simps_of_case case_of_simps
functor realizers extract nonterminal judgment simproc_setup named_simps hide_fact code_deps
context_notation external_file bibtex_file""".split())
ISA_OPENERS = frozenset("theory locale class context instantiation experiment notepad overloading bundle".split())
ISA_STMT_KW = frozenset("fixes assumes shows obtains includes notes defines constrains if for and where is".split())
ISA_FACT_NS = "f"      # named by outer tokens
ISA_TERM_NS = "t"      # named by inner tokens
ISA_BOTH_NS = "b"

_ISA_LINE = re.compile(r"(?m)^[ \t]*((?:(?:private|qualified|protected)[ \t]+)*)([A-Za-z_]+)(?![\w'.])")
_ISA_PROOF = re.compile(r"(?<![\w.'])(?:proof|by|apply|using|unfolding|supply|including|sorry|oops|done|"
                        r"apply_end|nitpick|quickcheck|sledgehammer|subgoal|defer|prefer|back|\\<proof>)"
                        r"(?![\w.'])|(?<=\s)\.\.?(?=\s|$)")
_ISA_WHERE = re.compile(r"(?<![\w.'])where(?![\w.'])")
_ISA_IN = re.compile(r"\(\s*in\s+((?:" + _ISYM + r"|[\w'.])+)\s*\)")
_ISA_PAREN = re.compile(r"\([^()\"]*\)")
_ISA_BEGIN = re.compile(r"(?<![\w.'])begin(?![\w.'])")


def _isa_skip_opts(outer: str, p: int, e: int):
    """Skip white space and parenthesised options from P; return (new p, locale or None)."""
    loc = None
    while True:
        p = _WS.match(outer, p).end()
        m = _ISA_IN.match(outer, p)
        if m and m.end() <= e:
            loc = m.group(1)
            p = m.end()
            continue
        m = _ISA_PAREN.match(outer, p)
        if m and m.end() <= e:
            p = m.end()
            continue
        return p, loc


def _isa_attr_end(outer: str, p: int) -> int:
    """If outer[p] opens an attribute bracket, the offset after its close; else p."""
    if outer[p:p + 1] == "[":
        q = _match_close(outer, p, "[", "]", min(len(outer), p + 2000))
        if q > 0:
            return q + 1
    return p


def isabelle_table(text: str) -> dict:
    tspans = []
    outer, inner = scan_isabelle(text, tspans)
    L = Lines(outer)
    n = len(outer)
    cmds = []
    for m in _ISA_LINE.finditer(outer):
        w = m.group(2)
        if w in ISA_DECL or w in ISA_OTHER_CMDS:
            cmds.append((m.start(), m.start(2), m.end(2), w, m.group(1).split()))
    decls, stack, anomalies, interps = [], [], [], {}
    parents = {}               # locale or class -> the locales its header imports
    pending = None

    def qualifier():
        for k, q in reversed(stack):
            if q:
                return q
        return None

    def first_inner_head(a, b):
        """The defined name of `definition "f x = .."`: the first token of the first inner
        string. When that token is a symbol (`"\\<V> \\<equiv> set Vs"`) the symbol is the name."""
        m = re.compile(r"[^\s(]").search(inner, a, b)
        if not m:
            return None
        t = _ISYMRUN.match(inner, m.start(), b)
        return t.group() if t else None

    for ci, (ls, ks, ke, w, mods) in enumerate(cmds):
        e = cmds[ci + 1][0] if ci + 1 < len(cmds) else n
        if w == "begin":
            if pending is not None:
                stack.append(pending)
                pending = None
            else:
                stack.append(("begin", None))
            continue
        if w == "end":
            pending = None
            if stack:
                stack.pop()
            else:
                anomalies.append(f"end-without-scope@{L.line(ks)}")
            continue
        pending = None
        p, loc = _isa_skip_opts(outer, ke, e)
        if w in ISA_OPENERS:
            q = None
            if w in ("locale", "class"):
                m = _INAME.match(outer, p)
                q = m.group() if m else None
            elif w == "context":
                m = _INAME.match(outer, p)
                if m and m.group() not in ISA_STMT_KW and m.group() != "begin":
                    q = m.group()
            bm = _ISA_BEGIN.search(outer, ke, e)
            if bm:
                stack.append((w, q))
            else:
                pending = (w, q)
        cls = ISA_DECL.get(w)
        if cls is None:
            continue
        qual = loc or qualifier()
        scope = [qual] if qual else []
        end = _rstrip_off(outer, ks, e)
        names, name_at, provides, ns, split = [], None, {}, ISA_FACT_NS, None
        if w in ISA_THM:
            m = _INAME.match(outer, p)
            if m and m.group() not in ISA_STMT_KW:
                q = _isa_attr_end(outer, _WS.match(outer, m.end()).end())
                q = _WS.match(outer, q).end()
                if outer[q:q + 1] == ":" and outer[q:q + 2] != "::":
                    names, name_at = [m.group()], (m.start(), m.end())
            pm = _ISA_PROOF.search(outer, p, end)
            split = pm.start() if pm else None
            sm = re.compile(r"(?<![\w.'])shows(?![\w.'])").search(outer, p, split if split else end)
            if sm:
                for x in re.compile(r"(?:shows|and)\s+((?:" + _ISYM + r"|[\w'.])+)\s*(?:\[[^\]]*\])?\s*:(?!:)").finditer(
                        outer, sm.start(), split if split else end):
                    provides[x.group(1)] = "shows-name"
        elif w in ("lemmas", "theorems"):
            m = _INAME.match(outer, p)
            if m:
                names, name_at = [m.group()], (m.start(), m.end())
            k = outer.find("=", p, end)
            split = k if k >= 0 else None
        elif w == "named_theorems":
            for x in re.split(r"(?<![\w.'])and(?![\w.'])", outer[p:end]):
                m = _INAME.match(x, _WS.match(x, 0).end())
                if m:
                    names.append(m.group())
        elif w in ("definition", "abbreviation", "defs"):
            ns = ISA_TERM_NS
            m = _INAME.match(outer, p)
            wm = _ISA_WHERE.search(outer, p, end)
            nxt = _WS.match(outer, m.end()).end() if m else p
            if m and m.group() not in ISA_STMT_KW and (outer.startswith("::", nxt) or outer.startswith("where", nxt)
                                                         or outer[nxt:nxt + 1] == "("):
                names, name_at = [m.group()], (m.start(), m.end())
                split = wm.start() if wm else None
            else:
                h = first_inner_head(p, end)
                if h:
                    names = [h]
                split = wm.start() if wm else None
        elif w in ("fun", "function", "primrec", "primcorec", "primcorecursive", "corec", "corecursive",
                   "partial_function", "nominal_function", "nominal_primrec", "inductive", "coinductive",
                   "inductive_set", "coinductive_set"):
            ns = ISA_TERM_NS
            wm = _ISA_WHERE.search(outer, p, end)
            head_end = wm.start() if wm else end
            head = _ISA_PAREN.sub(lambda mm: " " * len(mm.group()), outer[p:head_end])
            first = True
            for part in re.split(r"(?<![\w.'])(?:and|for)(?![\w.'])", head):
                m = _INAME.match(part, _WS.match(part, 0).end())
                if m and m.group() not in ISA_STMT_KW:
                    names.append(m.group())
                    if first:
                        name_at = (p + m.start(), p + m.end()) if part is head or head.startswith(part) else None
                first = False
                if "for" in part.split():
                    break
            if wm:
                split = wm.start()
                if w.startswith(("inductive", "coinductive")) and names:
                    for x in re.compile(r"(?:(?<=\s)|(?<=\|))((?:" + _ISYM + r"|[\w'.])+)\s*(?:\[[^\]]*\])?\s*:(?!:)").finditer(
                            outer, wm.end(), end):
                        if x.group(1) not in ISA_STMT_KW:
                            provides[names[0] + "." + x.group(1)] = "intro-rule"
                            provides[x.group(1)] = "intro-rule"
        elif w in ("datatype", "codatatype", "old_datatype", "nominal_datatype", "type_synonym", "typedef",
                   "typedecl", "record", "quotient_type", "alphabet"):
            ns = ISA_TERM_NS
            seg = outer[p:end]
            eq = seg.find("=")
            head = seg[:eq] if eq >= 0 else seg
            head = _ISA_PAREN.sub(lambda mm: " " * len(mm.group()), head)
            cand = [x for x in _INAME.finditer(head) if not x.group().startswith("'")]
            if cand:
                names = [cand[-1].group()]
                name_at = (p + cand[-1].start(), p + cand[-1].end())
            if eq >= 0 and w in ("datatype", "codatatype", "old_datatype", "nominal_datatype"):
                depth, start, parts = 0, eq + 1, []
                for i in range(eq + 1, len(seg)):
                    c = seg[i]
                    if c in "([":
                        depth += 1
                    elif c in ")]":
                        depth -= 1
                    elif c == "|" and depth == 0:
                        parts.append(seg[start:i])
                        start = i + 1
                parts.append(seg[start:])
                for part in parts:
                    part = re.sub(r"^\s*\(\s*[\w']+\s*:\s*", " ", part)
                    m = _INAME.match(part, _WS.match(part, 0).end())
                    if m and not m.group().startswith("'"):
                        provides[m.group()] = "constructor"
            elif eq >= 0 and w in ("record", "alphabet"):
                for x in re.compile(r"((?:" + _ISYM + r"|[\w'])+)\s*::").finditer(seg, eq + 1):
                    provides[x.group(1)] = "field"
        elif w in ("locale", "class"):
            ns = ISA_BOTH_NS
            m = _INAME.match(outer, p)
            if m:
                names, name_at = [m.group()], (m.start(), m.end())
                for x in re.compile(r"(?:assumes|and)\s+((?:" + _ISYM + r"|[\w'.])+)\s*(?:\[[^\]]*\])?\s*:(?!:)").finditer(
                        outer, m.end(), end):
                    provides[m.group() + "." + x.group(1)] = "assumption"
                eq = _WS.match(outer, m.end()).end()
                if outer[eq:eq + 1] == "=":
                    hm = re.compile(r"(?<![\w.'])(?:fixes|assumes|defines|notes|constrains|includes|begin)(?![\w.'])").search(
                        outer, eq, end)
                    for part in outer[eq + 1:hm.start() if hm else end].split("+"):
                        pm2 = re.match(r"\s*(?:(?:" + _ISYM + r"|[\w'.])+\s*:(?!:)\s*)?((?:" + _ISYM + r"|[\w'.])+)", part)
                        if pm2 and pm2.group(1) not in ISA_STMT_KW:
                            parents.setdefault(m.group(), []).append(pm2.group(1))
        elif w in ("interpretation", "global_interpretation", "sublocale", "subclass"):
            ns = ISA_FACT_NS
            seg_end = end
            pm = _ISA_PROOF.search(outer, p, end)
            split = pm.start() if pm else None
            head = outer[p:split if split else seg_end]
            if w in ("sublocale", "subclass"):
                head2 = re.split(r"<|\\<subseteq>", head, 1)
                sub = _INAME.match(head2[0], _WS.match(head2[0], 0).end()) if len(head2) > 1 else None
                head = head2[1] if len(head2) > 1 else head
                sup = re.match(r"\s*(?:(?:" + _ISYM + r"|[\w'.])+\s*:(?!:)\s*)?((?:" + _ISYM + r"|[\w'.])+)", head)
                child = sub.group() if sub else qualifier()
                if child and sup:
                    parents.setdefault(child, []).append(sup.group(1))
            m = re.compile(r"\s*((?:" + _ISYM + r"|[\w'.])+)\s*:(?!:)\s*((?:" + _ISYM + r"|[\w'.])+)").match(head)
            if m:
                names = [m.group(1)]
                interps[m.group(1)] = m.group(2)
        elif w in ("instantiation", "instance"):
            pm = _ISA_PROOF.search(outer, p, end)
            split = pm.start() if pm else None
        elif w in ("consts", "axiomatization"):
            ns = ISA_TERM_NS
            wm = _ISA_WHERE.search(outer, p, end)
            for x in re.compile(r"((?:" + _ISYM + r"|[\w'.])+)\s*::").finditer(outer, p, wm.start() if wm else end):
                names.append(x.group(1))
            if wm:
                for x in re.compile(r"((?:" + _ISYM + r"|[\w'.])+)\s*(?:\[[^\]]*\])?\s*:(?!:)").finditer(outer, wm.end(), end):
                    provides[x.group(1)] = "axiom"
        elif w in ("lift_definition", "sepref_def", "sepref_definition", "quotient_definition"):
            ns = ISA_TERM_NS if w != "sepref_def" else ISA_BOTH_NS
            m = _INAME.match(outer, p)
            if m:
                names, name_at = [m.group()], (m.start(), m.end())
            im = re.compile(r"(?<![\w.'])is(?![\w.'])").search(outer, p, end)
            split = im.start() if im else None
        elif w == "method":
            ns = ISA_FACT_NS
            m = _INAME.match(outer, p)
            if m:
                names, name_at = [m.group()], (m.start(), m.end())
            k = outer.find("=", p, end)
            split = k if k >= 0 else None
        elif w == "bundle":
            m = _INAME.match(outer, p)
            if m:
                names = [m.group()]
        else:                                        # termination, crunch, crunches, declare
            split = ke
        first = True
        for short in names or [None]:
            full = (qual + "." + short if qual and "." not in short else short) if short else None
            d = _decl(full, short, w, cls, ls, ks, end, scope)
            d["name_at"] = name_at if first else None
            d["split"] = split if (split is not None and ks < split < end) else None
            d["provides"] = {(qual + "." + k if qual and "." not in k and v in ("shows-name",) else k): v
                             for k, v in provides.items()} if first else {}
            d["ns"] = ns
            d["flags"] = sorted(set(mods))
            d["dup"] = not first
            first = False
            decls.append(d)
    if stack:
        anomalies.append("scope-open-at-eof:" + str(len(stack)))
    return {"lang": "isabelle", "dialect": "isabelle", "masked": outer, "inner": inner, "L": L, "decls": decls,
            "opens": [], "interps": interps, "parents": parents, "anomalies": anomalies,
            "tspans": tspans, "tstarts": [a for a, _ in tspans]}


_IB_FACT = re.compile(r"(?<![\w'.?])(" + _IID + r")\s*(?:\[[^\]\n]*\])?\s*:(?!:)")
_IB_NOTE = re.compile(r"(?<![\w.'])(?:note\s+\(?\s*(" + _IID + r")|interpret\s+(" + _IID + r")\s*:(?!:))")
_ISA_CASE = re.compile(r"(?<![\w.'])case\s+\(?\s*$")
_IB_FIX = re.compile(r"(?<![\w.'])(?:fixes|fix|for|obtains?|define|defines|arbitrary\s*:)(?![\w.'])(?=([^\n]{0,200}))")
_IB_BINDER = re.compile(r"(?:\\<(?:" + "|".join(ISA_BINDERS) + r")>!?|(?<![\w'.])(?:ALL|EX|SOME|THE|LEAST|GREATEST|INF|SUP)\b|[%{]|!!)"
                        r"\s*((?:" + _IID + r"(?:\s+|(?=[.:\\<])))+)(?:\.|::|\\<in>|\\<le>|<)")


def isabelle_bound(outer_text: str, inner_text: str) -> tuple[set[str], set[str]]:
    """(fact names, term names) bound inside an Isabelle declaration. Fact names: `name:` and
    `name[attrs]:` in the outer syntax, names after note/interpret/case. Term names: names
    after fixes/fix/for/obtain/define, and after a binder symbol in the inner syntax. Flat."""
    facts, terms = set(), set()
    for m in _IB_FACT.finditer(outer_text):
        facts.add(m.group(1))
    for m in _IB_NOTE.finditer(outer_text):     # `interpret p: loc` binds p; `interpret loc` binds nothing
        facts.add(m.group(1) or m.group(2))
    for m in _IB_FIX.finditer(outer_text):
        seg = re.split(r"(?<![\w.'])(?:where|assumes|shows|rule|taking|in)(?![\w.'])|::|\"|\)", m.group(1))[0]
        for x in _ISIMPLE.findall(seg):
            if x != "and":
                terms.add(x)
    for m in _IB_BINDER.finditer(inner_text):
        terms.update(m.group(1).split())
    return facts, terms


def isabelle_tokens(outer: str, inner: str, a: int, b: int, tspans=None, tstarts=None):
    """Yield (channel+token, offset, False). Channels: 'o' the outer syntax; 'c' an outer
    name right after `case` (a constructor or a rule); 'i' an inner string; 'y' an inner
    string that follows `::` (a type)."""
    for ch, src in (("o", outer), ("i", inner)):
        for m in _ITOK.finditer(src, a, b):
            t = m.group()
            if t[0] != "\\":
                c = ch
                if ch == "o":
                    if _ISA_CASE.search(src, max(a, m.start() - 12), m.start()):
                        c = "c"
                elif tstarts:
                    k = bisect.bisect_right(tstarts, m.start()) - 1
                    if k >= 0 and m.start() < tspans[k][1]:
                        c = "y"
                yield c + t, m.start(), False
        k = src.find("\\<", a, b)
        while 0 <= k < b:                        # a name written with symbols, e.g. \<alpha>_inv
            ls = k
            while ls > a and (src[ls - 1].isalnum() or src[ls - 1] in "_'."):
                ls -= 1
            m = _ISYMRUN.match(src, ls, b)
            if m and m.end() > k and re.search(r"[\w']", _SYMS.sub("", m.group())):
                yield ch + m.group(), m.start(), False
            k = src.find("\\<", max(k + 2, m.end() if m else 0), b)


# ============================================================================ tables and tokens

_BODY_OPENER = re.compile(r":=|=(?![=>])|(?:where|is)(?![\w'.])")


def file_table(text: str, lang: str) -> dict:
    t = {"lean": lean_table, "rocq": rocq_table, "isabelle": isabelle_table}[lang](text)
    L, n = t["L"], len(t["masked"])
    doc_at = {}                                  # offset where a doc comment's code resumes -> its span
    for a, b in t.get("docs") or ():
        doc_at[_WS.match(t["masked"], b).end()] = (a, b)
    for i, d in enumerate(t["decls"]):
        d["i"] = i
        d["line"] = L.line(d["kw"])
        d["lines"] = [L.line(d["start"]) if lang != "lean" else L.line(min(d["start"], d["kw"])),
                      L.line(max(d["end"] - 1, d["kw"]))]
        if lang == "lean":
            # the span starts at the first attribute or modifier, not at blank lines before it
            s = d["start"]
            while s < d["kw"] and t["masked"][s] in " \t\n":
                s += 1
            d["start"] = s
            d["lines"][0] = L.line(s)
        dc = doc_at.get(d["start"] if lang == "lean" else _WS.match(t["masked"], d["start"]).end())
        d["doc_lines"] = [L.line(dc[0]), L.line(dc[1] - 1)] if dc else None
        sp = d["split"]
        if sp is None:
            d["stmt_lines"] = [d["line"], d["lines"][1]]
            d["body_lines"] = None
        else:
            se = _rstrip_off(t["masked"], d["kw"], sp)
            d["stmt_lines"] = [d["line"], L.line(max(se - 1, d["kw"]))]
            bs = _WS.match(t["masked"], sp).end()
            m = _BODY_OPENER.match(t["masked"], bs)          # the body starts after `:=`, `where`, `=`
            if m and m.end() < d["end"]:
                bs = _WS.match(t["masked"], m.end()).end()
            d["body_lines"] = [L.line(min(bs, max(d["end"] - 1, sp))), d["lines"][1]]
    t["n_lines"] = L.n if not t["masked"].endswith("\n") else L.n - 1
    return t


def decl_bound(t: dict, d: dict):
    """(hard, terms, soft, types) for declaration D, cached in the table.
    lean, rocq: hard and soft as in lean_bound / rocq_bound, soft offsets made absolute;
    terms is None; types (Lean only) maps a header binder or section variable to the first
    identifier of its type. isabelle: hard is the set of bound fact names, terms the set of
    bound term names, soft and types are empty."""
    cache = t.setdefault("bound", {})
    r = cache.get(d["i"])
    if r is not None:
        return r
    lang = t["lang"]
    seg = t["masked"][d["kw"]:d["end"]]
    if lang == "isabelle":
        f, tm = isabelle_bound(seg, t["inner"][d["kw"]:d["end"]])
        r = (f, tm, {}, {})
    else:
        if lang == "lean":
            hard, soft, types = lean_bound(seg)
        else:
            hard, soft = rocq_bound(seg, d["name_at"][1] - d["kw"] if d["name_at"] else 0)
            types = {}
        for nm, a, b, ty in t.get("variables") or ():  # Lean section variables in scope here
            if a < d["kw"] and (b is None or d["kw"] < b):
                if nm not in hard and ty:
                    types.setdefault(nm, ty)
                hard.add(nm)
                soft.pop(nm, None)
        r = (hard, None, {k: (v[0] + d["kw"], v[1] + d["kw"]) for k, v in soft.items()}, types)
    cache[d["i"]] = r
    return r


def decl_mentions(t: dict, d: dict) -> dict:
    """token -> [n_stmt, first_stmt_offset, n_body, first_body_offset, head_only] for the
    declaration D of table T. Skipped: the declared name's own occurrence in the header; the
    binding occurrence of a soft-bound name; its occurrences after its definition (a dotted
    Lean token `h.f` is then kept as the field token `.f`)."""
    lang, masked = t["lang"], t["masked"]
    a, b = d["kw"], d["end"]
    sp = d["split"] if d["split"] is not None else b
    skip = d["name_at"][0] if d["name_at"] else -1
    soft = decl_bound(t, d)[2]
    it = (lean_tokens(masked, a, b) if lang == "lean" else rocq_tokens(masked, a, b) if lang == "rocq"
          else isabelle_tokens(masked, t["inner"], a, b, t.get("tspans"), t.get("tstarts")))
    out = {}
    by_at = -1
    if lang == "lean":                           # before the first `by` of the body every word is a term
        mb = _LEAN_BY.search(masked, sp, b)
        by_at = mb.start() if mb else b
    for tok, off, head in it:
        if off == skip:
            continue
        if head and off < by_at:
            head = False
        if soft and tok[0] != ".":
            first = tok.split(".", 1)
            z = soft.get(first[0])
            if z is not None and (off == z[0] or off >= z[1]):
                if off == z[0] or len(first) == 1 or lang != "lean":
                    continue
                tok, head = "." + first[1].split(".")[0], False
        r = out.get(tok)
        if r is None:
            r = out[tok] = [0, -1, 0, -1, True]
        if off < sp:
            r[0] += 1
            if r[1] < 0 or off < r[1]:
                r[1] = off
        else:
            r[2] += 1
            if r[3] < 0 or off < r[3]:
                r[3] = off
        if not head:
            r[4] = False
    return out


def range_tokens(t: dict, a: int, b: int):
    """(token, offset, tactic_head) for every identifier token in the offsets [a, b) of table T,
    in order of offset."""
    lang, masked = t["lang"], t["masked"]
    it = (lean_tokens(masked, a, b) if lang == "lean" else rocq_tokens(masked, a, b) if lang == "rocq"
          else isabelle_tokens(masked, t["inner"], a, b, t.get("tspans"), t.get("tstarts")))
    return sorted(it, key=lambda x: (x[1], x[0]))


# ============================================================================ resolver

MATCH_LEVELS = ("exact", "scoped", "opened", "file-qualified", "suffix", "field", "last")
FIELD_TYPE_RULES = True      # switch for measurement with feature_gold.py; see library/features/gold-lean.md


class Resolver:
    """Maps a token met inside a declaration to the declarations of the copied files it may name.

    A declaration's full name is its written name prefixed by the enclosing Lean namespaces,
    Rocq modules or Isabelle locale. A token with components c1..ck matches a declaration
    whose full name ends with c1..ck. The part of the full name the token leaves out decides
    the level:
      exact           nothing is left out
      scoped          what is left out is a prefix of the using declaration's own scope (for
                      Isabelle: its locale or a locale that locale imports)
      opened          what is left out is named by an `open` (Lean) or `Import` (Rocq) of the
                      using file; the scope of the open is not tracked
      file-qualified  (Rocq, Isabelle) the token carries the file name before the full name
      suffix          (Rocq, Isabelle) anything else: the name lives in a module or locale the
                      text does not show to be open. Functor instances, `Include`, locale
                      inheritance from files not copied and unprefixed interpretations make
                      such a reference legal; the text does not say whether one applies. Lean
                      has no such level: there the name must be exact, scoped or opened.
      field           (Lean only) `x.f` or `(e).f` with x bound or lower-case: f is the last
                      component of a declaration in some namespace (generalised field
                      notation). The written type of x, when the header gives one, selects
                      among several candidates.
      last            (Isabelle only) a qualified fact `p.f` whose prefix names nothing known
                      or is bound in the proof (`interpret p: loc`): f is the last component
                      of a fact declared in a locale
    Only the best level found is used. exact, scoped, opened and file-qualified are the
    strong levels: among several candidates the nearest one declared before the using
    declaration in the same file wins, else the last one of the first other file in path
    order. suffix, field and last are the weak levels: every candidate gets an edge.
    `amb` is the number of candidates at the level used. A declaration made later in the
    same file is never a candidate. A one-component token bound inside the using
    declaration names nothing (see lean_bound, rocq_bound, isabelle_bound).
    """

    def __init__(self, tables: list[tuple[str, dict]]):
        self.tables = tables
        self.items = []                 # g -> (file index, decl, group)
        self.by_last = {}               # last component -> [(g, components, via)]
        self.opens = []
        self.stems = []
        self.interps = {}
        self.aliases = {}
        self.parents = {}
        for fi, (path, t) in enumerate(tables):
            self.opens.append(frozenset(t["opens"]))
            self.stems.append(path.rsplit("/", 1)[-1].rsplit(".", 1)[0])
            self.interps.update(t["interps"])
            self.aliases.update(t.get("aliases") or {})
            for k, v in sorted((t.get("parents") or {}).items()):
                self.parents.setdefault(k, [])
                self.parents[k] += [x for x in v if x not in self.parents[k]]
            group = None
            for d in t["decls"]:
                g = len(self.items)
                if not d["dup"]:
                    group = g
                self.items.append((fi, d, group))
                if "aborted" in d["flags"]:
                    continue                           # `Abort.` leaves no constant behind
                if d["name"]:
                    self._add(d["name"], g, None)
                for nm in sorted(d["provides"]):
                    full = nm if t["lang"] == "isabelle" else ".".join(d["scope"] + [nm])
                    self._add(full, g, d["provides"][nm])

    _VIA_NS = {"assumption": "f", "shows-name": "f", "intro-rule": "f", "axiom": "f",
               "constructor": "t", "field": "t"}

    def _add(self, full: str, g: int, via):
        comps = tuple(full.split("."))
        ns = self._VIA_NS.get(via) or self.items[g][1]["ns"]
        self.by_last.setdefault(comps[-1], []).append((g, comps, via, ns))

    def bound(self, g: int):
        fi, d, _ = self.items[g]
        return decl_bound(self.tables[fi][1], d)

    def _visible(self, g: int) -> list:
        """Name prefixes visible inside declaration G without qualification: its own
        namespace path (Lean: that of its full name; Rocq: its modules); for Isabelle the
        enclosing locale and the locales that locale imports, transitively."""
        fi, d, _ = self.items[g]
        lang = self.tables[fi][1]["lang"]
        if lang == "lean" and d["name"]:
            return [tuple(d["name"].split(".")[:-1])]
        own = tuple(x for s in d["scope"] for x in s.split("."))
        if lang != "isabelle" or not d["scope"]:
            return [own]
        seen, todo = [], [d["scope"][0]]
        while todo:
            x = todo.pop(0)
            if x in seen:
                continue
            seen.append(x)
            todo += self.parents.get(x, [])
        return [tuple(x.split(".")) for x in seen]

    def _lookup(self, comps: tuple, g: int, ns: str | None, allow_suffix: bool, only_qualified: bool = False,
                forward: bool = False):
        """Best-level candidates for the components COMPS used inside declaration G.
        Returns (level, [(g2, via)]) or None. A declaration made later in the same file is
        not a candidate (none of the three languages lets a declaration name a later one,
        mutual blocks apart); FORWARD lifts that for text that is not inside G."""
        cands = self.by_last.get(comps[-1])
        if not cands:
            return None
        fi, d, group = self.items[g]
        k = len(comps)
        vis = self._visible(g)
        opens = self.opens[fi]
        buckets = {"exact": [], "scoped": [], "opened": [], "suffix": []}
        loose = []
        for g2, full, via, ns2 in cands:
            if len(full) < k or full[-k:] != comps:
                continue
            fi2, d2, group2 = self.items[g2]
            if ns is not None and ns2 not in ns and ns2 != "b":
                continue
            if only_qualified and len(full) < 2:
                continue
            if d2["vis_end"] is not None and (fi2 != fi or d["kw"] > d2["vis_end"]):
                continue
            if group2 == group and g2 != g:
                continue                                   # a name declared by the same command
            if fi2 == fi and g2 > g and not forward:
                continue                                   # declared later in the same file
            rest = full[:-k]
            if not rest:
                buckets["exact"].append((g2, via))
            elif any(len(rest) <= len(v) and v[:len(rest)] == rest for v in vis):
                buckets["scoped"].append((g2, via))
            elif any(".".join(rest[i:]) in opens for i in range(len(rest))):
                buckets["opened"].append((g2, via))
            elif via != "assumption":
                buckets["suffix"].append((g2, via))
            else:
                loose.append((g2, via))
        # an assumption of a locale the user is not known to be in: kept only when a single
        # locale assumes that name (names such as `dest` or `neq` are assumed by many)
        if len(loose) == 1 and not buckets["suffix"]:
            buckets["suffix"] = loose
        if only_qualified:                      # field and last: every qualified candidate counts
            merged = buckets["exact"] + buckets["scoped"] + buckets["opened"] + buckets["suffix"]
            return ("suffix", merged) if merged else None
        for level in ("exact", "scoped", "opened", "suffix"):
            if buckets[level] and (level != "suffix" or allow_suffix):
                return level, buckets[level]
        return None

    def _pick(self, cands: list, g: int):
        """One candidate out of several: (g2, via, number of candidates). A declaration's own
        name comes before a name it provides (via is None sorts last under `max`)."""
        fi = self.items[g][0]
        key = lambda c: (c[0], c[1] is None, c[1] or "")
        same = [c for c in cands if self.items[c[0]][0] == fi]
        before = [c for c in same if c[0] <= g]
        if before:
            c = max(before, key=key)
        elif same:
            c = min(same, key=key)
        else:                                   # another file: the first in path order, its last one
            f0 = min(self.items[c[0]][0] for c in cands)
            c = max((c for c in cands if self.items[c[0]][0] == f0), key=key)
        return c[0], c[1], len(set(x[0] for x in cands))

    def resolve(self, g: int, tok: str, head_only: bool = False, allow_self: bool = False):
        """Declarations named by TOK inside declaration G.
        Returns (list of (g2, level, via, amb), note) where note is None, 'self', 'shadowed'
        or 'tactic'. g2 is never g unless ALLOW_SELF (used for text that lies outside G)."""
        fi, d, _ = self.items[g]
        lang = self.tables[fi][1]["lang"]
        out, note = [], None
        _lk = self._lookup

        def lookup(comps, g, ns, allow_suffix, only_qualified=False):
            return _lk(comps, g, ns, allow_suffix, only_qualified, forward=allow_self)

        def take(res, via2=None, level2=None):
            nonlocal note
            level, cands = res
            level = level2 or level
            if level in ("suffix", "field", "last"):       # the text does not choose: keep them all
                others = sorted(set(c for c in cands if c[0] != g or allow_self), key=lambda c: (c[0], c[1] or ""))
                if not others:
                    note = "self"
                for g2, via in others:
                    out.append((g2, level, via2 or via, len(others)))
                return
            g2, via, amb = self._pick(cands, g)
            if g2 == g and not allow_self:
                note = "self"
                return
            out.append((g2, level, via2 or via, amb))

        if lang == "lean":
            bound = self.bound(g)[0]
            if tok.startswith("."):
                res = lookup((tok[1:],), g, None, True, only_qualified=True)
                if res:
                    take(res, level2="field")
                return out, note
            comps = tuple(tok.split("."))
            if comps[0] == "_root_" and len(comps) > 1:
                res = lookup(comps[1:], g, None, False)
                if res and res[0] == "exact":
                    take(res)
                return out, note
            if len(comps) == 1:
                if tok in bound:
                    return out, "shadowed"
                if head_only and tok in LEAN_TACTICS:
                    return out, "tactic"
            for k in range(len(comps), 0, -1):
                if k == 1 and len(comps) > 1 and comps[0] in bound:
                    break
                res = lookup(comps[:k], g, None, False)
                if res:
                    take(res, via2=None if k == len(comps) else "head")
                    return out, note
            if len(comps) >= 2 and (comps[0] in bound or comps[0][:1].islower() or comps[0][:1] == "_"):
                res = lookup((comps[1],), g, None, True, only_qualified=True)
                if res:
                    ty = self.bound(g)[3].get(comps[0])
                    if ty:                               # the receiver's written type picks the namespace
                        tc = tuple(ty.split("."))

                        def member_of(c):                # the namespace that the candidate lives in
                            nm = tuple((self.items[c[0]][1]["name"] or "").split("."))
                            return nm if c[1] in ("field", "constructor") else nm[:-1]

                        sub = [c for c in res[1] if c[0] != g and member_of(c)[-len(tc):] == tc]
                        if sub:
                            res = (res[0], sub)
                        elif FIELD_TYPE_RULES and tc[0] not in bound and tc[0][:1].isupper():
                            res = None                   # a named type with no such member in these files
                    if res:
                        take(res, level2="field")
            return out, note
        if lang == "rocq":
            comps = tuple(tok.split("."))
            if len(comps) == 1 and tok in self.bound(g)[0]:
                return out, "shadowed"
            if len(comps) == 1 and head_only and tok in ROCQ_TACTICS:
                return out, "tactic"
            res = lookup(comps, g, None, True)
            if res:
                take(res)
                return out, note
            for k in range(1, len(comps)):
                res = lookup(comps[k:], g, None, False)
                if res and res[0] == "exact":
                    cands = [c for c in res[1] if self.stems[self.items[c[0]][0]] == comps[k - 1]]
                    if cands:
                        take(("file-qualified", cands))
                        return out, note
            if len(comps) >= 2 and comps[0] in self.aliases:      # Module M := N.
                res = lookup(tuple(self.aliases[comps[0]].split(".")) + comps[1:], g, None, True)
                if res:
                    take(res, via2="module-alias")
            return out, note
        # isabelle
        ch, name = tok[0], tok[1:]
        comps = tuple(name.split("."))
        facts, terms = self.bound(g)[:2]

        def prefer(res, keep):
            """Among candidates of one level keep those that satisfy KEEP, if any does."""
            sub = [c for c in res[1] if keep(self.items[c[0]][1], c[1])]
            return (res[0], sub) if sub else res

        if ch == "c":                              # `case (C x y)`: a constructor or a rule name
            res = lookup(comps, g, None, True)
            if res:
                take(prefer(res, lambda d2, via: via in ("constructor", "intro-rule")))
            return out, note
        if ch in "iy":
            if len(comps) == 1 and name in terms:
                return out, "shadowed"
            for k in range(len(comps)):
                res = lookup(comps[k:], g, "tb", True)
                if res:
                    if ch == "y":                  # in a type, a type's own name comes first
                        res = prefer(res, lambda d2, via: via is None and d2["cls"] == TYPE)
                    else:                          # in a term, a field or constructor comes first
                        res = prefer(res, lambda d2, via: not (via is None and d2["cls"] == TYPE))
                    take(res, via2=None if k == 0 else "token-suffix")
                    return out, note
            return out, note
        if len(comps) == 1 and name in terms:
            return out, "shadowed"                 # `fixes x`, `obtain x`: a term name in the outer syntax
        if comps[0] in facts:
            if len(comps) == 1:
                return out, "shadowed"
            # `p.f` with p bound in the proof (interpret p: loc): the fact f of some locale
            res = lookup((comps[-1],), g, "f", True, only_qualified=True)
            if res:
                take(res, level2="last")
            return out, note
        res = lookup(comps, g, "fb", True)
        if res:
            take(res)
            return out, note
        for k in range(1, len(comps)):
            res = lookup(comps[k:], g, "fb", False)
            if res and res[0] == "exact":
                cands = [c for c in res[1] if self.stems[self.items[c[0]][0]] == comps[k - 1]]
                if cands:
                    take(("file-qualified", cands))
                    return out, note
        for suffix, via in (("_def", "def"), ("_axioms", "axioms")):
            if comps[-1].endswith(suffix) and len(comps[-1]) > len(suffix):
                res = lookup(comps[:-1] + (comps[-1][:-len(suffix)],), g, "tb", True)
                if res:
                    take(res, via2=via)
                    return out, note
        for k in range(len(comps) - 1, 0, -1):
            res = lookup(comps[:k], g, None, True)
            if res:                                # `t.simps`, `l.fact`: the declaration named t or l
                take(prefer(res, lambda d2, via: via is None), via2="qualified")
                break
        if len(comps) >= 2 and comps[0] in self.interps:
            res = lookup(tuple(self.interps[comps[0]].split(".")) + comps[1:], g, "fb", True)
            if res:
                take(res, via2="interpretation")
        if not out and note is None and len(comps) >= 2:
            res = lookup((comps[-1],), g, "f", True, only_qualified=True)
            if res:
                take(res, level2="last")
        return out, note


# ============================================================================ self test

def _names(text, lang):
    return [(d["name"], d["kind"], d["lines"][0], d["lines"][1]) for d in file_table(text, lang)["decls"]]


def self_test() -> list[str]:
    """Run the built-in cases; return the list of failures (empty when all pass)."""
    fails = []

    def check(label, got, want):
        if got != want:
            fails.append(f"{label}: got {got!r}, want {want!r}")

    # ---------------------------------------------------------------- Lean
    lean = (
        "/- header /- nested -/ theorem fake : True := trivial -/\n"          # 1
        "namespace Foo\n"                                                      # 2
        "-- theorem commented : True := trivial\n"                             # 3
        "/-- doc with theorem inside -/\n"                                     # 4
        "@[simp, to_additive (attr := simp) bar_add]\n"                        # 5
        "private theorem bar.baz (x : Nat) (h : x = 1 := by decide) :\n"       # 6
        "    x = 1 := by\n"                                                    # 7
        "  have s : String := \"theorem inside string : x\"\n"                 # 8
        "  exact h\n"                                                          # 9
        "\n"                                                                   # 10
        "def f : Nat → Nat\n"                                                  # 11
        "  | 0 => 1\n"                                                         # 12
        "  | n + 1 => f n\n"                                                   # 13
        "instance : Inhabited Nat := ⟨0⟩\n"                                    # 14
        "instance (priority := 100) instFoo : Inhabited Nat where\n"           # 15
        "  default := 'a'.toNat\n"                                             # 16
        "mutual\n"                                                             # 17
        "  theorem m1 : True := trivial\n"                                     # 18
        "  theorem m2 : True := m1\n"                                          # 19
        "end\n"                                                                # 20
        "set_option maxHeartbeats 400000 in\n"                                 # 21
        "theorem _root_.top (a : Nat) : a = a := rfl\n"                        # 22
        "end Foo\n"                                                            # 23
        "structure S where\n"                                                  # 24
        "  x : Nat\n"                                                          # 25
        "theorem uses : Foo.bar.baz 1 = Foo.bar.baz 1 := by\n"                 # 26
        "  rw [Foo.f]; exact (top 1).symm\n"                                   # 27
    )
    check("lean decls", _names(lean, "lean"), [
        ("Foo.bar.baz", "theorem", 5, 9), ("Foo.f", "def", 11, 13), (None, "instance", 14, 14),
        ("Foo.instFoo", "instance", 15, 16), ("Foo.m1", "theorem", 18, 18), ("Foo.m2", "theorem", 19, 19),
        ("top", "theorem", 21, 22), ("S", "structure", 24, 25), ("uses", "theorem", 26, 27)])
    t = file_table(lean, "lean")
    d = t["decls"][0]
    check("lean stmt/body split", (d["stmt_lines"], d["body_lines"]), ([6, 7], [7, 9]))
    check("lean pattern-matching body", t["decls"][1]["body_lines"], [12, 13])
    check("lean structure has no body", t["decls"][7]["body_lines"], None)
    check("lean flags", d["flags"], ["private", "attr"])
    m = decl_mentions(t, t["decls"][-1])
    check("lean mention in statement", m.get("Foo.bar.baz", [0])[0], 2)
    check("lean mention in body", (m.get("Foo.f", [0, 0, 0])[2], m.get("top", [0, 0, 0])[2]), (1, 1))
    check("lean string is masked", "inside" in decl_mentions(t, d), False)
    hard, soft, types = lean_bound("theorem a (x y : Nat) {z : Foo.Bar n} : ∀ w, P := by\n intro u v\n"
                                   " obtain ⟨p, hp⟩ := foo\n have hq : Q :=\n   bar (lem x : R)\n rcases h with ⟨r, s⟩ | t\n")
    check("lean bound", (sorted(hard), sorted(soft), types),
          (["hp", "p", "r", "s", "t", "u", "v", "w", "x", "y", "z"], ["hq"], {"x": "Nat", "y": "Nat", "z": "Foo.Bar"}))
    field = ("structure A where\n  n : Nat\nstructure B where\n  n : Nat\ndef A.size (a : A) : Nat := a.n\n"
             "def B.size (b : B) : Nat := b.n\nvariable (v : B)\ntheorem t1 (a : A) : a.size = a.size := rfl\n"
             "theorem t2 : v.size = v.size := rfl\ntheorem t3 (h : True) : h.size = 0 := sorry\n"
             "theorem t4 (α : Type) (h : α) : h.size = 0 := sorry\ntheorem t5 (a : A) : a.n = (A.mk 0).n := rfl\n"
             "theorem t6 : True :=\n  trivial\n")
    R = Resolver([("F.lean", file_table(field, "lean"))])
    by = {d["name"]: g for g, (_, d, _) in enumerate(R.items)}
    names = lambda g, tok: sorted(R.items[x[0]][1]["name"] for x in R.resolve(g, tok)[0])
    check("lean field by binder type", names(by["t1"], "a.size"), ["A.size"])
    check("lean field by variable type", names(by["t2"], "v.size"), ["B.size"])
    check("lean field ruled out by a named type", names(by["t3"], "h.size"), [])
    check("lean field undecided", names(by["t4"], "h.size"), ["A.size", "B.size"])
    check("lean structure field", names(by["t5"], "a.n"), ["A"])
    check("lean structure constructor", names(by["t5"], "A.mk"), ["A"])
    ft = file_table(field, "lean")
    check("lean provides", sorted(next(d for d in ft["decls"] if d["name"] == "A")["provides"].items()),
          [("A.mk", "constructor"), ("A.n", "field")])
    check("lean provides, parents and arms",
          [sorted(d["provides"]) for d in file_table(
              "structure S (X Y : Type) extends X ≃ Y, Foo.Bar X where\n  c ::\n  (p q : Nat)\n"
              "inductive E | a | b\ninductive T\n  | leaf\n  | node (l r : T) : T\n", "lean")["decls"]],
          [["S.c", "S.p", "S.q", "S.toBar"], ["E.a", "E.b"], ["T.leaf", "T.node"]])
    m6 = decl_mentions(ft, next(d for d in ft["decls"] if d["name"] == "t6"))
    check("lean word at line start before any `by` is a term", m6.get("trivial", [0, 0, 0, 0, True])[4], False)
    shadow = ("theorem key : True := trivial\ntheorem user (h : True) : True := by\n  have key : True :=\n"
              "    key\n  exact key\n")
    t2 = file_table(shadow, "lean")
    check("lean soft binding", decl_mentions(t2, t2["decls"][1]).get("key"), [0, -1, 1, shadow.index("    key") + 4, True])
    lean3 = ("namespace a\nlemma l1 : true :=\nbegin\n  trivial\nend\n\n"
             "theorem l2 : true :=\nbegin\n  exact l1\nend\nend a\ndef d := 1\n")
    check("lean3 begin/end", _names(lean3, "lean"),
          [("a.l1", "lemma", 2, 5), ("a.l2", "theorem", 7, 10), ("d", "def", 12, 12)])
    check("lean3 dialect", file_table(lean3, "lean")["dialect"], "lean3")

    # ---------------------------------------------------------------- Rocq
    rocq = (
        "(* Lemma fake : True. (* nested *) Proof. Qed. *)\n"                 # 1
        "Module M.\n"                                                          # 2
        "Section S.\n"                                                         # 3
        "Variables (n : nat) (m k : nat).\n"                                   # 4
        "Hypothesis H : n = m.\n"                                              # 5
        "Definition d (x : nat) : nat := x + n.\n"                             # 6
        "Lemma l1 : d 0 = n.\n"                                                # 7
        "Proof. unfold d. (* \"*)\" *) reflexivity. Qed.\n"                    # 8
        "Definition d2 : nat.\n"                                               # 9
        "Proof. exact (d 1). Defined.\n"                                       # 10
        "#[local] Instance inst : Foo nat := {| f := d |}.\n"                  # 11
        "Lemma l2 : True. exact I. Qed.\n"                                     # 12
        "Inductive t : Type := | A : t | B (x : nat) : t\n"                    # 13
        "with u : Type := C : u.\n"                                            # 14
        "Fixpoint ev (x : nat) : bool := match x with 0 => true | S y => od y end\n"   # 15
        "with od (x : nat) : bool := match x with 0 => false | S y => ev y end.\n"     # 16
        "Record r := mk { fa : nat; fb : bool }.\n"                            # 17
        "Notation \"x +++ y\" := (d x) (at level 50).\n"                       # 18
        "Lemma l3 : forall x, d x = x + n.\n"                                  # 19
        "Proof using H. intros x. apply l1... Qed.\n"                          # 20
        "End S.\n"                                                             # 21
        "End M.\n"                                                             # 22
        "Theorem t1 : M.d 0 0 = 0. Proof. Admitted.\n"                         # 23
    )
    check("rocq decls", _names(rocq, "rocq"), [
        ("M.n", "Variables", 4, 4), ("M.m", "Variables", 4, 4), ("M.k", "Variables", 4, 4),
        ("M.H", "Hypothesis", 5, 5), ("M.d", "Definition", 6, 6), ("M.l1", "Lemma", 7, 8),
        ("M.d2", "Definition", 9, 10), ("M.inst", "Instance", 11, 11), ("M.l2", "Lemma", 12, 12),
        ("M.t", "Inductive", 13, 14), ("M.ev", "Fixpoint", 15, 16), ("M.r", "Record", 17, 17),
        ("M.l3", "Lemma", 19, 20), ("t1", "Theorem", 23, 23)])
    t = file_table(rocq, "rocq")
    by = {d["name"]: d for d in t["decls"]}
    check("rocq stmt/body", (by["M.l1"]["stmt_lines"], by["M.l1"]["body_lines"]), ([7, 7], [8, 8]))
    check("rocq Defined body", by["M.d2"]["body_lines"], [10, 10])
    check("rocq provides", (by["M.t"]["provides"], by["M.ev"]["provides"], by["M.r"]["provides"]),
          ({"A": "constructor", "B": "constructor", "u": "mutual", "C": "constructor"}, {"od": "mutual"},
           {"mk": "constructor", "fa": "field", "fb": "field"}))
    check("rocq no anomalies", t["anomalies"], [])
    check("rocq comment with string", "reflexivity" in decl_mentions(t, by["M.l1"]), True)
    hard, soft = rocq_bound("Lemma a (x y : T) : forall z, P.\nProof.\n intros u v. destruct u as [p q].\n"
                            " move=> /view a b. set (w := foo). have hh : Q by apply bar.\n"
                            " exists c. apply (lem : R). pose proof (foo a) as foo.\n", 7)
    check("rocq bound", (sorted(hard), sorted(soft)), (["a", "b", "u", "v", "x", "y", "z"], ["foo", "hh", "p", "q", "w"]))

    # ---------------------------------------------------------------- Isabelle
    isa = (
        "theory T imports Main begin\n"                                            # 1
        "(* lemma fake: \"True\" (* nested *) by simp *)\n"                        # 2
        "text \\<open>lemma in_text: here\\<close>\n"                              # 3
        "definition foo :: \"nat \\<Rightarrow> nat\" where \"foo x = x\"\n"       # 4
        "fun bar :: \"nat \\<Rightarrow> nat\" where\n"                            # 5
        "  \"bar 0 = 0\"\n"                                                        # 6
        "| \"bar (Suc n) = foo n\"\n"                                              # 7
        "lemma bar [simp]: \"bar 0 = 0\" by simp\n"                                # 8
        "lemma\n"                                                                  # 9
        "  assumes a: \"x = foo y\"\n"                                             # 10
        "  shows b: \"x = y\"\n"                                                   # 11
        "  using a unfolding foo_def by (simp add: bar.simps)\n"                   # 12
        "locale loc = fixes f :: \"nat \\<Rightarrow> nat\" assumes ax: \"f 0 = 0\"\n"  # 13
        "begin\n"                                                                  # 14
        "lemma \\<alpha>_l: \"f 0 = 0\"\n"                                         # 15
        "proof -\n"                                                                # 16
        "  show ?thesis by (rule ax)\n"                                            # 17
        "qed\n"                                                                    # 18
        "end\n"                                                                    # 19
        "lemma (in loc) l2: \"f 0 = 0\" \\<comment> \\<open>lemma no: x\\<close>\n"  # 20
        "  by (rule \\<alpha>_l)\n"                                                # 21
        "datatype 'a tr = Leaf | Node \"'a tr\" 'a\n"                              # 22
        "interpretation I: loc \"\\<lambda>x. x\" by unfold_locales simp\n"        # 23
        "lemmas both = bar I.l2\n"                                                 # 24
        "end\n"                                                                    # 25
    )
    check("isabelle decls", _names(isa, "isabelle"), [
        ("foo", "definition", 4, 4), ("bar", "fun", 5, 7), ("bar", "lemma", 8, 8), (None, "lemma", 9, 12),
        ("loc", "locale", 13, 13), ("loc.\\<alpha>_l", "lemma", 15, 18), ("loc.l2", "lemma", 20, 21),
        ("tr", "datatype", 22, 22), ("I", "interpretation", 23, 23), ("both", "lemmas", 24, 24)])
    t = file_table(isa, "isabelle")
    d = t["decls"][3]
    check("isabelle assumes/shows split", (d["stmt_lines"], d["body_lines"]), ([9, 11], [12, 12]))
    check("isabelle shows-name", d["provides"], {"b": "shows-name"})
    check("isabelle namespaces", [x["ns"] for x in t["decls"][:5]], ["t", "t", "f", "f", "b"])
    check("isabelle constructors", t["decls"][7]["provides"], {"Leaf": "constructor", "Node": "constructor"})
    check("isabelle locale assumption", t["decls"][4]["provides"], {"loc.ax": "assumption"})
    check("isabelle interpretation", t["interps"], {"I": "loc"})
    m = decl_mentions(t, d)
    check("isabelle channels", (m.get("ifoo", [0])[0], m.get("ofoo_def", [0, 0, 0])[2], m.get("obar.simps", [0, 0, 0])[2]),
          (1, 1, 1))
    check("isabelle document text is masked", "oin_text" in decl_mentions(t, t["decls"][0]), False)
    # ---------------------------------------------------------------- resolver
    def targets(text, lang, user, tok, path="F.x"):
        R = Resolver([(path, file_table(text, lang))])
        g = [k for k, (_, d, _) in enumerate(R.items) if d["name"] == user][0]
        return sorted((R.items[x[0]][1]["name"], x[1], x[2]) for x in R.resolve(g, tok)[0])

    lean_r = ("namespace A\ntheorem base : True := trivial\ntheorem later_user : True := later\n"
              "theorem later : True := base\nend A\nopen A in\ntheorem out1 : True := base\n"
              "theorem out2 (ext : Nat) : True := by\n  ext x\n  exact _root_.A.base\n")
    check("lean scoped", targets(lean_r, "lean", "A.later", "base"), [("A.base", "scoped", None)])
    check("lean no forward reference", targets(lean_r, "lean", "A.later_user", "later"), [])
    check("lean opened", targets(lean_r, "lean", "out1", "base"), [("A.base", "opened", None)])
    check("lean _root_", targets(lean_r, "lean", "out2", "_root_.A.base"), [("A.base", "exact", None)])
    check("lean bound name is not a mention", targets(lean_r, "lean", "out2", "ext"), [])
    rocq_r = ("Module M.\nLemma l : True. Proof. exact I. Qed.\nEnd M.\nModule N := M.\n"
              "Section S.\nVariable v : nat.\nNotation w := v.\nLemma in_s : v = v. Proof. reflexivity. Qed.\nEnd S.\n"
              "Lemma dead : False. Proof. Abort.\nLemma dead : True. Proof. exact I. Qed.\n"
              "Lemma user (v : nat) : True. Proof. set q := w. apply N.l. apply l. exact dead. Qed.\n")
    check("rocq module alias", targets(rocq_r, "rocq", "user", "N.l"), [("M.l", "exact", "module-alias")])
    check("rocq name in a module not opened", targets(rocq_r, "rocq", "user", "l"), [("M.l", "suffix", None)])
    check("rocq section variable in scope", targets(rocq_r, "rocq", "in_s", "v"), [("v", "exact", None)])
    check("rocq section notation out of scope", targets(rocq_r, "rocq", "user", "w"), [])
    tr = file_table(rocq_r, "rocq")
    check("rocq Abort", [("aborted" in d["flags"]) for d in tr["decls"] if d["name"] == "dead"], [True, False])
    isa_r = ("theory T imports Main begin\ndatatype st = Idle | Busy nat\nrecord conf =\n  st :: \"st\"\n"
             "locale base = fixes f :: nat assumes pos: \"f > 0\"\nbegin\nlemma in_base: \"f > 0\" by (rule pos)\nend\n"
             "locale ext = base + fixes g :: nat\nbegin\nlemma in_ext: \"f > 0\" by (rule in_base)\nend\n"
             "lemma user: \"st c = Idle\"\nproof (cases x)\n  case (Busy n)\n  fix y :: \"st\"\n"
             "  show ?thesis by (simp add: st.split in_base)\nqed\nend\n")
    check("isabelle locale parent", targets(isa_r, "isabelle", "ext.in_ext", "oin_base"), [("base.in_base", "scoped", None)])
    check("isabelle fact outside its locale", targets(isa_r, "isabelle", "user", "oin_base"), [("base.in_base", "suffix", None)])
    check("isabelle field in a term", targets(isa_r, "isabelle", "user", "ist"), [("conf", "exact", "field")])
    check("isabelle type name in a type", targets(isa_r, "isabelle", "user", "yst"), [("st", "exact", None)])
    check("isabelle t.split", targets(isa_r, "isabelle", "user", "ost.split"), [("st", "exact", "qualified")])
    check("isabelle case name", targets(isa_r, "isabelle", "user", "cBusy"), [("st", "exact", "constructor")])
    tu = file_table(isa_r, "isabelle")
    check("isabelle channels y and c", sorted(k for k in decl_mentions(tu, tu["decls"][-1]) if k[0] in "yc"), ["cBusy", "yst"])

    f, tm = isabelle_bound("lemma assumes a: \"P\" shows \"Q\"\nproof -\n fix x y\n obtain z where hz: \"R\" sorry\n"
                           " have step[simp]: \"S\" sorry\n note n1 = hz\nqed\n", "\\<forall>u v. P u v")
    check("isabelle bound", (sorted(f), sorted(tm)), (["a", "hz", "n1", "step"], ["u", "v", "x", "y", "z"]))
    return fails
