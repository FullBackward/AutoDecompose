"""Lexers, statement parser and proof-step reader for feature_terms.py.

Standard library only. Self-contained: nothing here imports another library
tool. Everything in this module is syntactic (tier T1): it reads characters
and tokens, never elaborated terms. Where the text does not decide a question
the functions return None with a reason code; they do not guess silently.

Three languages are handled: lean (Lean 4, and Lean 3 `begin ... end`
blocks), rocq (Gallina with Ltac and SSReflect proofs), isabelle (Isar outer
syntax with HOL inner syntax). Isabelle symbols `\\<name>` are opaque tokens
named by their name; the only names given a meaning are the short lists
ISA_* below (connectives, binders, relations, bracket pairs). No symbol table
and no mapping to Unicode is used.
"""
from __future__ import annotations

import bisect
import re
import unicodedata

LEX_VERSION = "1.0.0"

PROVER_LANGS = ("lean", "rocq", "isabelle")


# ===================================================================== tokens

class Tok:
    """One token. k: id num str sym open close inner scope dot tvar ctl.
    depth is the bracket depth outside the token; first marks the first token of a line."""
    __slots__ = ("k", "t", "line", "col", "depth", "first", "pos")

    def __init__(self, k, t, line, col, pos):
        self.k, self.t, self.line, self.col, self.pos = k, t, line, col, pos
        self.depth, self.first = 0, False

    def __repr__(self):
        return f"{self.k}:{self.t}@{self.line}:{self.col}/{self.depth}"


class _Pos:
    """Offset -> (line, column), both counted from the start of the text given."""

    def __init__(self, text):
        self.starts = [0]
        for m in re.finditer("\n", text):
            self.starts.append(m.end())

    def at(self, pos):
        i = bisect.bisect_right(self.starts, pos) - 1
        return i + 1, pos - self.starts[i]


# ------------------------------------------------------------------ comments

def blank_comments(text, lang):
    """Replace comments by spaces. Offsets, lines and columns are unchanged.

    lean: `--` to end of line and nested `/- -/` (doc comments included), outside strings.
    rocq: nested `(* *)`, outside strings.
    isabelle: nested `(* *)` outside strings and cartouches; `\\<comment> \\<open>..\\<close>`;
    `\\<^marker>\\<open>..\\<close>`; `-- "text"`; and the cartouche or string argument of the document
    commands text, txt, text_raw, chapter, section, subsection, subsubsection, paragraph.
    """
    out = list(text)
    n = len(text)

    def wipe(a, b):
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    def block_end(j, opener, closer):
        depth = 1
        while j < n and depth:
            if text.startswith(opener, j):
                depth, j = depth + 1, j + len(opener)
            elif text.startswith(closer, j):
                depth, j = depth - 1, j + len(closer)
            else:
                j += 1
        return j

    i = 0
    if lang == "lean":
        while i < n:
            c = text[i]
            if c == '"':
                j = i + 1
                while j < n and text[j] != '"':
                    j += 2 if text[j] == "\\" else 1
                i = j + 1
            elif text.startswith("--", i):
                j = text.find("\n", i)
                j = n if j < 0 else j
                wipe(i, j)
                i = j
            elif text.startswith("/-", i):
                j = block_end(i + 2, "/-", "-/")
                wipe(i, j)
                i = j
            else:
                i += 1
    elif lang == "rocq":
        while i < n:
            c = text[i]
            if c == '"':
                j = i + 1
                while j < n:
                    if text[j] == '"':
                        if j + 1 < n and text[j + 1] == '"':
                            j += 2
                            continue
                        break
                    j += 1
                i = j + 1
            elif text.startswith("(*", i) and not text.startswith("(*)", i):
                j = block_end(i + 2, "(*", "*)")
                wipe(i, j)
                i = j
            else:
                i += 1
    elif lang == "isabelle":
        doc = re.compile(r"(?m)^[ \t]*(?:text|txt|text_raw|chapter|section|subsection|subsubsection|paragraph"
                         r"|subparagraph)\b[ \t]*(?:\([^)\n]*\)[ \t]*)?")

        def cartouche_end(j):
            depth = 0
            while j < n:
                if text.startswith("\\<open>", j):
                    depth, j = depth + 1, j + 7
                elif text.startswith("\\<close>", j):
                    depth, j = depth - 1, j + 8
                    if depth == 0:
                        return j
                else:
                    j += 1
            return n

        def string_end(j):
            j += 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" and not text.startswith("\\<", j) else 1
            return min(n, j + 1)

        doc_at = {m.end(): m.start() for m in doc.finditer(text)}
        while i < n:
            if i in doc_at:
                j = i
                while j < n and text[j] in " \t\n":
                    j += 1
                if text.startswith("\\<open>", j):
                    e = cartouche_end(j)
                    wipe(doc_at[i], e)
                    i = e
                    continue
                if j < n and text[j] == '"':
                    e = string_end(j)
                    wipe(doc_at[i], e)
                    i = e
                    continue
            c = text[i]
            if c == '"':
                i = string_end(i)
            elif text.startswith("\\<comment>", i) or text.startswith("\\<^marker>", i):
                j = text.find(">", i) + 1
                k = j
                while k < n and text[k] in " \t\n":
                    k += 1
                if text.startswith("\\<open>", k):
                    e = cartouche_end(k)
                    wipe(i, e)
                    i = e
                else:
                    i = j
            elif text.startswith("\\<open>", i):
                i = cartouche_end(i)
            elif text.startswith("(*", i) and not text.startswith("(*)", i):
                j = block_end(i + 2, "(*", "*)")
                wipe(i, j)
                i = j
            elif text.startswith("--", i) and re.match(r'--[ \t]*"', text[i:i + 12]):
                e = string_end(text.find('"', i))
                wipe(i, e)
                i = e
            else:
                i += 1
    return "".join(out)


# -------------------------------------------------------------------- lexers

_DIGITS = "0123456789"
_SUBSCRIPT_DIGITS = "₀₁₂₃₄₅₆₇₈₉"
_LEAN_NOT_IDENT = "λᶜᵀᵒᵖˣᵐᵈᴴ"          # letters by Unicode category, operators in Lean text
LEAN_OPEN = "([{⟨⦃⟦⟪‹⌊⌈"
LEAN_CLOSE = ")]}⟩⦄⟧⟫›⌋⌉"
_LEAN_OPS = sorted(["<;>", ":=", "=>", "->", "<-", "<->", "<=", ">=", "!=", "==", "&&", "||", "::", "++", "|>.",
                    "|>", "<|", "<$>", ">>=", "...", "..", "^^", "/\\", "\\/", "<:", "⁻¹", "×ˢ"],
                   key=lambda s: (-len(s), s))


def _lean_idstart(ch):
    return (ch.isalpha() and ch not in _LEAN_NOT_IDENT) or ch == "_"


def _lean_idrest(ch):
    return (ch.isalpha() and ch not in _LEAN_NOT_IDENT) or ch in "_'" or ch in _DIGITS \
        or ch in _SUBSCRIPT_DIGITS or unicodedata.category(ch) == "Mn"


# subscript letters and digits that attach to a preceding operator character: `∈ᵢ`, `‖ₑ`, `→ₗ`, `≃ₐ`
_LEAN_OP_SUFFIX = "₀₁₂₃₄₅₆₇₈₉ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓ₊₋"
_LEAN_HOM = "→≃↪↠≅"                      # followed at once by * or +: a bundled-map arrow such as `→*`, `≃+*`


def lex_lean(text):
    P, toks, i, n = _Pos(text), [], 0, len(text)

    def add(k, a, b):
        line, col = P.at(a)
        toks.append(Tok(k, text[a:b], line, col, a))

    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            add("str", i, min(n, j + 1))
            i = j + 1
        elif c == "'" and re.match(r"'(?:\\.|[^\\'\n])'", text[i:i + 4]) and not (i and _lean_idrest(text[i - 1])):
            j = i + (4 if text[i + 1] == "\\" else 3)
            add("str", i, j)
            i = j
        elif c in _DIGITS:
            j = i
            if text.startswith(("0x", "0X"), i):
                j = i + 2
                while j < n and text[j] in "0123456789abcdefABCDEF":
                    j += 1
            else:
                while j < n and text[j] in _DIGITS:
                    j += 1
                if j + 1 < n and text[j] == "." and text[j + 1] in _DIGITS:
                    j += 1
                    while j < n and text[j] in _DIGITS:
                        j += 1
            add("num", i, j)
            i = j
        elif _lean_idstart(c) or c == "«" or (
                c == "." and i + 1 < n and (_lean_idstart(text[i + 1]) or text[i + 1] == "«")
                and not (i and text[i - 1] == ".")):
            j = i + 1 if c == "." else i
            while True:
                if j < n and text[j] == "«":
                    k = text.find("»", j)
                    j = n if k < 0 else k + 1
                else:
                    while j < n and _lean_idrest(text[j]):
                        j += 1
                    while j < n and text[j] in "!?" and not (j + 1 < n and text[j + 1] == "="):
                        j += 1
                if j + 1 < n and text[j] == "." and (_lean_idstart(text[j + 1]) or text[j + 1] == "«"):
                    j += 1
                    continue
                if j + 1 < n and text[j] == "." and text[j + 1] in _DIGITS:
                    j += 1
                    while j < n and text[j] in _DIGITS:
                        j += 1
                    continue
                if text.startswith(".{", j):                 # universe arguments `Foo.{u, v}`
                    k = text.find("}", j)
                    j = n if k < 0 else k + 1
                break
            if text[i:j] == "ℕ" and text.startswith("+", j) and not (j + 1 < n and (text[j + 1].isalnum()
                                                                               or text[j + 1] == "(")):
                j += 1                                       # `ℕ+`, the positive naturals
            elif text[i:j] == "ℝ" and text.startswith("≥0", j):
                j += 3 if text.startswith("≥0∞", j) else 2   # `ℝ≥0`, `ℝ≥0∞`
            add("id", i, j)
            i = j
        elif c == "." and i + 1 < n and text[i + 1] in _DIGITS and i and text[i - 1] in LEAN_CLOSE:
            j = i + 1                                        # projection after a bracket: `(f x).2`
            while j < n and text[j] in _DIGITS:
                j += 1
            add("id", i, j)
            i = j
        elif c in LEAN_OPEN:
            add("open", i, i + 1)
            i += 1
        elif c in LEAN_CLOSE:
            add("close", i, i + 1)
            i += 1
        elif text.startswith(("=O[", "=o[", "=Θ["), i):
            add("sym", i, i + 2)
            i += 2
        elif text.startswith(("∃!", "∑'", "∏'", "∫⁻"), i):
            add("sym", i, i + 2)
            i += 2
        else:
            for op in _LEAN_OPS:
                if text.startswith(op, i):
                    j = i + len(op)
                    break
            else:
                j = i + 1
                if c in _LEAN_HOM:
                    while j < n and text[j] in "*+":
                        j += 1
                if not c.isascii():
                    while j < n and text[j] in _LEAN_OP_SUFFIX:
                        j += 1
            add("sym", i, j)
            i = j
    return _finish(toks)


_ROCQ_SYMCH = set("!#$%&*+-/<=>?@\\^|~:")
_ROCQ_COLON_OPS = {":=", "::", ":>", ":>>", "*:", "%:", ":&:", ":|:", ":\\:", ":==:", ":!=:", ":*:", ":+:",
                   ":<=:", ":<:", "<:", ":=:", ":~:", "<:<", ":-:", "::="}


def lex_rocq(text):
    P, toks, i, n = _Pos(text), [], 0, len(text)

    def add(k, a, b, t=None):
        line, col = P.at(a)
        toks.append(Tok(k, text[a:b] if t is None else t, line, col, a))

    def idstart(ch):
        return (ch.isalpha() and ch != "λ") or ch == "_"

    def idrest(ch):
        return (ch.isalpha() and ch != "λ") or ch in "_'" or ch in _DIGITS or ch in _SUBSCRIPT_DIGITS

    while i < n:
        c = text[i]
        prev = text[i - 1] if i else " "
        if c.isspace():
            i += 1
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            add("str", i, min(n, j + 1))
            i = j + 1
        elif c in _DIGITS:
            j = i
            while j < n and text[j] in _DIGITS:
                j += 1
            add("num", i, j)
            i = j
        elif idstart(c) or (c == "'" and i + 1 < n and text[i + 1].isalpha()
                            and not (idrest(prev) or prev in ")]}")):
            j = i + 1
            while True:
                while j < n and idrest(text[j]):
                    j += 1
                if j + 1 < n and text[j] == "." and idstart(text[j + 1]) and c != "'":
                    j += 1
                    continue
                break
            if text[i:j] == "ltac" and text.startswith(":", j) and not text.startswith(":=", j):
                j += 1                                       # `ltac:(...)`
            add("id", i, j)
            i = j
        elif c == "<" and re.match(r"<-[A-Za-z]{1,3}->", text[i:i + 8]):
            j = i + re.match(r"<-[A-Za-z]{1,3}->", text[i:i + 8]).end()
            add("sym", i, j)                                 # an operator with an embedded tag: `<-T->`
            i = j
        elif c == "%" and i + 1 < n and not prev.isspace() and (
                text[i + 1].isalpha()
                or (text[i + 1] == ":" and i + 2 < n and (text[i + 2].isalpha() or text[i + 2] == "~"))):
            j = i + 1
            if text[j] == ":":
                j += 1
                if j < n and text[j] == "~":
                    j += 1
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            add("scope", i, j)
            i = j
        elif c == "\\" and i + 1 < n and text[i + 1].isalpha():
            j = i + 1
            while j < n and (text[j].isalpha() or text[j] == "_"):
                j += 1
            add("sym", i, j)
            i = j
        elif c == "`" and i + 1 < n and text[i + 1] in "({":
            add("open", i, i + 2)
            i += 2
        elif text.startswith("{|", i):
            add("open", i, i + 2)
            i += 2
        elif text.startswith("|}", i):
            add("close", i, i + 2)
            i += 2
        elif c == "[" and re.match(r"\[[-+*/<=>#~]{1,3}\]", text[i:i + 5]):
            j = text.index("]", i) + 1
            add("sym", i, j)
            i = j
        elif c in "([{":
            add("open", i, i + 1)
            i += 1
        elif c in ")]}":
            add("close", i, i + 1)
            i += 1
        elif c == ".":
            if text.startswith("...", i) and (i + 3 >= n or text[i + 3].isspace()):
                add("dot", i, i + 3, ".")
                i += 3
            elif i + 1 >= n or text[i + 1].isspace():
                add("dot", i, i + 1)
                i += 1
            elif text.startswith("..", i):
                add("sym", i, i + 2)
                i += 2
            elif re.match(r"\.[-+*][0-9]", text[i:i + 3]):
                add("sym", i, i + 3)
                i += 3
            elif text[i + 1] in _DIGITS:
                add("sym", i, i + 2)
                i += 2
            else:
                add("sym", i, i + 1)
                i += 1
        elif c == "=" and re.match(r"=[12i]\s", text[i:i + 3]) and prev.isspace():
            add("sym", i, i + 2)
            i += 2
        elif c in _ROCQ_SYMCH:
            j = i
            while j < n and text[j] in _ROCQ_SYMCH:
                j += 1
            run = text[i:j]
            if ":" in run and run not in _ROCQ_COLON_OPS:
                k = i
                for part in re.findall(r":=|::|:|[^:]+", run):
                    add("sym", k, k + len(part))
                    k += len(part)
            else:
                add("sym", i, j)
            i = j
        else:
            add("sym", i, i + 1)
            i += 1
    return _finish(toks)


# Isabelle symbols given a meaning, keyed by name. Everything else is opaque.
ISA_OPEN = {"lbrakk", "lbrace", "langle", "lparr", "lceil", "lfloor", "guillemotleft", "lblot"}
ISA_CLOSE = {"rbrakk", "rbrace", "rangle", "rparr", "rceil", "rfloor", "guillemotright", "rblot"}
_ISA_SYM = re.compile(r"\\<(\^?[A-Za-z_][A-Za-z0-9_]*)>")
_ISA_OPS = ("\\<Longrightarrow>", "==>", "-->", "<->", "<..<", "<..", "..<", "..", "::", "=>", "<=", ">=", "~=",
            "!!", "\\/", "/\\")


def lex_isabelle(text, inner=False):
    """Outer syntax when inner is False: strings and cartouches become one `inner` token each.
    Inner syntax when inner is True: the content of such a token."""
    P, toks, i, n = _Pos(text), [], 0, len(text)

    def add(k, a, b):
        line, col = P.at(a)
        toks.append(Tok(k, text[a:b], line, col, a))

    def absorb_sub(j):
        """Position after any `\\<^sub>X` runs that follow j (X one character or one symbol)."""
        while text.startswith(("\\<^sub>", "\\<^bsub>"), j):
            if text.startswith("\\<^bsub>", j):
                e = text.find("\\<^esub>", j)
                j = n if e < 0 else e + 8
                continue
            j += 7
            m = _ISA_SYM.match(text, j)
            j = m.end() if m else min(n, j + 1)
        return j

    def idrest(ch):
        return ch.isalnum() or ch in "_'"

    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if not inner and text.startswith("\\<open>", i):
            depth, j = 0, i
            while j < n:
                if text.startswith("\\<open>", j):
                    depth, j = depth + 1, j + 7
                elif text.startswith("\\<close>", j):
                    depth, j = depth - 1, j + 8
                    if depth == 0:
                        break
                else:
                    j += 1
            body_end = j - 8 if depth == 0 and text.startswith("\\<close>", j - 8) else j
            line, col = P.at(i + 7)
            toks.append(Tok("inner", text[i + 7:body_end], line, col, i + 7))
            i = j
            continue
        if not inner and c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" and not text.startswith("\\<", j) else 1
            line, col = P.at(min(n, i + 1))
            toks.append(Tok("inner", text[i + 1:j], line, col, i + 1))
            i = j + 1
            continue
        m = _ISA_SYM.match(text, i)
        if m:
            name, j = m.group(1), m.end()
            if j < n and text[j] == "_" and not name.startswith("^"):
                # a symbol glued to an identifier by an underscore is part of that identifier
                while j < n:
                    mm = _ISA_SYM.match(text, j)
                    if mm and text[j - 1] == "_" and not mm.group(1).startswith("^"):
                        j = mm.end()
                    elif idrest(text[j]):
                        j += 1
                    else:
                        break
                j = absorb_sub(j)
                add("id", i, j)
            elif name in ISA_OPEN:
                add("open", i, j)
            elif name in ISA_CLOSE:
                add("close", i, j)
            elif name.startswith("^"):
                add("ctl", i, j)
            else:
                j = absorb_sub(j)
                while text.startswith("\\<^sup>", j):
                    j += 7
                    mm = _ISA_SYM.match(text, j)
                    j = absorb_sub(mm.end() if mm else min(n, j + 1))
                add("sym", i, j)
            i = j
            continue
        if c in _DIGITS:
            j = i
            while j < n and text[j] in _DIGITS:
                j += 1
            if j + 1 < n and text[j] == "." and text[j + 1] in _DIGITS:
                j += 1
                while j < n and text[j] in _DIGITS:
                    j += 1
            add("num", i, j)
            i = j
        elif c.isalpha() or (c == "?" and i + 1 < n and text[i + 1].isalpha()) \
                or (c == "_" and i + 1 < n and idrest(text[i + 1])):
            j = i + 1
            while True:
                while j < n and idrest(text[j]):
                    j += 1
                mm = _ISA_SYM.match(text, j)
                if mm and text[j - 1] == "_" and not mm.group(1).startswith("^"):
                    j = mm.end()
                    continue
                if j + 1 < n and text[j] == "." and text[j + 1].isalpha() and c != "?":
                    j += 1
                    continue
                mm = _ISA_SYM.match(text, j + 1) if j < n and text[j] == "." else None
                if mm and not mm.group(1).startswith("^") and c != "?":
                    j = mm.end()                             # a qualified name whose last part is a symbol: `D1.\<V>`
                    continue
                break
            j = absorb_sub(j)
            add("id", i, j)
            i = j
        elif c == "'" and i + 1 < n and text[i + 1].isalpha():
            j = i + 1
            while j < n and idrest(text[j]):
                j += 1
            add("tvar", i, j)
            i = j
        elif c in "([{":
            add("open", i, i + 1)
            i += 1
        elif c in ")]}":
            add("close", i, i + 1)
            i += 1
        else:
            for op in _ISA_OPS:
                if text.startswith(op, i):
                    add("sym", i, i + len(op))
                    i += len(op)
                    break
            else:
                add("sym", i, i + 1)
                i += 1
    return _finish(toks)


def _finish(toks):
    """Set depth and first-on-line flags. Unbalanced brackets never make depth negative."""
    depth, last_line = 0, -1
    for t in toks:
        if t.k == "close":
            depth = max(0, depth - 1)
            t.depth = depth
        else:
            t.depth = depth
            if t.k == "open":
                depth += 1
        t.first = t.line != last_line
        last_line = t.line
    return toks


def balanced(toks):
    depth = 0
    for t in toks:
        if t.k == "open":
            depth += 1
        elif t.k == "close":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def lex(text, lang, inner=False):
    if lang == "lean":
        return lex_lean(text)
    if lang == "rocq":
        return lex_rocq(text)
    if lang == "isabelle":
        return lex_isabelle(text, inner)
    raise ValueError(lang)


# ================================================================ term parser
#
# A term is parsed only as far as its logical layer: binders, connectives and
# the first relation. Everything below a relation side or an application is a
# leaf summarised by its head token. Precedence is the fixed order in
# TERM[lang]["levels"] (loosest first); notations declared by a project are
# not known, so a leaf with an unknown infix symbol is reported as `expr`.

def _isa_base(t):
    """`\\<le>\\<^sub>s` -> `\\<le>`; other texts unchanged."""
    return t[:t.index(">") + 1] if t.startswith("\\<") and ">" in t else t


_REL_COMMON = {"=": "eq", "<": "lt", ">": "gt", "<=": "le", ">=": "ge"}

TERM = {
    "lean": {
        "forall": {"∀", "Π"}, "meta_forall": set(), "exists": {"∃"}, "exuniq": {"∃!"}, "lam": {"fun", "λ"},
        "binder_sep": {","}, "lam_sep": {"=>", "↦", ","},
        "ops": {"↔": "iff", "<->": "iff", "→": "arrow", "->": "arrow", "∨": "or", "\\/": "or",
                "∧": "and", "/\\": "and"},
        "levels": ("iff", "arrow", "or", "and"),
        "neg": {"¬"},
        "rel": dict(_REL_COMMON, **{
            "≠": "ne", "!=": "ne", "==": "eq", "≤": "le", "≥": "ge", "∈": "mem", "∉": "notmem", "⊆": "subset",
            "⊂": "subset", "⊇": "subset", "⊃": "subset", "∣": "dvd", "≡": "equiv", "≃": "equiv", "≅": "equiv",
            "≈": "equiv", "∼": "equiv", "=O": "asymp", "=o": "asymp", "=Θ": "asymp", "⊢": "entails",
            "⊧": "entails", "⊨": "entails", "⊭": "entails", "≼": "le", "≺": "lt", "⊑": "le", "⊏": "lt"}),
        "capture": {"if", "let", "match", "have", "show", "by", "do", "calc", "suffices"},
        "bigop": {"∑", "∏", "∑'", "∏'", "∫", "∫⁻", "⨆", "⨅", "⋃", "⋂", "⨁", "⨂", "⨍", "∮", "∐"},
        "bigop_binds": False,
        "colon": ":",
        "kw": {"fun", "λ", "let", "have", "show", "from", "if", "then", "else", "match", "with", "do", "by", "in",
               "at", "forall", "theorem", "lemma", "def", "where", "end", "instance", "class", "structure",
               "inductive", "private", "protected", "noncomputable", "nonrec", "abbrev", "example", "calc",
               "suffices", "obtain", "using", "this", "_", "problem", "deriving", "extends", "MOD", "PMOD", "ZMOD"},
        "sorts": {"Type", "Prop", "Sort"},
    },
    "rocq": {
        "forall": {"forall", "∀", "∏"}, "meta_forall": set(), "exists": {"exists", "∃", "exists2", "∑"},
        "exuniq": {"∃!"}, "lam": {"fun", "λ"},
        "binder_sep": {","}, "lam_sep": {"=>"},
        "ops": {"->": "arrow", "→": "arrow", "⇒": "arrow", "==>": "arrow", "<->": "iff", "↔": "iff",
                "\\/": "or", "∨": "or", "||": "or", "/\\": "and", "∧": "and", "&&": "and"},
        "levels": ("arrow", "iff", "or", "and"),
        "neg": {"~", "¬", "~~"},
        "rel": dict(_REL_COMMON, **{
            "<>": "ne", "≠": "ne", "!=": "ne", "==": "eq", "=1": "eq", "=2": "eq", "=i": "eq", "≤": "le",
            "≥": "ge", "\\in": "mem", "\\notin": "notmem", "\\subset": "subset", "\\proper": "subset",
            "\\is": "mem", "%|": "dvd", "≡": "equiv", "\\isog": "equiv", "[<=]": "le", "[<]": "lt", "[=]": "eq",
            "[#]": "ne", "<|": "other", "⇓": "other", "⊢": "entails", "⊧": "entails"}),
        "capture": {"let", "if", "match", "fix", "cofix"},
        "bigop": {"\\sum_", "\\prod_", "\\big", "\\bigcup_", "\\bigcap_", "\\max_", "\\min_", "\\int", "\\sum",
                  "\\prod", "\\bigcup", "\\bigcap", "\\big_", "\\int_", "\\esssup", "\\bigoplus_"},
        "bigop_binds": False,
        "colon": ":",
        "kw": {"forall", "exists", "exists2", "fun", "let", "in", "if", "then", "else", "match", "with", "end",
               "as", "return", "fix", "cofix", "struct", "_", "λ", "at", "using", "ltac:"},
        "sorts": {"Type", "Prop", "Set", "SProp", "UU", "hProp", "hSet"},
    },
    "isabelle": {
        "forall": {"\\<forall>", "ALL"}, "meta_forall": {"\\<And>", "!!"}, "exists": {"\\<exists>", "EX", "\\<nexists>"},
        "exuniq": set(), "lam": {"\\<lambda>", "%"},
        "binder_sep": {"."}, "lam_sep": {"."},
        "ops": {"\\<Longrightarrow>": "marrow", "==>": "marrow", "\\<longrightarrow>": "arrow", "-->": "arrow",
                "\\<longleftrightarrow>": "iff", "\\<Longleftrightarrow>": "iff", "\\<leftrightarrow>": "iff",
                "<->": "iff", "\\<or>": "or", "\\<and>": "and", "&": "and"},
        "levels": ("marrow", "arrow", "iff", "or", "and"),
        "neg": {"\\<not>", "~"},
        "rel": dict(_REL_COMMON, **{
            "\\<noteq>": "ne", "~=": "ne", "\\<le>": "le", "\\<ge>": "ge", "\\<in>": "mem", "\\<notin>": "notmem",
            "\\<subseteq>": "subset", "\\<subset>": "subset", "\\<supseteq>": "subset", "\\<supset>": "subset",
            "dvd": "dvd", "\\<equiv>": "eq", "\\<approx>": "equiv", "\\<sim>": "equiv", "\\<cong>": "equiv",
            "\\<simeq>": "equiv", "\\<sqsubseteq>": "le", "\\<sqsubset>": "lt", "\\<preceq>": "le",
            "\\<prec>": "lt", "\\<turnstile>": "entails", "\\<Turnstile>": "entails", "\\<tturnstile>": "entails",
            "\\<TTurnstile>": "entails"}),
        "capture": {"let", "if", "case", "LEAST", "GREATEST", "SOME", "THE"},
        "bigop": {"\\<Sum>", "\\<Prod>", "\\<Union>", "\\<Inter>", "\\<Squnion>", "\\<Sqinter>", "\\<integral>",
                  "SUM", "PROD", "UN", "INT", "INF", "SUP"},
        "bigop_binds": True,
        "colon": "::",
        "kw": {"let", "in", "if", "then", "else", "case", "of", "ALL", "EX", "LEAST", "GREATEST", "SOME", "THE",
               "SUM", "PROD", "UN", "INT", "INF", "SUP", "_", "dvd", "div", "mod"},
        "sorts": set(),
    },
}

# One arithmetic table for all three languages: a larger number binds tighter. It is used only to name the
# head of an `expr` leaf, never to build structure. Real precedences differ in places; see terms.md.
ARITH = {"|>": 10, "<|": 10, "$": 10, "×": 35, "++": 65, "+": 65, "-": 65, "∪": 65, "⊔": 68, "::": 67, "⊓": 69,
         "*": 70, "/": 70, "%": 70, "∩": 70, "\\": 70, "•": 73, "^": 75, "∘": 90, "\\o": 90,
         "\\<union>": 65, "\\<inter>": 70, "\\<times>": 80, "\\<circ>": 55, "@": 65, "#": 65, "div": 70, "mod": 70,
         "*:": 70, "+:": 65, ".+1": 99, ".-1": 99, "⁻¹": 99, "!": 99}

MAX_NODES = 400
MAX_DEPTH = 60


def _norm(t, lang):
    return _isa_base(t.t) if lang == "isabelle" else t.t


def _base(toks):
    return min(t.depth for t in toks)


def _strip_parens(toks):
    """Drop a pair of round brackets that encloses the whole list, repeatedly."""
    while len(toks) >= 2 and toks[0].k == "open" and toks[0].t == "(" and toks[-1].k == "close" \
            and toks[-1].t == ")" and all(t.depth > toks[0].depth for t in toks[1:-1]):
        toks = toks[1:-1]
    return toks


def _is_group(toks):
    """The list is exactly one bracket group."""
    return len(toks) >= 2 and toks[0].k == "open" and toks[-1].k == "close" \
        and all(t.depth > toks[0].depth for t in toks[1:-1])


def _find(toks, texts, start=0, base=None, lang=None):
    """Index of the first token at depth `base` whose (normalised) text is in texts."""
    if not toks:
        return None
    base = _base(toks) if base is None else base
    for i in range(start, len(toks)):
        t = toks[i]
        if t.depth == base and t.k not in ("open", "close") and (_norm(t, lang) if lang else t.t) in texts:
            return i
    return None


def top_items(toks):
    """Split a list into top-level items: a bracket group is one item, any other token is one item."""
    out, i, n = [], 0, len(toks)
    if not toks:
        return out
    base = _base(toks)
    while i < n:
        t = toks[i]
        if t.k == "open" and t.depth == base:
            j = i + 1
            while j < n and not (toks[j].k == "close" and toks[j].depth == base):
                j += 1
            out.append(toks[i:j + 1])
            i = j + 1
        else:
            out.append([t])
            i += 1
    return out


def binder_names(toks, lang):
    """Names bound by a binder prefix (the tokens between the binder word and its separator).

    Returns (names, n_slots, bounded): `_` fills a slot without giving a name; bounded is True for
    forms such as `x ∈ S`, `i < n`. A bracket group with a colon gives the names before the colon; a
    group without one is a pattern and gives every identifier inside it.
    """
    cfg = TERM[lang]
    names, slots, bounded = [], 0, False
    for item in top_items(toks):
        if len(item) > 1:
            inner = item[1:-1]
            c = _find(inner, {cfg["colon"], ":"}) if inner else None
            head = inner[:c] if c is not None else inner
            if c is None:
                cut = None
                for k, t in enumerate(head):
                    if t.k == "sym" and _norm(t, lang) in cfg["rel"]:
                        cut = k
                        break
                if cut is not None:
                    head, bounded = head[:cut], True
            got = [t.t for t in head if t.k == "id" and t.t not in cfg["kw"]]
            names += got
            slots += max(1, len(got) + sum(1 for t in head if t.t == "_"))
            continue
        t = item[0]
        if t.k == "id" and t.t == "_":
            slots += 1
        elif t.k == "id" and t.t not in cfg["kw"]:
            names.append(t.t)
            slots += 1
        elif t.k == "tvar":
            continue
        elif t.t in (cfg["colon"], ":"):
            break
        elif t.k == "sym" and (_norm(t, lang) in cfg["rel"] or t.t in ("in", "<-")):
            bounded = True
            break
        elif t.k == "id" and t.t == "in":
            bounded = True
            break
        elif t.t == "!":
            continue
        else:
            break
    return names, slots, bounded


class _Budget:
    def __init__(self):
        self.nodes = 0
        self.truncated = False


def parse_term(toks, lang, budget=None, depth=0):
    """Logical skeleton of a term as a tree of dicts. Keys: k (kind), c (children), plus per kind:
    forall/exists/exists-unique/lambda/let: n (bound slots), bounded, meta; rel: op, sym, chain;
    leaves (app, const, num, expr, bracket, atom, str, prefix, empty, cut): h (head token), a (arguments).
    Private keys start with `_`."""
    cfg = TERM[lang]
    budget = budget or _Budget()
    budget.nodes += 1
    toks = _strip_parens(toks)
    while lang == "rocq" and len(toks) > 1 and toks[-1].k == "scope" and toks[0].k == "open":
        toks = _strip_parens(toks[:-1])                       # `(0 < n)%nat`: the scope tag after the bracket
    if not toks:
        return {"k": "empty", "_t": toks}
    if budget.nodes > MAX_NODES or depth > MAX_DEPTH:
        budget.truncated = True
        return {"k": "cut", "_t": toks}
    base = _base(toks)
    n = len(toks)

    def sub(part):
        return parse_term(part, lang, budget, depth + 1)

    # ---- scan the top level
    ops, rels, cap, i = [], [], None, 0
    binders = cfg["forall"] | cfg["meta_forall"] | cfg["exists"] | cfg["exuniq"] | cfg["lam"]
    while i < n:
        t = toks[i]
        if t.depth == base and t.k not in ("open", "close"):
            x = _norm(t, lang)
            if t.k == "sym" and x[:1] in "‖∥":
                # a pair of norm or truncation bars encloses its content like a bracket: `‖f x‖`, `∥P∥`
                j = next((q for q in range(i + 1, n) if toks[q].depth == base and toks[q].k == "sym"
                          and toks[q].t[:1] == x[:1]), None)
                if j is not None:
                    i = j + 1
                    continue
            if x in binders or (t.k == "id" and x in cfg["capture"]):
                cap = i
                break
            if x in cfg["bigop"] or (lang == "rocq" and t.k == "sym" and x.rstrip("_") in cfg["bigop"]):
                if cfg["bigop_binds"]:
                    d = _find(toks, {"."}, i + 1, base)
                    if d is not None and not any(_norm(u, lang) in cfg["ops"] for u in toks[i + 1:d] if u.depth == base):
                        cap = i
                        break
                else:
                    d = _find(toks, {","}, i + 1, base)
                    if d is not None and lang == "lean":
                        i = d + 1
                        continue
            if t.k == "sym" or (t.k == "id" and x in cfg["rel"]):
                if x in cfg["ops"]:
                    ops.append((cfg["ops"][x], i))
                elif x in cfg["rel"]:
                    rels.append(i)
        i += 1

    # ---- connectives, loosest first
    for lv in cfg["levels"]:
        idx = [p for k, p in ops if k == lv]
        if not idx:
            continue
        parts, a = [], 0
        for p in idx:
            parts.append(toks[a:p])
            a = p + 1
        parts.append(toks[a:])
        if any(not p for p in parts):
            return _leaf(toks, lang, note="empty-operand")
        if lv == "marrow":
            flat = []
            for p in parts[:-1]:
                if _is_group(p) and _isa_base(p[0].t) == "\\<lbrakk>":
                    inner, a2 = p[1:-1], 0
                    for q, u in enumerate(inner):
                        if u.t == ";" and u.depth == p[0].depth + 1:
                            flat.append(inner[a2:q])
                            a2 = q + 1
                    flat.append(inner[a2:])
                else:
                    flat.append(p)
            parts = [p for p in flat if p] + [parts[-1]]
            return {"k": "arrow", "meta": 1, "c": [sub(p) for p in parts], "_t": toks}
        return {"k": lv, "c": [sub(p) for p in parts], "_t": toks}

    # ---- prefix forms at position 0
    x0 = _norm(toks[0], lang)
    if cap == 0:
        if x0 in binders or x0 in cfg["bigop"]:
            j = 1
            kind = "forall" if x0 in cfg["forall"] | cfg["meta_forall"] else \
                "exists-unique" if x0 in cfg["exuniq"] else "exists" if x0 in cfg["exists"] else \
                "lambda" if x0 in cfg["lam"] else "bigop"
            if kind == "exists" and n > 1 and toks[1].t == "!":
                kind, j = "exists-unique", 2
            seps = cfg["lam_sep"] if kind == "lambda" else cfg["binder_sep"]
            s = _find(toks, seps, j, base)
            if s is None or s + 1 >= n:
                return _leaf(toks, lang, note="binder-without-body")
            names, slots, bounded = binder_names(toks[j:s], lang)
            body = toks[s + 1:]
            node = {"k": kind, "n": slots, "_names": names, "_t": toks}
            if bounded:
                node["bounded"] = 1
            if x0 in cfg["meta_forall"]:
                node["meta"] = 1
            if x0 == "\\<nexists>":
                node["neg"] = 1
            if kind == "bigop":
                node["h"] = x0
            if lang == "rocq" and x0 == "exists2":
                amp = _find(body, {"&"})
                if amp is not None:
                    node["c"] = [{"k": "and", "c": [sub(body[:amp]), sub(body[amp + 1:])], "_t": body}]
                    return node
            node["c"] = [sub(body)]
            return node
        if x0 == "let":
            if lang == "lean":
                a = _find(toks, {":="}, 1, base)
                e = None
                if a is not None:
                    for q in range(a + 1, n):
                        u = toks[q]
                        if u.depth == base and ((u.first and u.col <= toks[0].col) or u.t == ";"):
                            e = q + 1 if u.t == ";" else q
                            break
            else:
                a = _find(toks, {":=", "="}, 1, base)
                e, pend = None, 0
                for q in range(1, n):
                    u = toks[q]
                    if u.depth == base and u.k == "id":
                        if u.t == "let":
                            pend += 1
                        elif u.t == "in":
                            if pend == 0:
                                e = q + 1
                                break
                            pend -= 1
            if a is None or e is None or e >= n:
                return _leaf(toks, lang, note="let-without-body")
            names, slots, _b = binder_names(toks[1:a], lang)
            return {"k": "let", "n": max(1, slots), "_names": names, "c": [sub(toks[e:])], "_t": toks}
        if x0 == "if":
            th, el, pend = None, None, 0
            for q in range(1, n):
                u = toks[q]
                if u.depth == base and u.k == "id":
                    if u.t == "if":
                        pend += 1
                    elif u.t == "then" and pend == 0 and th is None:
                        th = q
                    elif u.t == "else":
                        if pend == 0 and th is not None:
                            el = q
                            break
                        pend -= 1
            if th is None or el is None or el + 1 >= n or th + 1 >= el:
                return _leaf(toks, lang, note="if-without-branches")
            return {"k": "ite", "c": [sub(toks[th + 1:el]), sub(toks[el + 1:])], "_t": toks}
        return {"k": "prefix", "h": x0, "_t": toks}

    # ---- negation, then the first relation
    if x0 in cfg["neg"] and toks[0].k == "sym" and n > 1:
        return {"k": "not", "c": [sub(toks[1:])], "_t": toks}
    if rels:
        p = rels[0]
        if 0 < p < n - 1:
            x = _norm(toks[p], lang)
            op, rhs = cfg["rel"][x], toks[p + 1:]
            if lang == "lean" and rhs[-1].k == "close" and rhs[-1].t == "]" and x == "≡":
                o = next((q for q in range(len(rhs) - 1, -1, -1) if rhs[q].k == "open" and rhs[q].depth == base), None)
                if o is not None and o > 0 and o + 1 < len(rhs) and rhs[o + 1].t in ("MOD", "ZMOD", "PMOD", "SMOD"):
                    op, rhs = "modeq", rhs[:o]                # `a ≡ b [MOD n]`
            if lang == "lean" and op == "asymp" and rhs[0].k == "open" and rhs[0].t == "[":
                e = _group_end(rhs, 0)
                if e + 1 < len(rhs):
                    rhs = rhs[e + 1:]                         # `f =O[l] g`: the filter is not part of g
            node = {"k": "rel", "op": op, "sym": x, "c": [sub(toks[:p]), sub(rhs)], "_t": toks}
            if len(rels) > 1 and cap is None:
                node["chain"] = len(rels)
            return node
    return _leaf(toks, lang)


def _leaf(toks, lang, note=None):
    cfg = TERM[lang]
    toks = _strip_parens(toks)
    node = {"_t": toks}
    if note:
        node["note"] = note
    if not toks:
        node["k"] = "empty"
        return node
    base = _base(toks)
    # a type ascription `e : T` at the top of a leaf: keep e
    c = _find(toks, {cfg["colon"]}, 0, base)
    if c is not None and c > 0:
        inner = _leaf(toks[:c], lang)
        inner["_t"] = toks
        inner["asc"] = 1
        if note:
            inner["note"] = note
        return inner
    if lang != "isabelle" and len(toks) >= 2 and toks[0].t == "@" and toks[1].k == "id":
        toks = toks[1:]
        node["explicit"] = 1
    if lang == "rocq" and any(t.k == "scope" for t in toks):
        toks = [t for t in toks if t.k != "scope"] or toks      # `2%:R`, `(0 < n)%nat`: the scope tag is dropped
    items = top_items(toks)
    if lang == "isabelle":
        braces = [it for it in items if len(it) > 1 and _isa_base(it[0].t) == "\\<lbrace>"]
        if len(braces) >= 2:
            # `\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>`: a Hoare-triple form, named by the first identifier between
            mid = [it[0] for it in items if len(it) == 1 and it[0].k == "id"]
            node["k"], node["h"] = "triple", (mid[0].t if mid else "\\<lbrace>")
            return node
    if len(items) == 1:
        it = items[0]
        if len(it) == 1:
            t = it[0]
            node["k"] = {"num": "num", "id": "const", "str": "str", "tvar": "const"}.get(t.k, "atom")
            node["h"] = t.t
            return node
        node["k"], node["h"] = "bracket", it[0].t if lang != "isabelle" else _isa_base(it[0].t)
        if _is_comprehension(it, lang):
            node["sb"] = 1
        return node
    syms = [t for t in toks if t.depth == base and (t.k == "sym" or (t.k == "id" and t.t in ("div", "mod", "dvd")))
            and t.t != ","]
    if toks[0].k == "id" and toks[0].t not in cfg["kw"] and not syms:
        node["k"], node["h"], node["a"] = "app", toks[0].t, len(items) - 1
        return node
    if len(items[0]) > 1 and not syms:
        # a bracket group applied or projected: `(f x).Finite`, `{t | P t}.ncard`, `(f x) y`
        nxt = items[1][0] if len(items[1]) == 1 else None
        if nxt is not None and nxt.k == "id" and nxt.t.startswith("."):
            node["k"], node["h"], node["a"], node["g"] = "app", nxt.t, len(items) - 2, 1
            return node
        if items[0][0].t == "(":
            inner = _leaf(items[0], lang)
            if inner.get("k") in ("app", "const") and "h" in inner:
                node["k"], node["h"], node["a"], node["g"] = "app", inner["h"], len(items) - 1, 1
                return node
    node["k"] = "expr"
    if toks[0].k == "id" and toks[0].t not in cfg["kw"]:
        node["f"] = toks[0].t
    known = [(ARITH[_norm(t, lang)], k, _norm(t, lang)) for k, t in enumerate(syms) if _norm(t, lang) in ARITH]
    unknown = [_norm(t, lang) for t in syms if _norm(t, lang) not in ARITH]
    if unknown:
        node["h"], node["u"] = unknown[0], 1
    elif known:
        node["h"] = min(known)[2]
    else:
        ids = [t for t in toks if t.k == "id" and t.t not in cfg["kw"]]
        if ids:
            d = min(t.depth for t in ids)
            node["h"] = next(t.t for t in ids if t.depth == d)
        else:
            node["h"] = _norm(toks[0], lang)
    return node


def _is_comprehension(group, lang):
    """`{x | P}`, `{x : T | P}`, `{x // P}` (lean); `{x | P}`, `{x : T & P}`, `[set x | P]` (rocq);
    `{x. P}`, `{f x | x. P}` (isabelle). A token pattern: a sigma type in Rocq has the same form."""
    if len(group) < 3:
        return False
    o, inner, d = group[0].t, group[1:-1], group[0].depth + 1
    top = [t for t in inner if t.depth == d and t.k not in ("open", "close")]
    texts = [t.t for t in top]
    if lang == "lean":
        return o == "{" and ("|" in texts or "//" in texts) and ":=" not in texts
    if lang == "rocq":
        if o == "{":
            return "|" in texts or "&" in texts
        return o == "[" and bool(top) and top[0].t in ("set", "pred", "seq", "fset", "rel", "ffun", "qualify") \
            and "|" in texts
    return o == "{" and "." in texts


def scan_forms(toks, lang):
    """One flat pass over a statement's tokens: names bound anywhere in it, and counts of comprehension and
    big-operator forms. Binding is statement-wide here: a name bound in one place is treated as bound everywhere."""
    cfg = TERM[lang]
    bound, n_sb, n_big, n = [], 0, 0, len(toks)
    binders = cfg["forall"] | cfg["meta_forall"] | cfg["exists"] | cfg["exuniq"] | cfg["lam"]
    for i, t in enumerate(toks):
        x = _norm(t, lang)
        if t.k == "open":
            j = i + 1
            while j < n and not (toks[j].k == "close" and toks[j].depth == t.depth):
                j += 1
            grp = toks[i:j + 1]
            if _is_comprehension(grp, lang):
                n_sb += 1
                inner, d = grp[1:-1], t.depth + 1
                if lang == "isabelle":
                    dot = _find(inner, {"."}, 0, d)
                    bar = _find(inner, {"|"}, 0, d)
                    seg = inner[bar + 1:dot] if bar is not None and dot is not None and bar < dot else inner[:dot]
                else:
                    bar = _find(inner, {"|", "//", "&"}, 0, d)
                    seg = inner[:bar]
                    if lang == "rocq" and seg and seg[0].t in ("set", "pred", "seq", "fset", "rel", "ffun"):
                        seg = seg[1:]
                bound += binder_names(seg, lang)[0]
            continue
        is_big = x in cfg["bigop"] or (lang == "rocq" and t.k == "sym" and x.startswith("\\")
                                       and x.rstrip("_") in cfg["bigop"])
        if is_big:
            n_big += 1
        if x in binders or is_big or (t.k == "id" and x == "let"):
            j = i + 1
            if j < n and toks[j].t == "!":
                j += 1
            if lang == "rocq" and is_big:
                if j < n and toks[j].k == "open":
                    e = j + 1
                    while e < n and not (toks[e].k == "close" and toks[e].depth == toks[j].depth):
                        e += 1
                    bound += binder_names(toks[j + 1:e], lang)[0]
                continue
            seps = cfg["lam_sep"] if x in cfg["lam"] else {":=", "="} if x == "let" else cfg["binder_sep"]
            s = None
            for q in range(j, n):
                u = toks[q]
                if u.depth < t.depth:
                    break
                if u.depth == t.depth and u.k not in ("open", "close") and u.t in seps:
                    s = q
                    break
            if s is not None:
                if is_big and lang == "isabelle" and any(_norm(u, lang) in cfg["ops"] for u in toks[j:s]
                                                         if u.depth == t.depth):
                    continue
                bound += binder_names(toks[j:s], lang)[0]
    return bound, n_sb, n_big


# ========================================================== statement parsers

LEAN_DECL = {"theorem", "lemma", "def", "abbrev", "instance", "example", "problem", "structure", "inductive",
             "class", "axiom", "opaque", "have", "suffices", "show", "obtain", "determine"}
LEAN_MODS = {"private", "protected", "noncomputable", "nonrec", "unsafe", "partial", "public", "scoped", "local"}
ROCQ_DECL = {"Theorem", "Lemma", "Corollary", "Proposition", "Fact", "Remark", "Definition", "Fixpoint",
             "CoFixpoint", "Example", "Instance", "Let", "Property", "Goal", "Axiom", "Hypothesis", "Parameter",
             "Variable", "Conjecture", "Inductive", "CoInductive", "Record", "Structure", "Class", "Function",
             "Equations", "assert", "have", "suff", "enough", "Derive"}
ROCQ_MODS = {"Local", "Global", "Program", "Polymorphic", "Monomorphic", "Time", "Timeout", "Private", "Export"}
ISA_DECL = {"lemma", "theorem", "corollary", "proposition", "schematic_goal", "have", "show", "hence", "thus",
            "obtain", "definition", "abbreviation", "fun", "function", "primrec", "lemmas", "instance",
            "interpretation", "sublocale", "global_interpretation", "consider", "moreover", "also", "ultimately",
            "then", "from", "with", "finally", "theorems", "declare", "inductive", "datatype", "locale", "class"}
ISA_MODS = {"private", "qualified", "protected"}
ISA_ELEM = {"fixes", "assumes", "shows", "obtains", "notes", "defines", "includes", "constrains", "if", "for",
            "when", "where", "and", "is"}
ISA_PROOF_START = {"proof", "by", "apply", "using", "unfolding", "sorry", "oops", "done", "supply", "including",
                   "subgoal", "apply_end", "\\<proof>"}


def _group_end(toks, i):
    """Index of the close matching the open at i (or len(toks) - 1)."""
    d = toks[i].depth
    for j in range(i + 1, len(toks)):
        if toks[j].k == "close" and toks[j].depth == d:
            return j
    return len(toks) - 1


def _binder_groups(toks, lang):
    """Declaration binders between the name and the colon. Returns (binders, ok)."""
    out = []
    for item in top_items(toks):
        if len(item) == 1:
            t = item[0]
            if t.k == "id":
                out.append({"kind": "explicit", "names": [] if t.t == "_" else [t.t], "n": 1, "typed": False,
                            "type": None})
                continue
            if lang == "rocq" and t.t == "'":
                continue
            return out, False
        o, inner = item[0].t, item[1:-1]
        kind = {"(": "explicit", "{": "implicit", "⦃": "strict-implicit", "[": "instance", "`{": "instance",
                "`(": "explicit"}.get(o)
        if lang == "rocq" and o == "[":
            kind = "implicit"
        if kind is None:
            return out, False
        c = _find(inner, {":"}) if inner else None
        if c is None:
            if kind == "instance":
                out.append({"kind": kind, "names": [], "n": 1, "typed": True, "type": inner})
                continue
            a = _find(inner, {":="}) if inner else None
            head = inner if a is None else inner[:a]
            names = [t.t for t in head if t.k == "id" and t.t != "_"]
            slots = sum(1 for t in head if t.k == "id")
            out.append({"kind": "let" if a is not None else kind, "names": names, "n": max(1, slots), "typed": False,
                        "type": None})
            continue
        names = [t.t for t in inner[:c] if t.k == "id" and t.t != "_"]
        slots = sum(1 for t in inner[:c] if t.k == "id")
        ty = inner[c + 1:]
        a = _find(ty, {":="}, 0, item[0].depth + 1) if ty else None
        if a is not None:
            ty = ty[:a]
        out.append({"kind": kind, "names": names, "n": max(1, slots), "typed": True, "type": ty})
    return out, True


def _assign_index(toks, start, base=0):
    """First `:=` at depth base from start that does not belong to a `let` at that depth."""
    pend = 0
    for i in range(start, len(toks)):
        t = toks[i]
        if t.depth != base or t.k in ("open", "close"):
            continue
        if t.k == "id" and t.t == "let":
            pend += 1
        elif t.t == ":=":
            if pend:
                pend -= 1
            else:
                return i
    return None


def parse_statement(text, lang):
    """Parse a statement as recorded in entry.json. Returns (parsed, reason): parsed is None when reason is set.

    parsed: form, decl_kind, name, binders [{kind, names, n, typed, type (tokens)}], hyps [token lists],
    concl [token lists] (several for an Isabelle statement with several `shows` propositions), obtains
    (Isabelle), toks (every token of the statement region), n_decls, notes.
    """
    if text is None or not text.strip():
        return None, "empty-statement"
    src = blank_comments(text, lang)
    if lang == "lean":
        return _parse_lean(src)
    if lang == "rocq":
        return _parse_rocq(src)
    if lang == "isabelle":
        return _parse_isabelle(src)
    return None, "language-not-parsed"


def _parse_lean(src):
    toks = lex_lean(src)
    if not toks:
        return None, "empty-statement"
    if not balanced(toks):
        return None, "unbalanced-brackets"
    n, i, notes = len(toks), 0, []
    n_decls = sum(1 for t in toks if t.depth == 0 and t.k == "id" and t.t in LEAN_DECL
                  and t.t not in ("have", "show", "suffices", "obtain") and _decl_position(toks, t))
    while i < n:
        if toks[i].t == "@" and i + 1 < n and toks[i + 1].t == "[":
            i = _group_end(toks, i + 1) + 1
        elif toks[i].k == "id" and toks[i].t in LEAN_MODS:
            i += 1
        else:
            break
    if i >= n:
        return None, "empty-statement"
    kind, name, form = None, None, "bare"
    if toks[i].k == "id" and toks[i].t in LEAN_DECL:
        kind, form = toks[i].t, "decl"
        i += 1
        if i < n and toks[i].k == "id" and toks[i].t not in TERM["lean"]["kw"] and kind != "show":
            name = toks[i].t
            i += 1
            if i + 1 < n and toks[i].t == "." and toks[i + 1].t == "{":
                i = _group_end(toks, i + 1) + 1
    elif (toks[i].k == "id" and toks[i].t not in TERM["lean"]["kw"]) or toks[i].k == "open":
        form = "signature"
    # the colon that ends the binders: the first `:` at depth 0 before any `:=`
    colon = None
    for j in range(i, n):
        t = toks[j]
        if t.depth == 0 and t.k == "sym":
            if t.t == ":":
                colon = j
                break
            if t.t == ":=":
                break
    region_ok = False
    if form == "signature":
        # `name binders : type` or `binders : type` with no declaration word
        named = toks[i].k == "id"
        if colon is not None:
            sig = toks[i + 1:colon] if named else toks[i:colon]
            region_ok = all(t.k in ("id", "open", "close") or t.depth > 0 for t in sig)
            if region_ok:
                bs, region_ok = _binder_groups(sig, "lean")
                region_ok = region_ok and (named or any(b["typed"] for b in bs))
        if region_ok:
            if named:
                name = toks[i].t
                i += 1
        else:
            form, colon = "bare", None
    if form == "bare":
        end = _assign_index(toks, i)
        ty = toks[i:end] if end is not None else toks[i:]
        if not ty:
            return None, "empty-statement"
        return {"form": form, "decl_kind": None, "name": None, "binders": [], "hyps": [], "concl": [ty],
                "toks": ty, "n_decls": n_decls, "notes": notes}, None
    if colon is None:
        a = _assign_index(toks, i)
        binders, ok = _binder_groups(toks[i:a] if a is not None else toks[i:], "lean")
        if not ok:
            return None, "binder-parse"
        notes.append("no-type")
        return {"form": form, "decl_kind": kind, "name": name, "binders": binders, "hyps": [], "concl": [],
                "toks": toks[i:a] if a is not None else toks[i:], "n_decls": n_decls, "notes": notes}, None
    binders, ok = _binder_groups(toks[i:colon], "lean")
    if not ok:
        return None, "binder-parse"
    end = _assign_index(toks, colon + 1)
    for j in range(colon + 1, end if end is not None else n):
        t = toks[j]
        if t.depth == 0 and ((t.k == "id" and t.t == "where") or _is_arm(toks, j)):
            end = j
            break
    ty = toks[colon + 1:end] if end is not None else toks[colon + 1:]
    if not ty:
        return None, "empty-type"
    return {"form": form, "decl_kind": kind, "name": name, "binders": binders, "hyps": [], "concl": [ty],
            "toks": toks[i:end] if end is not None else toks[i:], "n_decls": n_decls, "notes": notes}, None


def _is_arm(toks, j):
    """The token at j is a line-leading `|` that starts a pattern-matching arm: a `=>` follows at depth 0
    before the next line-leading `|`. `|a - b| = 1` at the start of a line is not one."""
    t = toks[j]
    if not (t.t == "|" and t.first and t.depth == 0):
        return False
    for u in toks[j + 1:]:
        if u.depth == 0 and u.t == "=>":
            return True
        if u.depth == 0 and u.t == "|" and u.first:
            return False
    return False


def _decl_position(toks, t):
    """A declaration word counts when it starts a line or follows only attributes and modifiers on it."""
    if t.first:
        return True
    k = toks.index(t) - 1
    while k >= 0 and toks[k].line == t.line:
        u = toks[k]
        if not (u.depth > 0 or u.t in LEAN_MODS or u.t in ("@", "]", "[")):
            return False
        k -= 1
    return True


def _parse_rocq(src):
    toks = lex_rocq(src)
    if not toks:
        return None, "empty-statement"
    n, i, notes = len(toks), 0, []
    while i < n:
        if toks[i].t == "#" and i + 1 < n and toks[i + 1].t == "[":
            i = _group_end(toks, i + 1) + 1
        elif toks[i].k == "id" and toks[i].t in ROCQ_MODS:
            i += 1
        else:
            break
    if i >= n:
        return None, "empty-statement"
    n_decls = sum(1 for k, t in enumerate(toks) if t.depth == 0 and t.k == "id" and t.t in ROCQ_DECL
                  and t.t[0].isupper() and (k == 0 or toks[k - 1].k == "dot" or toks[k - 1].t in ROCQ_MODS))
    kind, name, form = None, None, "bare"
    if toks[i].k == "id" and toks[i].t in ROCQ_DECL:
        kind, form = toks[i].t, "decl"
        i += 1
        if kind == "assert" and i < n and toks[i].k == "open":
            e = _group_end(toks, i)
            inner = toks[i + 1:e]
            c = _find(inner, {":"}) if inner else None
            if c is not None:
                ty = inner[c + 1:]
                nm = inner[0].t if inner[0].k == "id" else None
            else:
                ty, nm = inner, None
            if not ty:
                return None, "empty-type"
            return {"form": form, "decl_kind": kind, "name": nm, "binders": [], "hyps": [], "concl": [ty],
                    "toks": ty, "n_decls": n_decls, "notes": notes}, None
        if i < n and toks[i].k == "id" and toks[i].t not in TERM["rocq"]["kw"]:
            name = toks[i].t
            i += 1
    end = None
    for j in range(i, n):
        if toks[j].k == "dot" and toks[j].depth == 0:
            end = j
            break
    region = toks[i:end] if end is not None else toks[i:]
    if not region:
        return None, "empty-statement"
    if not balanced(region):
        return None, "unbalanced-brackets"
    base = _base(region)
    if form == "bare":
        return {"form": form, "decl_kind": None, "name": None, "binders": [], "hyps": [], "concl": [region],
                "toks": region, "n_decls": n_decls, "notes": notes}, None
    colon = None
    for j, t in enumerate(region):
        if t.depth == base and t.k == "sym":
            if t.t == ":":
                colon = j
                break
            if t.t == ":=":
                break
    if colon is None:
        a = _assign_index(region, 0, base)
        binders, ok = _binder_groups(region[:a] if a is not None else region, "rocq")
        if not ok:
            return None, "binder-parse"
        notes.append("no-type")
        return {"form": form, "decl_kind": kind, "name": name, "binders": binders, "hyps": [], "concl": [],
                "toks": region[:a] if a is not None else region, "n_decls": n_decls, "notes": notes}, None
    binders, ok = _binder_groups(region[:colon], "rocq")
    if not ok:
        return None, "binder-parse"
    a = _assign_index(region, colon + 1, base)
    ty = region[colon + 1:a] if a is not None else region[colon + 1:]
    if not ty:
        return None, "empty-type"
    return {"form": form, "decl_kind": kind, "name": name, "binders": binders, "hyps": [], "concl": [ty],
            "toks": region[:a] if a is not None else region, "n_decls": n_decls, "notes": notes}, None


def _blank_inner_comments(text):
    """`(* .. *)` comments inside a term are blanked; the operator section `(*)` is kept."""
    out, i, n = list(text), 0, len(text)
    while i < n:
        if text.startswith("(*", i) and not text.startswith("(*)", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("(*", j) and not text.startswith("(*)", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("*)", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def _isa_inner(tok):
    """Inner tokens of a string or cartouche. Line numbers continue the outer count."""
    toks = lex_isabelle(_blank_inner_comments(tok.t), inner=True)
    for t in toks:
        t.line += tok.line - 1
    return toks


def _parse_isabelle(src):
    outer = lex_isabelle(src)
    if not outer:
        return None, "empty-statement"
    n, i, notes = len(outer), 0, []
    while i < n and outer[i].k == "id" and outer[i].t in ISA_MODS:
        i += 1
    if i >= n:
        return None, "empty-statement"
    kind, name, form = None, None, "bare"
    has_inner = any(t.k == "inner" for t in outer)
    if outer[i].k == "id" and outer[i].t in ISA_DECL:
        kind, form = outer[i].t, "decl"
        i += 1
        if i + 1 < n and outer[i].t == "(" and outer[i + 1].t == "in":
            i = _group_end(outer, i) + 1
        if i < n and outer[i].k == "id" and outer[i].t not in ISA_ELEM and outer[i].t not in ISA_PROOF_START:
            name = outer[i].t
            i += 1
        if i < n and outer[i].t == "[":
            i = _group_end(outer, i) + 1
        if i < n and outer[i].t == ":":
            i += 1
    elif outer[i].k == "id" and i + 1 < n and outer[i + 1].t == ":" and has_inner:
        name, form = outer[i].t, "labelled"
        i += 2
    elif not has_inner:
        toks = lex_isabelle(src, inner=True)
        if not balanced(toks):
            return None, "unbalanced-brackets"
        return {"form": "bare", "decl_kind": None, "name": None, "binders": [], "hyps": [], "concl": [toks],
                "toks": toks, "n_decls": 0, "notes": notes}, None
    binders, hyps, concl, obtains, mode = [], [], [], [], "shows"
    while i < n:
        t = outer[i]
        if t.k == "id" and t.t in ISA_PROOF_START and t.depth == 0:
            break
        if t.k == "open":
            i = _group_end(outer, i) + 1
            continue
        if t.k == "id" and t.depth == 0:
            if t.t in ("fixes", "for"):
                mode = "fixes"
            elif t.t in ("assumes", "if", "when"):
                mode = "assumes"
            elif t.t == "shows":
                mode = "shows"
            elif t.t == "obtains":
                mode = "obtains"
            elif t.t in ("notes", "defines", "includes", "constrains"):
                mode = "skip"
            elif t.t == "where":
                mode = "shows" if mode not in ("obtains",) else "obtains-props"
            elif t.t in ("and", "is"):
                pass
            elif mode == "fixes":
                binders.append({"kind": "fixes", "names": [t.t], "n": 1, "typed": False, "type": None})
            elif mode == "obtains":
                obtains.append(t.t)
            i += 1
            continue
        if t.t == "::" and mode == "fixes":
            if binders:
                binders[-1]["typed"] = True
            i += 2
            continue
        if t.k == "inner":
            if mode == "assumes":
                hyps.append(_isa_inner(t))
            elif mode in ("shows", "obtains", "obtains-props"):
                concl.append(_isa_inner(t))
        i += 1
    all_toks = [u for part in hyps + concl for u in part]
    if not concl:
        return None, "no-proposition"
    if not all(balanced(p) for p in hyps + concl):
        return None, "unbalanced-brackets"
    return {"form": form, "decl_kind": kind, "name": name, "binders": binders, "hyps": hyps, "concl": concl,
            "obtains": obtains if mode.startswith("obtains") else None, "toks": all_toks, "n_decls": 1,
            "notes": notes}, None


# ================================================================ proof steps
#
# CLASS_TABLE is the main judgement in the extractor: it assigns each tactic,
# proof command or proof method head to one class. It is data, with a version.
# A head that is in no row is reported as `unclassified`; nothing is inferred
# from its spelling except the two prefix rules in HEAD_PREFIX_RULES.

CLASS_TABLE_VERSION = "1"

CLASSES = ("automation", "trivial-close", "exact", "apply", "rewrite", "intro", "have", "obtain", "show",
           "suffices", "induction", "case-split", "ext", "witness", "constructor", "calc", "contra", "context",
           "combinator", "structure", "facts", "term", "sorry", "domain", "unclassified")

CLASS_TABLE = {
    "lean": {
        "automation": "simp simp_all simpa simp_arith simp_all_arith field_simp norm_num norm_num1 norm_cast "
                      "push_cast exact_mod_cast assumption_mod_cast apply_mod_cast mod_cast ring ring_nf ring1 "
                      "ring_exp linarith nlinarith positivity omega decide native_decide dec_trivial aesop "
                      "aesop_cat tauto itauto polyrith linear_combination linear_combination' abel abel_nf group "
                      "noncomm_ring module lia nia grind bv_decide bv_omega gcongr bound continuity measurability "
                      "fun_prop finiteness norm_fin tidy finish cc simp_wf simp_intro hint solve_by_elim "
                      "apply_assumption apply_rules interval compute_degree monicity reduce_mod_char subsingleton "
                      "cancel_denoms field push zify qify rify nomatch order cat_disch exact? apply? rw?",
        "trivial-close": "rfl trivial assumption contradiction done refl ac_rfl infer_instance exact_decide eq_refl",
        "exact": "exact from exacts",
        "apply": "apply refine refine' convert convert_to congr congr! congrm apply_fun peel filter_upwards "
                 "fapply eapply rapply mono lift",
        "rewrite": "rw rwa rewrite erw nth_rw nth_rewrite simp_rw grw subst unfold delta change dsimp push_neg "
                   "conv conv_lhs conv_rhs unfold_let simp_only dsimp_only simp_all_only rw_mod_cast beta_reduce "
                   "eta_reduce whnf reduce unfold_coes dunfold subst_vars substs enter arg lhs rhs equals",
        "intro": "intro intros rintro rintros assume introv introsI",
        "have": "have haveI replace observe",
        "obtain": "obtain rcases choose cases'",
        "show": "show",
        "suffices": "suffices wlog rsuffices",
        "induction": "induction induction' fun_induction strong_induction_on induction_on termination_by "
                     "decreasing_by",
        "case-split": "cases by_cases match interval_cases fin_cases mod_cases split split_ifs casesm cases_type "
                      "rcases_alt obtain_alt rintro_alt if cases_matching injection",
        "ext": "ext ext1 funext",
        "witness": "use exists existsi refine_exists",
        "constructor": "constructor left right and_intros split_ands refine_struct econstructor fconstructor",
        "calc": "calc trans transitivity",
        "contra": "by_contra contrapose exfalso absurd by_contradiction",
        "context": "set let clear revert generalize specialize rename_i rename symm swap rotate_left rotate_right "
                   "pick_goal clear_value letI classical open inhabit lift_lets extract_goal generalize_proofs "
                   "unfreezingI resetI exactI substI symmetry borelize",
        "combinator": "try repeat all_goals any_goals iterate focus first on_goal skip work_on_goal solve",
        "structure": "case next",
        "sorry": "sorry admit stop",
        "domain": "p2m_exact_reverting iexact isplitl isplitr isplit icases iintro ipureintro iframe imodintro "
                  "imod iexists iapply inext iempintro ileft iright itrivial ihave ispecialize irevert iclear "
                  "irename wp_apply wp_pures wp_bind",
    },
    "rocq": {
        "automation": "auto eauto tauto intuition firstorder lia nia lra nra psatz omega ring field congruence "
                      "easy now hauto sauto qauto hammer sfirstorder crush set_solver naive_solver solve_ndisj "
                      "btauto nsatz fourier zify typeclasses_eauto decide_equality dintuition rtauto itauto "
                      "simplify_eq solve_proper f_equiv xomega eomega ssromega autorewrite ring_simplify "
                      "field_simplify autounfold rep_lia extlia fwd entailer cancel normalize algebra "
                      "remove_bools_options ring_lia fsetdec SvD.fsetdec CatReducible pcuic fmap_solve in_crush lias",
        "trivial-close": "reflexivity assumption eassumption trivial done discriminate contradiction idpath tea "
                         "trea tas",
        "exact": "exact eexact",
        "apply": "apply eapply refine simple_apply congr f_equal rapply lapply simple_eapply simple_refine "
                 "srapply nrapply napply snrapply exploit eexploit use find_apply_lem_hyp find_apply_hyp_hyp "
                 "apply_in_hyps sep_apply",
        "rewrite": "rewrite erewrite setoid_rewrite rewrite_strat unfold fold change replace subst simpl cbn cbv "
                   "compute vm_compute native_compute lazy hnf red pattern under unlock simp find_rewrite "
                   "push_Zmod pull_Zmod simpl_rev",
        "intro": "intro intros move=> introv iIntros => Intros Intro",
        "have": "have assert pose_proof epose_proof eassert iAssert assert_PROP",
        "obtain": "decompose iDestruct break_exists",
        "show": "show",
        "suffices": "suff suffices enough wlog cut eenough",
        "induction": "induction elim eelim einduction functional_induction dependent_induction fix cofix pcofix "
                     "iInduction iLöb einit ecofix ginit gcofix funelim simple_induction depind",
        "case-split": "destruct case case_eq inversion inv invs edestruct dependent_destruction inversion_clear "
                      "simple_inversion case_match destruct_with_eqn destr decide simple_destruct invc "
                      "dependent_inversion depelim if_tac simple_if_tac bdestruct noconf find_inversion "
                      "case_leq",
        "ext": "extensionality functional_extensionality funext",
        "witness": "exists eexists exists2 iExists Exists instantiate",
        "constructor": "split constructor econstructor left right esplit iSplit iSplitL iSplitR esplits splits "
                       "eleft eright ssplit",
        "calc": "transitivity etransitivity trans etrans intermediate_path",
        "contra": "exfalso absurd contradict Contradict",
        "context": "move move: move/ pose set clear revert generalize specialize rename remember clearbody "
                   "symmetry epose eset injection unshelve shelve cycle swap idtac iModIntro iNext iPureIntro "
                   "iFrame iClear iRevert iPoseProof iSpecialize iLeft iRight dependent_rewrite revgoals forget",
        "combinator": "try repeat do first last solve progress timeout once abstract time dispatch tryif all par "
                      "match lazymatch let",
        "structure": "",
        "sorry": "admit Admitted Abort give_up",
        "domain": "forward forward_call forward_if start_function erbind rbind TransfInstr tau_steps",
    },
    "isabelle": {
        "automation": "simp simp_all auto blast force fastforce clarsimp metis meson smt argo arith linarith "
                      "presburger algebra eval code_simp normalization safe clarify fast best slow bestsimp "
                      "slowsimp auto2 sep_auto wp wpsimp vcg satx iprover order simp_arith sos sledgehammer "
                      "lexicographic_order pat_completeness size_change transfer_prover measurable real_asymp "
                      "approximation sep_solve sep_cancel monad_eq intro_classes unfold_locales intro_locales "
                      "standard sepref refine_vcg vc_solve refine_rcg rel_auto pred_auto pred_simp rel_simp "
                      "hoare_auto unat_arith",
        "trivial-close": "assumption fact this - succeed . .. done contradiction",
        "exact": "",
        "apply": "rule erule drule frule rule_tac erule_tac drule_tac frule_tac intro elim dest rules "
                 "relation atomize_elim cut_tac rule_format",
        "rewrite": "subst unfold unfolding simp_only rewrite hypsubst hypsubst_thin simplesubst fold",
        "intro": "fix assume presume",
        "have": "have hence subgoal_tac",
        "obtain": "obtain guess",
        "show": "show thus",
        "suffices": "",
        "induction": "induct induction induct_tac coinduct coinduction nominal_induct infinite_descent",
        "case-split": "cases case_tac ind_cases consider",
        "ext": "",
        "witness": "",
        "constructor": "",
        "calc": "also finally",
        "contra": "",
        "context": "let define note interpret insert transfer thin_tac rename_tac rotate_tac atomize tactic "
                   "write supply including defer prefer back",
        "combinator": "use all fail",
        "structure": "proof qed next case { subgoal apply by apply_end goal_cases",
        "facts": "from with using then moreover ultimately",
        "sorry": "sorry oops",
        "domain": "corres corressimp ccorres crunch ctac csymbr cinit",
    },
}

# A head absent from CLASS_TABLE that matches one of these regular expressions takes the class given.
HEAD_PREFIX_RULES = {
    "lean": [],
    "rocq": [(r"^i[A-Z]\w*$", "domain"), (r"^wp_\w+$", "domain"), (r"^ssprove\w*$", "domain"),
             (r"^fcf_\w+$", "domain"), (r"^solve_\w+$", "automation"), (r"^destruct_\w+$", "case-split"),
             (r"^simplify_\w+$", "automation")],
    "isabelle": [(r"^wp\w*$", "automation"), (r"^c?corres\w*$", "domain")],
}


def _invert(table):
    out = {}
    for cls, names in table.items():
        for nm in names.split():
            if nm in out and out[nm] != cls:
                raise ValueError(f"head {nm!r} in two classes: {out[nm]} and {cls}")
            out[nm] = cls
    return out


HEAD_CLASS = {lang: _invert(tab) for lang, tab in CLASS_TABLE.items()}


def classify_head(name, lang):
    tab = HEAD_CLASS[lang]
    key = name.replace(" ", "_")
    if key in tab:
        return tab[key]
    if name in tab:
        return tab[name]
    stripped = key.rstrip("?!'")
    if stripped in tab:
        return tab[stripped]
    if name == "«term»":
        return "term"
    for rx, cls in HEAD_PREFIX_RULES[lang]:
        if re.match(rx, name):
            return cls
    return "unclassified"


# ---------------------------------------------------------------------- lean

_LEAN_TOP = {"theorem", "lemma", "def", "abbrev", "instance", "example", "problem", "structure", "inductive",
             "class", "axiom", "opaque", "determine", "snip"}
_LEAN_ARM = {"case", "case'", "next", "on_goal", "conv", "conv_lhs", "conv_rhs", "match", "pick_goal",
             "work_on_goal", "focus_case"}
_LEAN_COMB = {"try", "repeat", "repeat'", "all_goals", "any_goals", "iterate", "focus", "first", "classical",
              "any_goals!", "solve"}
_LEAN_ALT = {"rcases", "obtain", "rintro"}


def _lean_head_name(toks, i):
    t = toks[i]
    name = t.t
    nxt = toks[i + 1].t if i + 1 < len(toks) else ""
    if name in ("simp", "simp_all", "dsimp", "simp?", "simp!") and nxt == "only":
        return name.rstrip("?!") + " only"
    return name


def _has_alt(toks, i, stop_names):
    """A `|` between the head at i and the next statement-level stop on the same tactic: the pattern has alternatives."""
    d, line = toks[i].depth, toks[i].line
    for u in toks[i + 1:]:
        if u.depth < d:
            return False
        if u.depth == d and (u.t in (";", "<;>", ":=", "=>") or (u.first and u.line != line)):
            return False
        if u.t == "|":
            return True
    return False


def lean4_heads(toks, fragment=False):
    """Tactic heads of Lean 4 text, in order, as (token index, name). See terms.md for the layout rules:
    a head is the first token after `by`, a bullet, `;`, `<;>`, a combinator or the `=>` of a case arm, or the
    first token of a line that starts in the column of its tactic block at that block's bracket depth."""
    heads, stack, n = [], [], len(toks)
    new_block = same = arm = False
    info = {"bullets": 0, "calc_steps": 0, "arms": 0, "symbol_heads": 0}
    if fragment and toks:
        stack.append([toks[0].col, toks[0].depth])
    for i, t in enumerate(toks):
        while stack and t.depth < stack[-1][1]:
            stack.pop()
        is_head = False
        if t.first:
            arm = False
        if new_block:
            stack.append([t.col, t.depth])
            is_head, new_block, same = True, False, False
        elif same:
            is_head, same = True, False
        elif t.first and stack:
            while stack and t.col < stack[-1][0]:
                stack.pop()
            if stack and t.depth == stack[-1][1]:
                if t.col == stack[-1][0]:
                    is_head = True
                elif t.t == "|":
                    arm = True
                    info["arms"] += 1
        if is_head:
            if t.t in ("·", ".", "•") and t.k == "sym":
                info["bullets"] += 1
                new_block = True
                continue
            if t.t == "|":
                if heads and heads[-1][1] == "first":
                    same = True
                else:
                    arm = True
                    info["arms"] += 1
                continue
            if t.k == "open" and t.t in "({":
                new_block = True
                continue
            if t.t == "<;>":
                same = True
                continue
            if t.t == "_" or t.t == "...":
                info["calc_steps"] += 1
                continue
            if t.k == "id" and t.t in ("by", "decreasing_by"):
                if t.t == "decreasing_by":
                    heads.append((i, t.t))
                new_block = i + 1 < n
                continue
            if t.k == "id":
                name = _lean_head_name(toks, i)
                if name in _LEAN_ALT and _has_alt(toks, i, None):
                    name += "_alt"
                heads.append((i, name))
                if name in _LEAN_ARM:
                    arm = True
                if name in _LEAN_COMB:
                    same = True
                    if name == "iterate" and i + 1 < n and toks[i + 1].k == "num":
                        same = False
                continue
            info["symbol_heads"] += 1                         # a bracket or symbol in head position: not a tactic
            continue
        if t.k == "id" and t.t in ("by", "decreasing_by"):
            if t.t == "decreasing_by":
                heads.append((i, t.t))
            new_block = i + 1 < n
        elif t.t in (";", "<;>") and stack and t.depth == stack[-1][1]:
            same = True
        elif t.t == "=>" and arm and stack and t.depth == stack[-1][1]:
            new_block, arm = i + 1 < n, False
        elif t.k == "id" and t.t == "termination_by":
            heads.append((i, t.t))
        elif t.t == "_" and t.first and i + 1 < n and toks[i + 1].k == "sym":
            info["calc_steps"] += 1                          # a calc step on an indented line: `_ ≤ c := ..`
    return heads, info


def lean3_heads(toks):
    """Tactic heads of a Lean 3 `begin ... end` block: the first token after `begin`, `,`, `;`, `<|>` or `{`
    at the bracket depth of the enclosing tactic block, and after `by`."""
    heads, stack, expect = [], [], False
    info = {"bullets": 0, "calc_steps": 0, "arms": 0, "symbol_heads": 0}
    for i, t in enumerate(toks):
        if t.k == "id" and t.t == "begin":
            stack.append(t.depth)
            expect = True
            continue
        if t.k == "id" and t.t == "end" and stack and t.depth == stack[-1]:
            stack.pop()
            expect = False
            continue
        if t.k == "close" and t.t == "}" and len(stack) > 1 and t.depth == stack[-1] - 1:
            stack.pop()
            continue
        if expect:
            if t.k == "open" and t.t == "{":
                stack.append(t.depth + 1)
                info["bullets"] += 1
                continue
            expect = False
            if t.k == "id" and t.t not in ("by",):
                name = t.t
                if name in ("simp", "dsimp") and i + 1 < len(toks) and toks[i + 1].t == "only":
                    name += " only"
                if name in _LEAN_ALT and _has_alt(toks, i, None):
                    name += "_alt"
                heads.append((i, name))
                if name in _LEAN_COMB:
                    expect = True
                continue
            if t.t == "...":
                info["calc_steps"] += 1
        if t.k == "id" and t.t == "by":
            expect = True
        elif t.t == "..." and t.first:
            info["calc_steps"] += 1
        elif stack and t.depth == stack[-1] and t.t in (",", ";", "<|>"):
            expect = True
    return heads, info


def read_lean_site(text):
    src = blank_comments(text, "lean")
    toks = lex_lean(src)
    out = {"n_tokens": len(toks), "toks": toks, "decls": [], "heads": [], "body": [], "mode": "none",
           "dialect": "lean4",
           "info": {"bullets": 0, "calc_steps": 0, "arms": 0, "symbol_heads": 0}, "closing": None}
    if not toks:
        return out
    starts = [i for i, t in enumerate(toks) if t.depth == 0 and t.k == "id" and t.t in _LEAN_TOP
              and _decl_position(toks, t)]
    lean3 = any(t.k == "id" and t.t == "begin" and t.first for t in toks)
    if lean3:
        out["dialect"] = "lean3"
    scan = lean3_heads if lean3 else lean4_heads
    modes = []
    if not starts:
        # a range inside a proof, or a `have` cut out of one
        hs, info = (scan(toks) if lean3 else lean4_heads(toks, fragment=True))
        out["heads"] = [(toks[i].line, nm) for i, nm in hs]
        out["body"], out["mode"], out["info"] = toks, "fragment", info
        if hs:
            top = [nm for i, nm in hs if toks[i].depth == toks[0].depth]
            out["closing"] = (top or [hs[-1][1]])[-1]
        return out
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(toks)
        # attributes and modifiers before the next declaration belong to it
        seg = toks[s:e]
        name = seg[1].t if len(seg) > 1 and seg[1].k == "id" else None
        colon = None
        for j, t in enumerate(seg):
            if t.depth == 0 and t.k == "sym":
                if t.t == ":":
                    colon = j
                    break
                if t.t == ":=":
                    break
        a = _assign_index(seg, (colon + 1) if colon is not None else 1)
        eq = None
        for j in range((colon + 1) if colon is not None else 1, a if a is not None else len(seg)):
            t = seg[j]
            if t.depth == 0 and (_is_arm(seg, j) or (t.k == "id" and t.t == "where")):
                eq = j
                break
        if eq is not None:
            body, mode = seg[eq:], "equations"
        elif a is not None:
            body = seg[a + 1:]
            mode = "tactic" if body and body[0].t in ("by", "begin") else "term" if body else "none"
        else:
            body, mode = [], "none"
        out["decls"].append({"kind": seg[0].t, "name": name, "mode": mode})
        modes.append(mode)
        if not body:
            continue
        hs, info = scan(body)
        if mode in ("term", "equations"):
            out["heads"].append((body[0].line, "«term»"))
        out["heads"] += [(body[i].line, nm) for i, nm in hs]
        for key in info:
            out["info"][key] += info[key]
        out["body"] += body
        # the closing step is the last head that is not inside brackets: in `exact f (by simp)` it is `exact`.
        # Lean 3 writes tactic blocks in braces, so there every head counts.
        top = [nm for i, nm in hs if lean3 or body[i].depth == body[0].depth]
        out["closing"] = (top or [hs[-1][1]])[-1] if hs and mode == "tactic" else "«term»"
    kinds = [m for m in modes if m != "none"]
    out["mode"] = "none" if not kinds else kinds[0] if len(set(kinds)) == 1 else "mixed"
    return out


# ---------------------------------------------------------------------- rocq

_ROCQ_THEOREM = {"Theorem", "Lemma", "Corollary", "Proposition", "Fact", "Remark", "Goal", "Property", "Example",
                 "Instance", "Definition", "Let", "Fixpoint", "CoFixpoint", "Derive", "Function", "Equations"}
_ROCQ_END = {"Qed", "Defined", "Admitted", "Abort", "Save"}
_ROCQ_VERNAC = {"Check", "Print", "Set", "Unset", "Show", "Hint", "Opaque", "Transparent", "Search", "About",
                "Locate", "Eval", "Compute", "Import", "Export", "Require", "Open", "Close", "Local", "Global",
                "Existing", "Ltac", "Ltac2", "Tactic", "Notation", "Arguments", "Unshelve", "Guarded", "Optimize",
                "Section", "End", "Module", "Variable", "Variables", "Context", "Hypothesis", "Hypotheses",
                "Implicit", "Generalizable", "Scheme", "Combined", "Infix", "Reserved", "Bind", "Delimit",
                "Canonical", "Coercion", "Declare", "Record", "Structure", "Inductive", "CoInductive", "Class",
                "Parameter", "Parameters", "Axiom", "Axioms", "Conjecture", "Obligation", "Solve", "Program",
                "Polymorphic", "Monomorphic", "From", "Include", "Universe", "Universes", "Constraint", "Create",
                "Remove", "Typeclasses", "Obligations", "Strategy", "Add", "Proof", "HB", "Elpi", "Fail", "Succeed",
                "Time", "Timeout", "Redirect", "Extraction", "Recursive", "Comments", "Opaque", "Abort"}
_ROCQ_COMB = {"try", "repeat", "do", "first", "last", "solve", "progress", "timeout", "once", "abstract", "time",
              "tryif", "unshelve", "all", "par"}


def _local_depth(toks):
    """Depths recomputed inside one sentence, so that focusing braces of other sentences do not count."""
    out, d = [], 0
    for t in toks:
        if t.k == "close":
            d = max(0, d - 1)
            out.append(d)
        else:
            out.append(d)
            if t.k == "open":
                d += 1
    return out


def _rocq_segment_head(seg, heads, flags, line):
    """Append the head or heads of one `;`-segment of a tactic sentence."""
    i, n = 0, len(seg)
    while i < n:
        t = seg[i]
        nxt = seg[i + 1] if i + 1 < n else None
        if t.k == "id" and t.t in _ROCQ_COMB:
            heads.append((line, t.t))
            i += 1
            if t.t in ("do", "timeout") and i < n and (seg[i].k == "num" or seg[i].t in ("!", "?")):
                i += 1
                if i < n and seg[i].t in ("!", "?"):
                    i += 1
            if t.t in ("all", "par") and i < n and seg[i].t == ":":
                i += 1
            if t.t in ("first", "last") and i < n and seg[i].k == "num":
                i += 1
            if t.t in ("first", "last") and i < n and seg[i].t in ("first", "last"):
                heads.append((line, seg[i].t))
                return
            continue
        if t.k == "id" and t.t == "by":
            flags["by"] = flags.get("by", 0) + 1
            if nxt is not None and nxt.t == "[" and i + 2 < n and seg[i + 2].t == "]":
                heads.append((line, "done"))
                return
            if nxt is None:
                heads.append((line, "done"))
                return
            i += 1
            continue
        if t.k == "id" and t.t == "now":
            heads.append((line, "now"))
            i += 1
            continue
        if t.k == "open" and t.t == "(":
            # a parenthesised tactic sequence: `try (simpl; lia)`
            ld = _local_depth(seg[i:])
            e = next((q for q in range(1, len(ld)) if seg[i + q].k == "close" and ld[q] == 0), len(ld))
            part = []
            for q in range(1, e):
                u = seg[i + q]
                if u.t == ";" and ld[q] == 1:
                    if part:
                        _rocq_segment(part, heads, flags, part[0].line)
                    part = []
                else:
                    part.append(u)
            if part:
                _rocq_segment(part, heads, flags, part[0].line)
            return
        if t.k == "open" and t.t == "[":
            # `[tac | tac | ..]`: one tactic per goal; the head `dispatch`, then the heads of each alternative
            heads.append((line, "dispatch"))
            ld = _local_depth(seg[i:])
            e = next((q for q in range(1, len(ld)) if seg[i + q].k == "close" and ld[q] == 0), len(ld))
            part = []
            for q in range(1, e + 1):
                u = seg[i + q] if q < e else None
                if u is None or (u.t in ("|", "||") and ld[q] == 1):
                    if part and part[0].t not in (">",):
                        _rocq_segment(part, heads, flags, part[0].line)
                    part = []
                    if u is not None and u.t == "||":
                        part = []
                else:
                    part.append(u)
            return
        if t.k == "id":
            name, n2 = t.t, (nxt.t if nxt is not None else "")
            if name == "move":
                name = "move=>" if n2 == "=>" else "move:" if n2 == ":" else "move/" if n2.startswith("/") else "move"
            elif name in ("pose", "epose") and n2 == "proof":
                name = "pose_proof"
            elif name == "dependent" and n2 in ("destruction", "induction", "inversion", "rewrite"):
                name = "dependent_" + n2
            elif name == "functional" and n2 == "induction":
                name = "functional_induction"
            elif name == "typeclasses" and n2 == "eauto":
                name = "typeclasses_eauto"
            elif name == "simple" and n2 in ("apply", "eapply", "induction", "destruct", "inversion", "refine"):
                name = "simple_" + n2
            elif name == "decide" and n2 == "equality":
                name = "decide_equality"
            elif name == "without" and n2 == "loss":
                name = "wlog"
            elif name == "give_up":
                name = "give_up"
            heads.append((line, name))
            return
        if t.t == "=>":
            heads.append((line, "=>"))
            return
        heads.append((line, "«sym»"))
        return


def _rocq_segment(seg, heads, flags, line):
    """Heads of one `;`-segment, and of a closing `by tac` later in it (`have H : P by tac`)."""
    _rocq_segment_head(seg, heads, flags, line)
    ld = _local_depth(seg)
    for q in range(1, len(seg)):
        if seg[q].k == "id" and seg[q].t == "by" and ld[q] == 0:
            _rocq_segment(seg[q:], heads, flags, seg[q].line)
            break


def read_rocq_site(text):
    src = blank_comments(text, "rocq")
    toks = lex_rocq(src)
    out = {"n_tokens": len(toks), "toks": toks, "decls": [], "heads": [], "body": [], "mode": "none",
           "dialect": "rocq",
           "info": {"bullets": 0, "calc_steps": 0, "arms": 0, "by": 0, "alt": 0}, "closing": None}
    if not toks:
        return out
    sentences, cur = [], []
    for t in toks:
        if t.k == "dot":
            if cur:
                sentences.append(cur)
            cur = []
        else:
            cur.append(t)
    if cur:
        sentences.append(cur)
    in_proof, modes, last_head = None, [], None
    flags = out["info"]
    for s in sentences:
        k = 0
        while k < len(s) and ((s[k].k == "sym" and set(s[k].t) <= set("-+*")) or s[k].t in ("{", "}")):
            if s[k].t != "}":
                flags["bullets"] += 1
            k += 1
        s = s[k:]
        if not s:
            continue
        # goal selectors `2:`, `1-3:`, `all:`
        for q in range(min(4, len(s))):
            if s[q].t == ":" and q > 0 and all(u.k == "num" or u.t in ("all", "par", "-", ",") for u in s[:q]):
                s = s[q + 1:]
                break
        while s and s[0].t == "{":
            flags["bullets"] += 1
            s = s[1:]
        if not s:
            continue
        w, m = s[0].t, 0
        while m < len(s) and (s[m].t in ROCQ_MODS or s[m].t == "#" or (m and s[m - 1].t == "#")):
            m += 1
        if s[0].t == "#" and len(s) > 1 and s[1].t == "[":
            m = 1
            ld = _local_depth(s)
            while m < len(s) and not (s[m].k == "close" and ld[m] == 0):
                m += 1
            m += 1
            while m < len(s) and s[m].t in ROCQ_MODS:
                m += 1
        if m >= len(s):
            continue
        w = s[m].t
        if in_proof is None:
            in_proof = not (s[m].k == "id" and (w in _ROCQ_THEOREM or w in _ROCQ_VERNAC or w in _ROCQ_END))
            if in_proof:
                modes.append("fragment")
        if s[m].k == "id" and w in _ROCQ_THEOREM:
            ld = _local_depth(s)
            has_def = any(t.t == ":=" and ld[q] == 0 for q, t in enumerate(s))
            name = s[m + 1].t if m + 1 < len(s) and s[m + 1].k == "id" else None
            if has_def:
                a = next(q for q, t in enumerate(s) if t.t == ":=" and ld[q] == 0)
                out["decls"].append({"kind": w, "name": name, "mode": "term"})
                modes.append("term")
                out["heads"].append((s[a].line, "«term»"))
                out["body"] += s[a + 1:]
                last_head, in_proof = "«term»", False
            else:
                out["decls"].append({"kind": w, "name": name, "mode": "tactic"})
                in_proof = True
            continue
        if s[m].k == "id" and w in _ROCQ_END:
            if w in ("Admitted", "Abort"):
                out["heads"].append((s[m].line, w))
                last_head = w
            if out["decls"] and out["decls"][-1]["mode"] == "tactic":
                modes.append("tactic")
            out["closing"] = last_head
            in_proof = False
            continue
        if s[m].k == "id" and w == "Proof":
            rest = s[m + 1:]
            if rest and rest[0].t not in ("using", "with"):
                out["heads"].append((s[m].line, "«term»"))
                out["body"] += rest
                last_head = "«term»"
                if out["decls"]:
                    out["decls"][-1]["mode"] = "term"
            in_proof = True
            continue
        if s[m].k == "id" and w in ("Next", "Obligation", "Solve"):
            in_proof = True
            continue
        if not in_proof or (s[m].k == "id" and w in _ROCQ_VERNAC):
            continue
        # a tactic sentence
        ld = _local_depth(s)
        base = 0
        seg, segs = [], []
        for q, t in enumerate(s):
            if t.t == ";" and ld[q] == base:
                segs.append(seg)
                seg = []
            else:
                seg.append(t)
        segs.append(seg)
        before = len(out["heads"])
        for seg in segs:
            if seg:
                _rocq_segment(seg, out["heads"], flags, seg[0].line)
        # an intro pattern with alternatives: `[a | b]` after the head of a segment
        for seg in segs:
            sd = _local_depth(seg)
            for q, t in enumerate(seg):
                if t.t in ("|", "||") and sd[q] >= 1 and q > 0:
                    opener = next((seg[r] for r in range(q - 1, -1, -1) if seg[r].k == "open" and sd[r] == sd[q] - 1),
                                  None)
                    lead = seg[0].t
                    if opener is not None and opener.t == "[" and seg[0].k != "open" and lead not in ("first", "solve"):
                        flags["alt"] += 1
                        break
        out["body"] += s
        if len(out["heads"]) > before:
            last_head = out["heads"][-1][1]
    if in_proof:
        out["closing"] = last_head
        if out["decls"] and out["decls"][-1]["mode"] == "tactic":
            modes.append("tactic")
    kinds = [m for m in modes if m != "none"]
    out["mode"] = "none" if not kinds else kinds[0] if len(set(kinds)) == 1 else "mixed"
    return out


# ------------------------------------------------------------------ isabelle

ISAR_COMMANDS = {"proof", "qed", "next", "case", "assume", "fix", "have", "show", "thus", "hence", "obtain", "from",
                 "with", "using", "unfolding", "by", "apply", "done", "also", "finally", "moreover", "ultimately",
                 "then", "note", "let", "define", "consider", "interpret", "presume", "subgoal", "supply",
                 "including", "sorry", "oops", "apply_end", "back", "defer", "prefer", "write", "guess"}
_ISA_TOP = {"lemma", "theorem", "corollary", "proposition", "schematic_goal", "definition", "fun", "function",
            "primrec", "instance", "interpretation", "sublocale", "global_interpretation", "instantiation",
            "termination", "lemmas", "abbreviation", "inductive", "datatype", "locale", "context", "class",
            "crunch", "crunches", "declare", "notation", "type_synonym", "record", "end", "begin", "private",
            "qualified", "named_theorems", "method", "ML", "setup", "export_code", "value", "term", "thm",
            "theorems", "overloading", "bundle", "unbundle", "hide_const", "no_notation", "syntax",
            "translations", "consts", "axiomatization", "typedef", "lift_definition", "codatatype", "primcorec",
            "nominal_datatype", "partial_function", "specification", "experiment", "notepad", "print_theorems"}
_ISA_THEOREM = {"lemma", "theorem", "corollary", "proposition", "schematic_goal"}


def _isa_method_heads(group):
    """Method names inside one parenthesised method expression: the first identifier of the group and of each
    part after `,`, `;` or `|`, round brackets nested, square brackets skipped."""
    out, expect, sq = [], True, 0
    for t in group[1:-1]:
        if t.k == "open" and t.t == "[":
            sq += 1
            expect = False
            continue
        if t.k == "close" and t.t == "]":
            sq = max(0, sq - 1)
            continue
        if sq:
            continue
        if t.k == "open" and t.t == "(":
            continue
        if t.k == "close":
            continue
        if t.t in (",", ";", "|"):
            expect = True
            continue
        if expect:
            expect = False
            if t.k == "id":
                out.append(t)
            elif t.t == "-":
                out.append(t)
    # `(use facts in \<open>method\<close>)`: the method is inside the cartouche
    for k, t in enumerate(group[:-1]):
        if t.k == "id" and t.t == "in" and group[k + 1].k == "inner":
            sub = lex_isabelle("(" + group[k + 1].t + ")")
            for u in sub:
                u.line += group[k + 1].line - 1
            out += _isa_method_heads(sub)
    return out


def read_isabelle_site(text):
    src = blank_comments(text, "isabelle")
    toks = lex_isabelle(src)
    out = {"n_tokens": 0, "toks": toks, "decls": [], "heads": [], "body": [], "mode": "none", "dialect": "isar",
           "info": {"bullets": 0, "calc_steps": 0, "arms": 0, "by": 0, "apply": 0, "blocks": 0}, "closing": None}
    n_inner = 0
    for t in toks:
        if t.k == "inner":
            n_inner += len(lex_isabelle(t.t, inner=True))
    out["n_tokens"] = len(toks) - sum(1 for t in toks if t.k == "inner") + n_inner
    if not toks:
        return out
    n, i, pd = len(toks), 0, 0
    body_from, methods_seen, last_close = None, 0, None
    info = out["info"]

    def method_at(j):
        """(method head tokens, index after the method) for a method starting at j, or ([], j)."""
        if j >= n:
            return [], j
        t = toks[j]
        if t.k == "open" and t.t == "(":
            e = _group_end(toks, j)
            hs = _isa_method_heads(toks[j:e + 1])
            j = e + 1
        elif t.k == "id" and t.t not in ISAR_COMMANDS and t.t not in _ISA_TOP:
            hs, j = [t], j + 1
        elif t.t == "-" and t.k == "sym":
            hs, j = [t], j + 1
        else:
            return [], j
        while j < n and (toks[j].t in ("+", "?") or (toks[j].k == "open" and toks[j].t == "[")):
            j = _group_end(toks, j) + 1 if toks[j].k == "open" else j + 1
        return hs, j

    while i < n:
        t = toks[i]
        if t.k == "open" and t.t in "([":
            i = _group_end(toks, i) + 1
            continue
        if t.k in ("open", "close") and t.t in "{}":
            if t.t == "{":
                info["blocks"] += 1
                out["heads"].append((t.line, "{"))
            i += 1
            continue
        if t.k == "id" and t.t in _ISA_THEOREM | {"definition", "fun", "function", "primrec", "instance",
                                                 "interpretation", "sublocale", "global_interpretation",
                                                 "termination", "lemmas", "abbreviation"}:
            nm = toks[i + 1].t if i + 1 < n and toks[i + 1].k == "id" and toks[i + 1].t not in ISA_ELEM else None
            out["decls"].append({"kind": t.t, "name": nm, "mode": "none"})
            i += 1
            continue
        if t.k == "id" and t.t in ISAR_COMMANDS:
            if body_from is None:
                body_from = i
            out["heads"].append((t.line, t.t))
            if out["decls"]:
                out["decls"][-1]["mode"] = "tactic"
            j = i + 1
            if t.t in ("by", "apply", "proof", "qed", "apply_end"):
                info[t.t] = info.get(t.t, 0) + 1
                hs, j = method_at(j)
                for h in hs:
                    out["heads"].append((h.line, _isa_method_name(toks, h)))
                if t.t == "by":
                    hs2, j = method_at(j)
                    for h in hs2:
                        out["heads"].append((h.line, _isa_method_name(toks, h)))
            if t.t in ("by", "qed", "done", "sorry", "oops"):
                out["closing"] = out["heads"][-1][1]
            if t.t in ("also", "finally"):
                info["calc_steps"] += 1
            i = j
            continue
        if t.k == "sym" and t.t in (".", "..") and body_from is not None or (t.k == "sym" and t.t in (".", "..")
                                                                             and i and toks[i - 1].k == "inner"):
            if body_from is None:
                body_from = i
            out["heads"].append((t.line, t.t))
            out["closing"] = t.t
        i += 1
    if body_from is not None:
        out["body"] = toks[body_from:]
        out["mode"] = "tactic"
    return out


def _isa_method_name(toks, h):
    """`simp only: ...` is reported as `simp only`; every other method by its name."""
    k = next((q for q, u in enumerate(toks) if u is h), None)
    if k is not None and h.t == "simp" and k + 1 < len(toks) and toks[k + 1].t == "only":
        return "simp only"
    return h.t


def read_site(text, lang):
    """Proof steps of a site's text. Returns a dict: n_tokens, decls [{kind, name, mode}], heads [(line, name)]
    with line counted from the start of the text, body (tokens after the statement), mode, dialect, info, closing."""
    if lang == "lean":
        return read_lean_site(text)
    if lang == "rocq":
        return read_rocq_site(text)
    if lang == "isabelle":
        return read_isabelle_site(text)
    raise ValueError(lang)


# ============================================================ file-level context
#
# Two helpers that read a whole copied file: the names bound by section-level
# variable commands in force at a line, and the extent of the declaration that
# starts at a site whose recorded range stops at the statement.

_LEAN_SCOPE = re.compile(r"(?:(?:noncomputable|public|private)\s+)*(section|namespace)\b[ \t]*([^\s]*)")
_LEAN_VARIABLE = re.compile(r"(?:@\[[^\]]*\]\s*)?variable\b")


def lean_context_vars(file_text, line):
    """Names bound by `variable` commands whose section or namespace is still open at `line` (1-based).
    Scopes are followed by the `section`, `namespace` and `end` lines that start in column 0; a Lean 3 proof's
    `end` is told apart by the `begin` in column 0 that it closes. Auto-bound implicits are not seen."""
    lines = blank_comments(file_text, "lean").split("\n")
    stack, begins, i, stop = [[None, []]], 0, 0, min(line - 1, len(lines))
    while i < stop:
        ln = lines[i]
        m = _LEAN_SCOPE.match(ln)
        if m:
            stack.append([m.group(2) or None, []])
        elif re.match(r"begin\b", ln):
            begins += 1
        elif re.match(r"end\b", ln):
            name = ln[3:].strip() or None
            if begins and name is None:
                begins -= 1
            elif len(stack) > 1 and (name is None or stack[-1][0] is None
                                     or stack[-1][0].split(".")[-1] == name.split(".")[-1] or stack[-1][0] == name):
                stack.pop()
        elif _LEAN_VARIABLE.match(ln):
            chunk, j = ln, i + 1
            while j < len(lines) and lines[j][:1] in (" ", "\t") and lines[j].strip():
                chunk += "\n" + lines[j]
                j += 1
            toks = lex_lean(chunk)
            k = next((q for q, t in enumerate(toks) if t.t == "variable"), None)
            if k is not None:
                for item in top_items(toks[k + 1:]):
                    if len(item) > 1:
                        inner = item[1:-1]
                        c = _find(inner, {":"}) if inner else None
                        head = inner if c is None else inner[:c]
                        if item[0].t == "[" and c is None:
                            continue
                        stack[-1][1] += [t.t for t in head if t.k == "id" and t.t != "_"]
            i = j
            continue
        i += 1
    return sorted({nm for _n, names in stack for nm in names})


def rocq_context_vars(file_text, line):
    """Names bound by Variable(s), Context, Hypothesis and Hypotheses sentences whose Section or Module is still
    open at `line` (1-based)."""
    src = blank_comments(file_text, "rocq")
    cut = "\n".join(src.split("\n")[:max(0, line - 1)])
    toks = lex_rocq(cut)
    stack, cur, sentences = [[]], [], []
    for t in toks:
        if t.k == "dot":
            if cur:
                sentences.append(cur)
            cur = []
        else:
            cur.append(t)
    for s in sentences:
        k = 0
        while k < len(s) and s[k].t in ROCQ_MODS:
            k += 1
        if k >= len(s):
            continue
        w = s[k].t
        if w in ("Section", "Module") and not any(t.t == ":=" for t in s):
            stack.append([])
        elif w == "End" and len(stack) > 1:
            stack.pop()
        elif w in ("Variable", "Variables", "Hypothesis", "Hypotheses", "Context"):
            rest = s[k + 1:]
            if any(t.k == "open" for t in rest[:1]) or w == "Context":
                for item in top_items(rest):
                    if len(item) > 1:
                        inner = item[1:-1]
                        c = _find(inner, {":"}) if inner else None
                        if c is not None:
                            stack[-1] += [t.t for t in inner[:c] if t.k == "id" and t.t != "_"]
            else:
                ld = _local_depth(rest)
                c = next((q for q, t in enumerate(rest) if t.t == ":" and ld[q] == 0), len(rest))
                stack[-1] += [t.t for t in rest[:c] if t.k == "id" and t.t != "_"]
    return sorted({nm for names in stack for nm in names})


def context_vars(file_text, line, lang):
    if lang == "lean":
        return lean_context_vars(file_text, line)
    if lang == "rocq":
        return rocq_context_vars(file_text, line)
    return None


_LEAN_TOPLINE = re.compile(
    r"(?:@\[|/-|--|#|theorem\b|lemma\b|def\b|abbrev\b|instance\b|example\b|problem\b|structure\b|inductive\b"
    r"|class\b|axiom\b|namespace\b|section\b|end\b|open\b|variable\b|universe\b|private\b|protected\b"
    r"|noncomputable\b|set_option\b|attribute\b|macro\b|syntax\b|notation\b|local\b|scoped\b|export\b|mutual\b"
    r"|alias\b|snip\b|determine\b|import\b|omit\b|include\b|public\b|unsafe\b|opaque\b|irreducible_def\b|elab\b"
    r"|initialize\b|deriving\b|theory\b)")
_ISA_TOPLINE = re.compile(
    r"(?:lemma|theorem|corollary|proposition|schematic_goal|definition|fun|function|primrec|end|text|section"
    r"|subsection|subsubsection|paragraph|chapter|locale|context|instance|instantiation|interpretation|sublocale"
    r"|global_interpretation|datatype|codatatype|type_synonym|abbreviation|inductive|coinductive|declare|lemmas"
    r"|record|termination|crunch|crunches|method|ML|named_theorems|private|qualified|notation|no_notation"
    r"|hide_const|unbundle|bundle|syntax|translations|consts|axiomatization|typedef|lift_definition|experiment"
    r"|notepad|class|export_code|value|thm|term|setup|overloading|theory|nominal_datatype|primcorec"
    r"|partial_function|specification)\b")


def declaration_end(file_text, a, b, lang):
    """Last line (1-based) of the declaration that starts in lines a..b, found without parsing the proof:
    lean: the line before the next line that starts a top-level command in column 0 (a Lean 3 `begin` in column
    0 runs to the next `end` in column 0); rocq: the first line at or after `a` that holds a `Qed.`,
    `Defined.`, `Admitted.` or `Abort.` sentence; isabelle: the line before the next top-level command in
    column 0. Returns b when nothing is found."""
    src = blank_comments(file_text, lang).split("\n")
    raw = file_text.split("\n")
    n = len(src)
    if lang == "lean":
        j = b
        if j < n and re.match(r"begin\b", src[j]):
            while j < n and not re.match(r"end\b", src[j]):
                j += 1
            return min(n, j + 1)
        while j < n:
            if raw[j][:1] not in ("", " ", "\t") and _LEAN_TOPLINE.match(raw[j]):
                break
            j += 1
        while j > b and not src[j - 1].strip():
            j -= 1
        return j
    if lang == "rocq":
        for j in range(a - 1, min(n, a - 1 + 20000)):
            if re.search(r"(?:^|\s)(?:Qed|Defined|Admitted|Abort)\s*\.(?:\s|$)", src[j]):
                return max(b, j + 1)
        return b
    if lang == "isabelle":
        j = b
        while j < n:
            if src[j][:1] not in ("", " ", "\t") and _ISA_TOPLINE.match(src[j]):
                break
            j += 1
        while j > b and not src[j - 1].strip():
            j -= 1
        return j
    return b
