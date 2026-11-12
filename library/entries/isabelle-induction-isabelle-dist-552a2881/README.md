# Induction on the reflected num datatype proves the linear normaliser linum correct

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | isabelle |
| Status | draft |
| Source | [isabelle-dist](../../sources/isabelle-dist/SOURCE.md) at `34ca456d44ca` |
| Licence | `BSD-3-Clause` |

## Intent

Prove the correctness of the linear-arithmetic normaliser `linum` — the
reflection target the chapter builds up to — by one structural induction over
the reflected `num` datatype. Each non-trivial constructor is discharged by the
matching helper lemma written immediately above it (`lin_add` for `Add` and
`CN`, `lin_mul` for `Mul`), both fed to `simp_all`, so the main proof is a
single line.

## The decomposition

### parent `linum`: [`src/HOL/Examples/Reflection_Examples.thy` lines 243-245](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Reflection_Examples.thy#L243-L245) ([local copy](code/src/HOL/Examples/Reflection_Examples.thy))

```isabelle
lemma linum [reflection]:
  "Inum (linum t) bs = Inum t bs"
  by (induct t rule: linum.induct) (simp_all add: lin_mul lin_add)
```

### child `lin_add`: [`src/HOL/Examples/Reflection_Examples.thy` lines 218-223](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Reflection_Examples.thy#L218-L223) ([local copy](code/src/HOL/Examples/Reflection_Examples.thy))

```isabelle
lemma lin_add:
  "Inum (lin_add t s) bs = Inum (Add t s) bs"
  apply (induct t s rule: lin_add.induct, simp_all add: Let_def)
  apply (case_tac "c1+c2 = 0",case_tac "n1 \<le> n2", simp_all)
  apply (case_tac "n1 = n2", simp_all add: algebra_simps)
  done
```

### child `lin_mul`: [`src/HOL/Examples/Reflection_Examples.thy` lines 231-233](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Reflection_Examples.thy#L231-L233) ([local copy](code/src/HOL/Examples/Reflection_Examples.thy))

```isabelle
lemma lin_mul:
  "Inum (lin_mul t i) bs = Inum (Mul i t) bs"
  by (induct t i rule: lin_mul.induct) (auto simp add: algebra_simps)
```

### context `num-datatype`: [`src/HOL/Examples/Reflection_Examples.thy` lines 137-138](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Reflection_Examples.thy#L137-L138) ([local copy](code/src/HOL/Examples/Reflection_Examples.thy))

```isabelle
text \<open>The type \<open>num\<close> reflects linear expressions over natural number\<close>
datatype num = C nat | Add num num | Mul nat num | Var nat | CN nat nat num
```

### context `Inum`: [`src/HOL/Examples/Reflection_Examples.thy` lines 152-158](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Reflection_Examples.thy#L152-L158) ([local copy](code/src/HOL/Examples/Reflection_Examples.thy))

```isabelle
primrec Inum:: "num \<Rightarrow> nat list \<Rightarrow> nat"
where
  Inum_C  : "Inum (C i) vs = i"
| Inum_Var: "Inum (Var n) vs = vs!n"
| Inum_Add: "Inum (Add s t) vs = Inum s vs + Inum t vs "
| Inum_Mul: "Inum (Mul c t) vs = c * Inum t vs "
| Inum_CN : "Inum (CN n c t) vs = c*(vs!n) + Inum t vs "
```

### context `lin_add-def`: [`src/HOL/Examples/Reflection_Examples.thy` lines 205-216](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Reflection_Examples.thy#L205-L216) ([local copy](code/src/HOL/Examples/Reflection_Examples.thy))

```isabelle
fun lin_add :: "num \<Rightarrow> num \<Rightarrow> num"
where
  "lin_add (CN n1 c1 r1) (CN n2 c2 r2) =
    (if n1 = n2 then 
      (let c = c1 + c2
       in (if c = 0 then lin_add r1 r2 else CN n1 c (lin_add r1 r2)))
     else if n1 \<le> n2 then (CN n1 c1 (lin_add r1 (CN n2 c2 r2))) 
     else (CN n2 c2 (lin_add (CN n1 c1 r1) r2)))"
| "lin_add (CN n1 c1 r1) t = CN n1 c1 (lin_add r1 t)"  
| "lin_add t (CN n2 c2 r2) = CN n2 c2 (lin_add t r2)" 
| "lin_add (C b1) (C b2) = C (b1 + b2)"
| "lin_add a b = Add a b"
```

### context `lin_mul-def`: [`src/HOL/Examples/Reflection_Examples.thy` lines 225-229](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Reflection_Examples.thy#L225-L229) ([local copy](code/src/HOL/Examples/Reflection_Examples.thy))

```isabelle
fun lin_mul :: "num \<Rightarrow> nat \<Rightarrow> num"
where
  "lin_mul (C j) i = C (i * j)"
| "lin_mul (CN n c a) i = (if i=0 then (C 0) else CN n (i * c) (lin_mul a i))"
| "lin_mul t i = (Mul i t)"
```

### context `linum-def`: [`src/HOL/Examples/Reflection_Examples.thy` lines 235-241](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Reflection_Examples.thy#L235-L241) ([local copy](code/src/HOL/Examples/Reflection_Examples.thy))

```isabelle
fun linum:: "num \<Rightarrow> num"
where
  "linum (C b) = C b"
| "linum (Var n) = CN n 1 (C 0)"
| "linum (Add t s) = lin_add (linum t) (linum s)"
| "linum (Mul c t) = lin_mul (linum t) c"
| "linum (CN n c t) = lin_add (linum (Mul c (Var n))) (linum t)"
```

How the parts fit. The lemma graph is a two-level tree:

```
linum   (parent, lines 243-245)
 ├─ lin_add   (child, lines 218-223)   — used by the Add and CN cases
 └─ lin_mul   (child, lines 231-233)   — used by the Mul case (and the CN case via the inner Mul)
```

`linum` unfolds the normaliser over the five constructors of `num`
(`C`, `Var`, `Add`, `Mul`, `CN`; see the `num-datatype` and `linum-def`
excerpts above). The proof is one structural induction `induct t rule:
linum.induct`, followed by `simp_all add: lin_mul lin_add`. The base-like `C`
and `Var` cases close by rewriting with the `Inum` equations alone; the three
recursive cases each reduce to a form the helpers are stated for:

- **Add** — `linum (Add t s) = lin_add (linum t) (linum s)`, so `lin_add`
  rewrites `Inum (lin_add …) bs` to `Inum (Add …) bs`, and the induction
  hypotheses close `linum t` and `linum s`.
- **Mul** — `linum (Mul c t) = lin_mul (linum t) c`, so `lin_mul` rewrites to
  `Inum (Mul c …) bs`, and the IH closes `linum t`.
- **CN** — `linum (CN n c t) = lin_add (linum (Mul c (Var n))) (linum t)`,
  which needs both `lin_add` (outer) and, through the inner
  `linum (Mul c (Var n))`, `lin_mul`; the IH closes `linum t` and
  `linum (Mul c (Var n))`.

Each child is a good leaf because its statement is self-contained (about
`lin_add`/`lin_mul` alone, with a free environment list `bs`) and its proof
closes without naming any further project lemma:

- `lin_add` closes by its own two-argument induction `lin_add.induct` (five
  cases from the five defining equations), plus two `case_tac`s to unfold the
  `if` guards (`c1+c2 = 0`, `n1 ≤ n2`, `n1 = n2`), finished with
  `algebra_simps`.
- `lin_mul` closes by its own induction `lin_mul.induct` (three cases) with
  `auto simp add: algebra_simps`.

Neither helper references `linum` or the other helper, so the dependency graph
is acyclic with both helpers at depth 1.

In my opinion the detail worth copying is that the helpers are stated to match
*exactly* the rewrite `simp_all` needs — `Inum (lin_add a b) bs =
Inum (Add a b) bs` — so the main induction never unfolds `lin_add` or
`lin_mul`; it only instantiates their correctness statements.

## Why it is good

1. **Check** — the parent `linum` closes from its two children: the one-line
   proof `by (induct t rule: linum.induct) (simp_all add: lin_mul lin_add)`
   (line 245) names `lin_mul` and `lin_add`, and both children are proved just
   above in the same file (`lin_add` ends in `done` at line 223, `lin_mul` at
   line 233).
2. **Check** — the dependency cone (lines 135-245, from "Example 2: Simple
   arithmetic formulae" through the `linum` lemma) contains no `sorry` or
   `oops`; every `oops` in the file lies outside this range.
3. **Author-statement** — the author flags `linum` as the chapter's main
   theorem: "Okay, let's try reflection. Some simplifications on num follow.
   You can skim until the main theorem linum." (lines 202-203).
4. **Known use** — the same move (correctness of a reflected simplifier by
   induction over the reflected datatype) recurs in the file: `nnf` is proved
   by `(induct p rule: nnf.induct) auto` (line 121), and `linaform` by
   `(induct p rule: linaform.induct) (auto simp add: linum)` (lines 315-316),
   which reuses `linum` itself as a leaf lemma.
5. **Measurement** — the glue proof is 1 line (245) while the two child proofs
   are 4 lines (`lin_add`, 220-223) and 1 line (`lin_mul`, 233); the shape is
   `direct_lemmas = 2`, `depth = 1`, `glue_lines = 1`, `child_lines = [4, 1]`.

## When to use it, and when not

Use it when you are proving a normaliser or simplifier correct — a goal of the
shape `I (f t) bs = I t bs`, where `f` is a `fun`/`primrec` recursion over a
reflected datatype `num` and `I` is the interpretation into the host type.
`f.induct` then gives one case per constructor, and each non-trivial
constructor reduces to a distinct helper (`lin_add`, `lin_mul`) whose
correctness can be stated and proved first as its own lemma, then fed to
`simp_all`.

Avoid it when the helpers depend on each other or on the main theorem (that
breaks the acyclic, depth-1 graph), when a helper is used once and is trivial
(fold it inline instead), or when a case needs the environment list or another
parameter fixed — then state an explicit `arbitrary:` on the induction. Here
`bs` is generalised automatically because it does not occur in the induction
variable `t`.

## Consequences

The move creates one obligation per helper: `lin_add` and `lin_mul` must each
be proved before the main induction, or `simp_all` stalls on the `Add`/`Mul`/
`CN` cases. The main induction is over `t` with the environment `bs`
generalised; fixing `bs` would break the recursive cases. The `CN` case needs
both helpers because `linum` recurses through a `Mul` inside an `Add`
(`lin_add (linum (Mul c (Var n))) (linum t)`), so a helper stated only for a
top-level constructor would not cover it. Each helper must state exactly the
rewrite `simp_all` needs (`Inum (lin_add a b) bs = Inum (Add a b) bs`); a
mismatched or missing equation leaves the goal unsimplified.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/isabelle-prover/mirror-isabelle at commit `34ca456d44ca14641450b5d52f51b38688d4d1b5`, under `BSD-3-Clause`; see the [source note](../../sources/isabelle-dist/SOURCE.md) for the licence text and attribution.
