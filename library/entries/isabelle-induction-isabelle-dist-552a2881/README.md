# Induction on the reflected num datatype proves the linear normaliser linum correct

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | isabelle |
| Status | draft |
| Source | [isabelle-dist](../../sources/isabelle-dist/SOURCE.md) at `34ca456d44ca` |
| Licence | `BSD-3-Clause` |
| Licence recorded | 2026-11-12T16:06:53Z |

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
| build | not-run | Source isabelle-prover/mirror-isabelle (default branch master) has no CI workflow: GitHub API listing of the repo root shows no .github directory and no Jenkinsfile or other CI config (only .hgignore/.hgtags/Admin/bin/doc/etc/lib/src); it is a mirror of the Mercurial-based Isabelle distribution whose CI runs on Isabelle's own test infrastructure, outside this GitHub mirror. So no CI workflow path exists to cite for building src/HOL/Examples/Reflection_Examples.thy. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| glue-cites-children | pass | cited: lin_add@src/HOL/Examples/Reflection_Examples.thy:245, lin_mul@src/HOL/Examples/Reflection_Examples.thy:245; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 34ca456d44ca14641450b5d52f51b38688d4d1b5 | check_provenance.py | 2026-11-12 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none; oops (listed, not failed): src/HOL/Examples/Reflection_Examples.thy:67 (oops), src/HOL/Examples/Reflection_Examples.thy:82 (oops), src/HOL/Examples/Reflection_Examples.thy:90 (oops), src/HOL/Examples/Reflection_Examples.thy:127 (oops), src/HOL/Examples/Reflection_Examples.thy:132 (oops), src/HOL/Examples/Reflection_Examples.thy:163 (oops), src/HOL/Examples/Reflection_Examples.thy:171 (oops), src/HOL/Examples/Reflection_Examples.thy:180 (oops), src/HOL/Examples/Reflection_Examples.thy:186 (oops), src/HOL/Examples/Reflection_Examples.thy:200 (oops), src/HOL/Examples/Reflection_Examples.thy:251 (oops), src/HOL/Examples/Reflection_Examples.thy:287 (oops), ... (22 in all) | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read the copied file code/src/HOL/Examples/Reflection_Examples.thy (byte-identical at 34ca456d per check_provenance). Line 245 is 'by (induct t rule: linum.induct) (simp_all add: lin_mul lin_add)', naming lin_mul and lin_add; lin_add ends in 'done' at line 223 and lin_mul's proof ends at line 233. | verifier |
| 2 | verified | grep over the copied file: 22 'oops' occurrences at exactly lines 67,82,90,127,132,163,171,180,186,200,251,287,292,321,328,344,371,384,388,419,450,484 (all outside 135-245), and zero 'sorry'. Range 135-245 has no oops or sorry. | verifier |
| 3 | verified | Read lines 202-203 of the copied file: text block reads 'Okay, let's try reflection. Some simplifications on num follow. You can skim until the main theorem linum.' (with markup stripped), matching the quoted author statement. | verifier |
| 4 | verified | Read copied file: line 121 'by (induct p rule: nnf.induct) auto' (nnf lemma), and lines 315-316 'lemma linaform: ...' / 'by (induct p rule: linaform.induct) (auto simp add: linum)' which names linum as a leaf lemma. Both recurrences of the same induction-over-reflected-datatype move are present. | verifier |
| 5 | verified | Read copied file: linum glue proof is a single line 245; lin_add proof body is lines 220-223 (apply, apply, apply, done) = 4 lines; lin_mul proof is a single line 233. So direct_lemmas=2, depth=1, glue_lines=1, child_lines=[4,1] as claimed. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Decomposition and shape are sound: parent linum (L243-245) statement 'Inum (linum t) bs = Inum t bs' matches code and closes by 'by (induct t rule: linum.induct) (simp_all add: lin_mul lin_add)'; children lin_add (L218-223, closed by its two-argument induction + case_tac + algebra_simps) and lin_mul (L231-233, closed by lin_mul.induct + auto algebra_simps) match the code; they are exactly the two lemmas the main proof names; shape direct_lemmas=2 depth=1 glue_lines=1 child_lines=[4,1] is correct. Objection: claim 2 is refuted. It asserts 'the dependency cone (lines 135-245) contains no sorry or oops' and that 'every oops in the file lies outside this range', listing oops at 163, 171, 180, 186, 200 among the outside lines - but those five lines are inside 135-245 (grep confirms oops at exactly 67,82,90,127,132,163,171,180,186,200,251,287,292,321,328,344,371,384,388,419,450,484). The oops at 160-200 are unrelated reify demo lemmas, not linum's cone, so the underlying fact (linum's real cone is sorry/oops-free) is true, but the claim's line-range statement is false and self-contradictory. Fix: reword claim 2 to name linum's actual dependency cone (num L137-138, Inum L152-158, lin_add L205-223, lin_mul L225-233, linum L235-245) as sorry/oops-free, and correctly state that the file's oops (including 163,171,180,186,200, which sit between those ranges) are in the unrelated reify/demo lemmas. | reviewer-correctness |
| generality | accept | Move is stated to generalise beyond linum: applicability.goal_shape gives the parametric template 'I (f t) bs = I t bs' over a fun/primrec recursion f on a reflected datatype with interpretation I, and also_known_as plus claim 4 (known-use at nnf L121 and linaform L315-316, the latter reusing linum as a leaf) show the same induction-over-reflected-datatype move recurring, so it is not tied to this example. 'when not to use' is honest and specific: avoid when helpers depend on each other or the main theorem (breaks the acyclic depth-1 graph), when a helper is single-use and trivial (inline it), or when a case needs a parameter fixed (state an explicit arbitrary:). Consequences are specific and trace to the code: one obligation per helper or simp_all stalls; bs must be generalised over the induction (fixing it breaks recursive cases); the CN case needs both helpers because linum recurses through a Mul inside an Add; each helper must state exactly the rewrite simp_all needs. The README states what makes the children good leaves for a bounded prover: each is self-contained with a free environment list, closes without naming any further project lemma (own f.induct + case_tac + algebra_simps/Let_def), and the helper graph is acyclic at depth 1. | reviewer-generality |
| provenance-licence | accept | Provenance pass (check_provenance.py): the single copied file code/src/HOL/Examples/Reflection_Examples.thy is byte-identical at pinned commit 34ca456d44ca14641450b5d52f51b38688d4d1b5. Commit is consistent across entry.json source.commit, sources/isabelle-dist/SOURCE.md, source.json and ledger. Licence BSD-3-Clause is consistent across entry.json, README, SOURCE.md and source.json, and upstream-COPYRIGHT is the standard 3-clause BSD text. All permalinks (blob/ at the pinned commit) point at the same repo/path and their cited line ranges match the copied file exactly (parent 243-245; children 218-223, 231-233; contexts 137-138, 152-158, 205-216, 225-229, 235-241). README and SOURCE.md both state the code is copied whole and unmodified under BSD-3-Clause. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/isabelle-prover/mirror-isabelle at commit `34ca456d44ca14641450b5d52f51b38688d4d1b5`, under `BSD-3-Clause`; see the [source note](../../sources/isabelle-dist/SOURCE.md) for the licence text and attribution.
