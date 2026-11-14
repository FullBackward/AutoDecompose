# Reduce-solve-transfer proves the Cubic Formula

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | isabelle |
| Status | draft |
| Source | [isabelle-dist](../../sources/isabelle-dist/SOURCE.md) at `34ca456d44ca` |
| Licence | `BSD-3-Clause` |
| Licence recorded | 2026-11-14T10:49:34Z |

## Intent

Prove the closed-form Cubic Formula by a reduce-solve-transfer composition. The
main theorem `cubic` does not solve the general cubic directly; its proof first
reduces the equation `a * x^3 + b * x^2 + c * x + d = 0` to the depressed form
`y^3 + 3 * p * y - 2 * q = 0` (via `cubic_reduction`), then invokes the
solution of that depressed form in terms of three candidate roots `s1, s2, s3`
(via `cubic_basic`, whose cube-root witness comes from `ccbrt`), and finally
transfers the answer back to `x` through the same substitution and a last case
split on `p = 0`.

## The decomposition

### parent `cubic`: [`src/HOL/ex/Cubic_Quartic.thy` lines 88-137](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/ex/Cubic_Quartic.thy#L88-L137) ([local copy](code/src/HOL/ex/Cubic_Quartic.thy))

```isabelle
lemma cubic:
  assumes a0: "a \<noteq> 0"
  shows
    "let
      p = (3 * a * c - b^2) / (9 * a^2);
      q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3);
      s = csqrt(q^2 + p^3);
      s1 = (if p = 0 then ccbrt(2 * q) else ccbrt(q + s));
      s2 = -s1 * (1 + \<i> * csqrt 3) / 2;
      s3 = -s1 * (1 - \<i> * csqrt 3) / 2
     in
      if p = 0 then
        a * x^3 + b * x^2 + c * x + d = 0 \<longleftrightarrow>
          x = s1 - b / (3 * a) \<or>
          x = s2 - b / (3 * a) \<or>
          x = s3 - b / (3 * a)
      else
        s1 \<noteq> 0 \<and>
          (a * x^3 + b * x^2 + c * x + d = 0 \<longleftrightarrow>
            x = s1 - p / s1 - b / (3 * a) \<or>
            x = s2 - p / s2 - b / (3 * a) \<or>
            x = s3 - p / s3 - b / (3 * a))"
proof -
  let ?p = "(3 * a * c - b^2) / (9 * a^2)"
  let ?q = "(9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3)"
  let ?s = "csqrt (?q^2 + ?p^3)"
  let ?s1 = "if ?p = 0 then ccbrt(2 * ?q) else ccbrt(?q + ?s)"
  let ?s2 = "- ?s1 * (1 + \<i> * csqrt 3) / 2"
  let ?s3 = "- ?s1 * (1 - \<i> * csqrt 3) / 2"
  let ?y = "x + b / (3 * a)"
  from a0 have zero: "9 * a^2 \<noteq> 0" "a^3 * 54 \<noteq> 0" "(a * 3) \<noteq> 0"
    by auto
  have eq: "a * x^3 + b * x^2 + c * x + d = 0 \<longleftrightarrow> ?y^3 + 3 * ?p * ?y - 2 * ?q = 0"
    by (rule cubic_reduction) (auto simp add: field_simps zero a0)
  have "csqrt 3^2 = 3" by (rule power2_csqrt)
  then have th0:
    "?s^2 = ?q^2 + ?p ^ 3 \<and> ?s1^ 3 = (if ?p = 0 then 2 * ?q else ?q + ?s) \<and>
      ?s2 = - ?s1 * (1 + \<i> * csqrt 3) / 2 \<and>
      ?s3 = - ?s1 * (1 - \<i> * csqrt 3) / 2 \<and>
      \<i>^2 + 1 = 0 \<and> csqrt 3^2 = 3"
    using zero by (simp add: field_simps ccbrt)
  from cubic_basic[OF th0, of ?y]
  show ?thesis
    apply (simp only: Let_def eq)
    using zero apply (simp add: field_simps ccbrt)
    using zero
    apply (cases "a * (c * 3) = b^2")
    apply (simp_all add: field_simps)
    done
qed
```

### child `ccbrt`: [`src/HOL/ex/Cubic_Quartic.thy` lines 15-27](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/ex/Cubic_Quartic.thy#L15-L27) ([local copy](code/src/HOL/ex/Cubic_Quartic.thy))

```isabelle
lemma ccbrt: "(ccbrt z) ^ 3 = z"
proof -
  from rcis_Ex obtain r a where ra: "z = rcis r a"
    by blast
  let ?r' = "if r < 0 then - root 3 (-r) else root 3 r"
  let ?a' = "a/3"
  have "rcis ?r' ?a' ^ 3 = rcis r a"
    by (cases "r < 0") (simp_all add: DeMoivre2)
  then have *: "\<exists>w. w^3 = z"
    unfolding ra by blast
  from someI_ex [OF *] show ?thesis
    unfolding ccbrt_def by blast
qed
```

### child `cubic_reduction`: [`src/HOL/ex/Cubic_Quartic.thy` lines 32-48](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/ex/Cubic_Quartic.thy#L32-L48) ([local copy](code/src/HOL/ex/Cubic_Quartic.thy))

```isabelle
lemma cubic_reduction:
  fixes a :: complex
  assumes
    "a \<noteq> 0 \<and> x = y - b / (3 * a) \<and>  p = (3* a * c - b^2) / (9 * a^2) \<and>
      q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3)"
  shows "a * x^3 + b * x^2 + c * x + d = 0 \<longleftrightarrow> y^3 + 3 * p * y - 2 * q = 0"
proof -
  from assms have "3 * a \<noteq> 0" "9 * a^2 \<noteq> 0" "54 * a^3 \<noteq> 0" by auto
  then have *:
      "x = y - b / (3 * a) \<longleftrightarrow> (3*a) * x = (3*a) * y - b"
      "p = (3* a * c - b^2) / (9 * a^2) \<longleftrightarrow> (9 * a^2) * p = (3* a * c - b^2)"
      "q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3) \<longleftrightarrow>
        (54 * a^3) * q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d)"
    by (simp_all add: field_simps)
  from assms [unfolded *] show ?thesis
    by algebra
qed
```

### child `cubic_basic`: [`src/HOL/ex/Cubic_Quartic.thy` lines 53-83](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/ex/Cubic_Quartic.thy#L53-L83) ([local copy](code/src/HOL/ex/Cubic_Quartic.thy))

```isabelle
lemma cubic_basic:
  fixes s :: complex
  assumes
    "s^2 = q^2 + p^3 \<and>
      s1^3 = (if p = 0 then 2 * q else q + s) \<and>
      s2 = -s1 * (1 + i * t) / 2 \<and>
      s3 = -s1 * (1 - i * t) / 2 \<and>
      i^2 + 1 = 0 \<and>
      t^2 = 3"
  shows
    "if p = 0
     then y^3 + 3 * p * y - 2 * q = 0 \<longleftrightarrow> y = s1 \<or> y = s2 \<or> y = s3
     else s1 \<noteq> 0 \<and>
      (y^3 + 3 * p * y - 2 * q = 0 \<longleftrightarrow> (y = s1 - p / s1 \<or> y = s2 - p / s2 \<or> y = s3 - p / s3))"
proof (cases "p = 0")
  case True
  with assms show ?thesis
    by (simp add: field_simps) algebra
next
  case False
  with assms have *: "s1 \<noteq> 0" by (simp add: field_simps) algebra
  with assms False have "s2 \<noteq> 0" "s3 \<noteq> 0"
    by (simp_all add: field_simps) algebra+
  with * have **:
      "y = s1 - p / s1 \<longleftrightarrow> s1 * y = s1^2 - p"
      "y = s2 - p / s2 \<longleftrightarrow> s2 * y = s2^2 - p"
      "y = s3 - p / s3 \<longleftrightarrow> s3 * y = s3^2 - p"
    by (simp_all add: field_simps power2_eq_square)
  from assms False show ?thesis
    unfolding ** by (simp add: field_simps) algebra
qed
```

### context `ccbrt-def`: [`src/HOL/ex/Cubic_Quartic.thy` lines 13-13](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/ex/Cubic_Quartic.thy#L13-L13) ([local copy](code/src/HOL/ex/Cubic_Quartic.thy))

```isabelle
definition "ccbrt z = (SOME (w::complex). w^3 = z)"
```

How the parts fit. The glue of `cubic` is a reduce-solve-transfer composition
over three project lemmas, all proved earlier in the same file. The lemma graph
is a star of depth 1: `cubic` uses each of the three children directly, and no
child uses another project lemma.

```
cubic_reduction (reduce)      ccbrt (witness)      cubic_basic (solve)
      |                          |                      |
      +------------+-------------+----------------------+
                   v
        cubic (parent: instantiate and transfer back)
```

- **`cubic_reduction` (reduce).** Rewrites the general cubic
  `a * x^3 + b * x^2 + c * x + d = 0` into the depressed form
  `y^3 + 3 * p * y - 2 * q = 0` under `x = y - b / (3 * a)` and the definitions
  of `p` and `q`. The glue applies it with
  `by (rule cubic_reduction) (auto simp add: field_simps zero a0)` (line 121) to
  get `eq`, the reduction of the goal to `?y`-coordinates. Its proof closes on
  its own: the three divisions in the assumptions are turned into products with
  `field_simps`, then `from assms [unfolded *] show ?thesis by algebra`.

- **`ccbrt` (witness).** Proves that the `ccbrt` definition (line 13,
  `SOME w. w^3 = z`) really is a cube root: `(ccbrt z) ^ 3 = z`. The glue uses
  it (`by (simp add: field_simps ccbrt)`, line 128), together with
  `power2_csqrt`, to assemble `th0` — the instantiation of the root candidates
  `s1, s2, s3` that `cubic_basic` needs. Its proof closes on its own: `rcis_Ex`
  gives the polar form, `DeMoivre2` builds the cube-root witness, and
  `someI_ex` discharges the `SOME`.

- **`cubic_basic` (solve).** Solves the depressed form: when `p = 0` it proves
  `y^3 + 3 * p * y - 2 * q = 0 <-> y = s1 | y = s2 | y = s3`, and when
  `p <> 0` the analogous `y = si - p / si` disjunction (with `s1 <> 0`). The
  glue applies it with `from cubic_basic[OF th0, of ?y]` (line 129). Its proof
  closes on its own by a case split on `p = 0`, each branch finished with
  `(simp add: field_simps) algebra`.

The final `show ?thesis` block (lines 130-136) is the transfer: it unfolds the
`let`-bound `p, q, s, s1, s2, s3`, rewrites `eq` back into the goal, and does a
last case split on `a * (c * 3) = b^2` — which is exactly `?p = 0` re-expressed
in the original coefficients — to match `cubic_basic`'s own branch on `p = 0`.
Each of the three children is a good leaf: a self-contained statement whose
proof closes without referring to any other project lemma, so each one is a
bounded hole an independent prover could fill.

## Why it is good

1. The parent site `cubic` is 50 lines long (lines 88-137) — *check*,
   `lines(cubic, 50)`, decided by `check_claims.py`.
2. The glue cites the reduce lemma: `cubic_reduction` occurs in the parent site
   `cubic` (line 121) — *check*, `cites(cubic, cubic_reduction)`.
3. The glue cites the solve lemma: `cubic_basic` occurs in the parent site
   `cubic` (line 129) — *check*, `cites(cubic, cubic_basic)`.
4. The shape is a shallow star: `cubic` uses exactly three direct project
   lemmas (`cubic_reduction`, `ccbrt`, `cubic_basic`), the longest chain of
   project lemmas below it has depth 1 (none of the three children cites
   another project lemma), and the sites are 50 lines for the parent and 13, 17
   and 31 lines for the children — *measurement*, counted in the copied file
   (parent lines 88-137; children 15-27, 32-48, 53-83).
5. The author labels the three stages in the file: "The reduction to a simpler
   form" (line 30), "The solutions of the special form" (line 51), and
   "Explicit formula for the roots" (line 86) — *author-statement*.

In my opinion the detail worth copying is that the reduction is stated as an
iff (`<->`) and the normal form is solved as its own lemma, so the glue is only
instantiation and rewriting: the parent never re-does the algebra of the
depressed form. That is why the three children can each be a self-contained
leaf of the kind a bounded prover fills independently.

The move is not one of the vocabulary's named moves, so it is recorded as
`other`; against survey F section 10 I read it as supporting rule 8 (backward
rule and witnesses as templates): the glue is assembled by applying each child
as a backward rule (`by (rule cubic_reduction)`, `from cubic_basic[OF th0]`),
and `ccbrt` is the `SOME`-witness whose existence the glue needs before it can
use the value. That mapping is my judgement, not a claim.

## When to use it, and when not

Use it when a target equation reduces by an invertible change of variable to a
normal form with a known, self-contained solution. The reduction must be an
equivalence (`<->`), so that the transfer back is pure rewriting, and the
normal form's solution plus the witness that makes it concrete must be
stateable as their own lemmas with no reference to the original goal. Avoid it
when the reduction is one-way (an implication only), because then the normal
form's solutions need not be the original's; when the normal form's solution
needs the original goal's hypotheses (so it cannot be stated separately); or
when the transfer step itself is non-trivial and would need its own lemma.

## Consequences

The move creates three obligations — the reduction equivalence
(`cubic_reduction`), the witness (`ccbrt`), and the normal-form solution
(`cubic_basic`) — after which the glue only instantiates and rewrites. The
transfer depends on the branch condition `p = 0` vs `p <> 0` being expressed
consistently in the normal-form lemma (there `p = 0` directly) and in the glue
(there re-expressed as `a * (c * 3) = b^2`); a mismatch between the two branch
conditions breaks the final `cases` step. The witness `ccbrt` is defined with
`SOME`, so the glue can use it only because the lemma `ccbrt` has already
discharged its existence obligation; without that lemma the value of `ccbrt` is
under-determined.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: ccbrt@src/HOL/ex/Cubic_Quartic.thy:95, cubic_reduction@src/HOL/ex/Cubic_Quartic.thy:121, cubic_basic@src/HOL/ex/Cubic_Quartic.thy:129; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(cubic, 50) -> lines: site cubic has 50 lines | check_claims.py |
| 2 | verified | cites(cubic, cubic_reduction) -> cites: cubic_reduction occurs at src/HOL/ex/Cubic_Quartic.thy:121 | check_claims.py |
| 3 | verified | cites(cubic, cubic_basic) -> cites: cubic_basic occurs at src/HOL/ex/Cubic_Quartic.thy:129 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/isabelle-prover/mirror-isabelle at commit `34ca456d44ca14641450b5d52f51b38688d4d1b5`, under `BSD-3-Clause`; see the [source note](../../sources/isabelle-dist/SOURCE.md) for the licence text and attribution.
