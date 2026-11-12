# Adequacy of sstriple by case split on the four continuations

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | isabelle |
| Status | accepted |
| Source | [autocorrode](../../sources/autocorrode/SOURCE.md) at `200f1acf2d26` |
| Licence | `MIT` |

## Intent

Reduce the headline adequacy theorem — a Hoare triple (`sstriple`) over the
non-deterministic evaluator implies the post-condition for every possible
continuation — to a case split on the four `continuation` constructors:
Success, Return and Abort are dispatched to the three per-constructor adequacy
lemmas, and Yield is discharged as impossible by `deep_evaluate_basic_no_yield'`.

## The decomposition

### parent `sstriple_adequacy`: [`Shallow_Separation_Logic/Adequacy.thy` lines 53-66](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Adequacy.thy#L53-L66) ([local copy](code/Shallow_Separation_Logic/Adequacy.thy))

```isabelle
lemma sstriple_adequacy:
  assumes \<open>\<Gamma> ; \<xi> \<turnstile> e \<stileturn> \<phi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>c \<in> deep_evaluates_nondet_basic (yield_handler \<Gamma>) e \<sigma>\<close>
    shows \<open>case c of
            continuation.Success v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<phi> v
          | continuation.Return v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<rho> v
          | continuation.Abort a \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<theta> a
          | continuation.Yield _ _ _ \<Rightarrow> False\<close>
  \<comment> \<open>Evaluating with \<^term>\<open>deep_evaluates_nondet_basic\<close> will never terminate in \<^term>\<open>Yield\<close>\<close>
  using assms
  by (auto simp add: sstriple_def deep_evaluate_basic_no_yield'
      atriple_rel_eval_value_adequacy atriple_rel_eval_return_adequacy
      atriple_rel_eval_abort_adequacy split: continuation.splits)
```

### child `atriple_rel_eval_value_adequacy`: [`Shallow_Separation_Logic/Adequacy.thy` lines 31-36](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Adequacy.thy#L31-L36) ([local copy](code/Shallow_Separation_Logic/Adequacy.thy))

```isabelle
lemma atriple_rel_eval_value_adequacy:
  assumes \<open>\<xi> \<turnstile> eval_value Y e \<stileturn>\<^sub>R \<phi>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>continuation.Success v \<sigma>' \<in> deep_evaluates_nondet_basic Y e \<sigma>\<close>
    shows \<open>\<sigma>' \<Turnstile> \<phi> v\<close>
  using assms by (auto simp add: atriple_rel_def eval_value_def urust_eval_predicate_defs)
```

### child `atriple_rel_eval_return_adequacy`: [`Shallow_Separation_Logic/Adequacy.thy` lines 38-43](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Adequacy.thy#L38-L43) ([local copy](code/Shallow_Separation_Logic/Adequacy.thy))

```isabelle
lemma atriple_rel_eval_return_adequacy:
  assumes \<open>\<xi> \<turnstile> eval_return Y e \<stileturn>\<^sub>R \<phi>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>continuation.Return v \<sigma>' \<in> deep_evaluates_nondet_basic Y e \<sigma>\<close>
    shows \<open>\<sigma>' \<Turnstile> \<phi> v\<close>
  using assms by (auto simp add: atriple_rel_def eval_return_def urust_eval_predicate_defs)
```

### child `atriple_rel_eval_abort_adequacy`: [`Shallow_Separation_Logic/Adequacy.thy` lines 45-50](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Adequacy.thy#L45-L50) ([local copy](code/Shallow_Separation_Logic/Adequacy.thy))

```isabelle
lemma atriple_rel_eval_abort_adequacy:
  assumes \<open>\<xi> \<turnstile> eval_abort Y e \<stileturn>\<^sub>R \<phi>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>continuation.Abort a \<sigma>' \<in> deep_evaluates_nondet_basic Y e \<sigma>\<close>
    shows \<open>\<sigma>' \<Turnstile> \<phi> a\<close>
  using assms by (auto simp add: atriple_rel_def eval_abort_def urust_eval_predicate_defs)
```

### child `deep_evaluate_basic_no_yield'`: [`Shallow_Micro_Rust/Core_Expression_Lemmas.thy` lines 77-79](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Micro_Rust/Core_Expression_Lemmas.thy#L77-L79) ([local copy](code/Shallow_Micro_Rust/Core_Expression_Lemmas.thy))

```isabelle
lemma deep_evaluate_basic_no_yield':
  shows \<open>Yield \<pi> \<sigma>' e' \<in> deep_evaluates_nondet_basic y e \<sigma> \<longleftrightarrow> False\<close>
using deep_evaluate_basic_no_yield by force
```

How the parts fit. The parent `sstriple_adequacy` (Adequacy.thy 53-66) is the
headline adequacy theorem; its proof is one `auto` call that works in two
stages. First `simp add: sstriple_def` unfolds the triple — defined in
[`Triple.thy` 35-46](code/Shallow_Separation_Logic/Triple.thy) — into a
conjunction of three exact-triple hypotheses:

```
ξ ⊢ eval_value  (yh Γ) e ⨝R φ
ξ ⊢ eval_return (yh Γ) e ⨝R ρ
ξ ⊢ eval_abort  (yh Γ) e ⨝R θ
```

Second, `split: continuation.splits` produces one goal per constructor of the
`continuation` datatype, and `auto` dispatches each:

```
Success v σ'  → atriple_rel_eval_value_adequacy   (31-36)
Return  v σ'  → atriple_rel_eval_return_adequacy  (38-43)
Abort   a σ'  → atriple_rel_eval_abort_adequacy   (45-50)
Yield _ _ _   → deep_evaluate_basic_no_yield'     (Core_Expression_Lemmas.thy 77-79)
```

The lemma graph is flat: the glue cites the four children directly, and no
child cites another child. The one non-trivial edge leaves the file —
`deep_evaluate_basic_no_yield'` closes from its named sibling
`deep_evaluate_basic_no_yield` (Core_Expression_Lemmas.thy 53-75), which is
itself proved by well-founded induction over the yield relation using
`expression_wf_base_is_wf` (Core_Expression.thy 93). That is the depth-3 chain
recorded in `shape`.

Why each child is a good leaf. The three `atriple_rel_eval_*_adequacy` lemmas
are self-contained statements — "an exact triple over `eval_value` /
`eval_return` / `eval_abort` together with the matching continuation membership
transfers the post-condition to the output state" — whose proofs close on their
own by unfolding definitions only (`atriple_rel_def`, `eval_*_def`,
`urust_eval_predicate_defs`), a single `auto` call with no further project
lemma. `deep_evaluate_basic_no_yield'` is also self-contained — "Yield is not a
possible result of deep evaluation" — and closes from its named sibling by
`force`.

In my opinion the detail worth copying is that the fourth constructor of the
case split is closed by a *negation* lemma (`Yield ... ⟷ False`) rather than by
a vacuous or separately-proved case, so the case analysis stays total while the
impossible case is documented as impossible in its own statement.

## Why it is good

1. **check** — The parent `sstriple_adequacy` is closed by a single `auto` call
   (lines 63-66) that unfolds `sstriple_def`, splits on `continuation.splits`,
   and dispatches the four constructors to the four named direct lemmas
   `deep_evaluate_basic_no_yield'`, `atriple_rel_eval_value_adequacy`,
   `atriple_rel_eval_return_adequacy` and `atriple_rel_eval_abort_adequacy`;
   the theory is built by the project's CI. [Adequacy.thy L63-L66, ci.yml,
   Shallow_Separation_Logic/ROOT](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Adequacy.thy#L63-L66)
2. **check** — Each of the three per-constructor children closes on its own by
   unfolding definitions only (`atriple_rel_def eval_*_def
   urust_eval_predicate_defs`, lines 36/43/50), with no further project lemma;
   the fourth child closes from its named sibling `deep_evaluate_basic_no_yield`
   by `force` (line 79). [Adequacy.thy L36/L43/L50,
   Core_Expression_Lemmas.thy L77-L79](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Micro_Rust/Core_Expression_Lemmas.thy#L77-L79)
3. **measurement** — `direct_lemmas = 4`; `glue_lines = 14` (Adequacy.thy
   53-66); child proof lines 6/6/6/3; `depth = 3` via
   `sstriple_adequacy → deep_evaluate_basic_no_yield' →
   deep_evaluate_basic_no_yield → expression_wf_base_is_wf`.
   [Core_Expression_Lemmas.thy L53-L79,
   Core_Expression.thy L93](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Micro_Rust/Core_Expression_Lemmas.thy#L53-L79)
4. **author-statement** — The authors state the goal and the Yield side in the
   surrounding text: "from a Hoare triple/weakest precondition
   entailment/function contract on a program `e` we can derive that the
   evaluating `e` on appropriate machines does not go wrong" (lines 12-16), and
   "Evaluating with `deep_evaluates_nondet_basic` will never terminate in
   `Yield`" (the comment at line 62).
   [Adequacy.thy L9-L27, L62](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Adequacy.thy#L9-L27)
5. **known-use** — The same `split: continuation.splits` move recurs four more
   times in the file (contract_adequacy line 92, wp_adequacy_deterministic line
   111, sstriple_from_evaluation line 141, contract_from_evaluation line 163),
   and `sstriple_adequacy` is reused as the head of the two corollaries
   `wp_adequacy` (line 77) and `contract_adequacy` (line 92).
   [Adequacy.thy L68-L77, L81-L92, L99-L111, L130-L141,
   L153-L163](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Adequacy.thy#L68-L77)

## When to use it, and when not

Use it when the result type has finitely many constructors (here four: Success,
Return, Abort, Yield), when one per-constructor lemma already exists for each
"real" constructor, and when a separate lemma rules out the remaining
constructor (here Yield). Then `split: continuation.splits` is exhaustive by
construction of the datatype, and no disjunction lemma has to be stated.

Avoid it when the per-constructor lemmas have not yet been stated (the split
then leaves goals that `auto` must solve from raw definitions, which may not
close); when the constructor count is large; or when a constructor's case
genuinely holds rather than being impossible, in which case a real child lemma
is needed instead of a falsity lemma.

## Consequences

The case split produces one goal per constructor plus an exhaustiveness
obligation that `continuation.splits` (a datatype case rule) discharges itself,
exactly because `continuation` is a datatype. The Yield case is not "covered"
but ruled out by `deep_evaluate_basic_no_yield'`, so the decomposition relies on
that lemma's strength (`Yield ... ⟷ False`). If a new constructor were added to
the `continuation` datatype, the split would produce a new goal and `auto` would
fail to close it, exposing the exhaustiveness obligation.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/ci.yml build job runs 'isabelle build -v -b -d . -o browser_info -d $AFP_COMPONENT_BASE/Word_Lib AutoCorrode'; AutoCorrode session ROOT lists Shallow_Separation_Logic, whose ROOT lists Adequacy as its first theory; pinned commit 200f1acf2d264f2dedee33792b986ebe73c224a3 is identical to default branch main (git compare status identical) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 4 file(s) byte-identical at 200f1acf2d264f2dedee33792b986ebe73c224a3 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Adequacy.thy L63-66: 'using assms by (auto simp add: sstriple_def deep_evaluate_basic_no_yield' atriple_rel_eval_value_adequacy atriple_rel_eval_return_adequacy atriple_rel_eval_abort_adequacy split: continuation.splits)' - single auto, unfolds sstriple_def, split continuation.splits, cites the four named lemmas; CI builds Adequacy via AutoCorrode session | verifier |
| 2 | verified | Adequacy.thy L36 'using assms by (auto simp add: atriple_rel_def eval_value_def urust_eval_predicate_defs)', L43 (eval_return), L50 (eval_abort) all close by auto from definitions only; Core_Expression_Lemmas.thy L77-79 deep_evaluate_basic_no_yield' closed by 'using deep_evaluate_basic_no_yield by force' | verifier |
| 3 | verified | glue_lines 14 = Adequacy.thy 53-66; child lines 6 (31-36), 6 (38-43), 6 (45-50), 3 (Core_Expression_Lemmas.thy 77-79); direct_lemmas 4; depth chain: sstriple_adequacy L64 uses deep_evaluate_basic_no_yield' -> no_yield' L79 uses deep_evaluate_basic_no_yield -> no_yield L56 uses expression_wf_base_is_wf -> expression_wf_base_is_wf at Core_Expression.thy L93 | verifier |
| 4 | verified | Adequacy.thy L14 'from a Hoare triple/weakest precondition entailment/function contract on a program e' and L16 'we can derive that the evaluating e on appropriate machines does not go wrong'; L62 comment 'Evaluating with deep_evaluates_nondet_basic will never terminate in Yield' | verifier |
| 5 | verified | Adequacy.thy: 'split: continuation.splits' recurs at L92 (contract_adequacy), L111 (wp_adequacy_deterministic), L141 (sstriple_from_evaluation), L163 (contract_from_evaluation); sstriple_adequacy reused at L77 (wp_adequacy 'simp add: sstriple_adequacy') and L92 (contract_adequacy 'dest!: sstriple_adequacy') | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Copied code matches entry verbatim: parent sstriple_adequacy (Adequacy.thy L53-66) is one auto call (simp add: sstriple_def ... split: continuation.splits) citing exactly the four children deep_evaluate_basic_no_yield', atriple_rel_eval_value_adequacy, atriple_rel_eval_return_adequacy, atriple_rel_eval_abort_adequacy; the four child statements and closed_by lines match code L31-36/38-43/45-50 and Core_Expression_Lemmas.thy L77-79 (using deep_evaluate_basic_no_yield by force). The split closes: sstriple_def (Triple.thy L35-46) unfolds the premise into three exact-triple conjuncts, Success/Return/Abort dispatch to the per-constructor lemmas, and Yield is ruled out by no_yield' (Yield ... iff False). Shape numbers correct: direct_lemmas=4 (exactly the four named lemmas), glue_lines=14 (L53-66), child_lines=[6,6,6,3] (L31-36/38-43/45-50/77-79), depth=3 chain sstriple_adequacy to no_yield' (L79) to no_yield (L56 uses expression_wf_base_is_wf) to expression_wf_base_is_wf (Core_Expression.thy L93, confirmed lemma). | reviewer-correctness |
| generality | accept | Move generalised beyond the example: applicability.use_when states the rule as 'finitely many constructors + one per-constructor lemma for each real constructor + a separate falsity lemma for the impossible constructor', with the four continuation constructors as illustration only. avoid_when is honest and specific (three named failure modes: per-constructor lemmas not yet stated so auto must close raw-definition goals that may not close; large constructor count; a constructor that genuinely holds needs a real child lemma instead of a falsity lemma). consequences correctly names the exhaustiveness obligation as discharged by the datatype case rule continuation.splits and the fragility to a newly added constructor. README 'Why each child is a good leaf' explicitly answers the bounded-prover question: each child is self-contained and closes by a single auto/force unfolding definitions only (atriple_rel_def, eval_*_def, urust_eval_predicate_defs) with no further project lemma; the Yield child closes from its named sibling by force. Confirmed against the copied code (Adequacy.thy 31-66, Core_Expression_Lemmas.thy 53-79). | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are mutually consistent and traceable. check_provenance.py reports pass: 4 file(s) byte-identical at 200f1acf2d264f2dedee33792b986ebe73c224a3. entry.json source.commit and every permalink use that same pinned commit with paths matching the four copied files under code/ (Adequacy.thy, Triple.thy, Eval.thy, Core_Expression_Lemmas.thy). source.json and sources/autocorrode/SOURCE.md record the identical commit (pinned 2026-11-12T13:44:17Z) and repo https://github.com/awslabs/AutoCorrode. Licence is MIT throughout entry.json/README/SOURCE.md/source.json, and sources/autocorrode/upstream-LICENSE is the standard MIT License (Amazon copyright); no conflicting or copyleft/NC notice. SOURCE.md carries licence text pointer and attribution; README's Source and licence section agrees. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/awslabs/AutoCorrode at commit `200f1acf2d264f2dedee33792b986ebe73c224a3`, under `MIT`; see the [source note](../../sources/autocorrode/SOURCE.md) for the licence text and attribution.
