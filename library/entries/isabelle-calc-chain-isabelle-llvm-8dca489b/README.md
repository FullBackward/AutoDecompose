# Transitivity chain conflates the KMP refinement ladder into kmp2_correct

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | isabelle |
| Status | draft |
| Source | [isabelle-llvm](../../sources/isabelle-llvm/SOURCE.md) at `6be37a9c3cae` |
| Licence | `BSD-3-Clause` |
| Licence recorded | 2026-11-14T15:15:47Z |

## Intent

The final KMP correctness theorem is assembled by transitivity instead of one
monolithic proof. The author proves each refinement step of the ladder
(`kmp2 → kmp1 → kmp → kmp_SPEC`) once as its own named lemma, then conflates
them with a four-line `also`/`finally` chain, so `kmp2_correct` holds without
restating any intermediate proof.

## The decomposition

### parent `kmp2_correct`: [`thys/examples/KMP.thy` lines 873-881](https://github.com/lammich/isabelle_llvm/blob/6be37a9c3cae74a1134dbef2979e312abb5f7f42/thys/examples/KMP.thy#L873-L881) ([local copy](code/thys/examples/KMP.thy))

```isabelle
lemma kmp2_correct: "s \<noteq> []
  \<Longrightarrow> kmp2 s t \<le> kmp_SPEC s t"
proof -
  assume "s \<noteq> []"
  have "kmp2 s t \<le> kmp1 s t" by (fact kmp2_refine)
  also have "... \<le> kmp s t" by (fact kmp1_refine)
  also have "... \<le> kmp_SPEC s t" by (fact kmp_correct[OF \<open>s \<noteq> []\<close>])
  finally show ?thesis.
qed
```

### child `kmp2_refine`: [`thys/examples/KMP.thy` lines 865-871](https://github.com/lammich/isabelle_llvm/blob/6be37a9c3cae74a1134dbef2979e312abb5f7f42/thys/examples/KMP.thy#L865-L871) ([local copy](code/thys/examples/KMP.thy))

```isabelle
lemma kmp2_refine: "kmp2 s t \<le> kmp1 s t"
  apply (rule refine_IdD)
  unfolding kmp2_def kmp1_def
  apply refine_rcg
                  apply refine_dref_type
                  apply (auto simp: in_br_conv I_outer_def I_in_na_def split: option.splits)
  done
```

### child `kmp1_refine`: [`thys/examples/KMP.thy` lines 524-533](https://github.com/lammich/isabelle_llvm/blob/6be37a9c3cae74a1134dbef2979e312abb5f7f42/thys/examples/KMP.thy#L524-L533) ([local copy](code/thys/examples/KMP.thy))

```isabelle
lemma kmp1_refine: "kmp1 s t \<le> kmp s t"
  apply (rule refine_IdD)
  unfolding kmp1_def kmp_def Let_def compute_\<ff>s_SPEC_def nres_monad_laws
  apply (intro ASSERT_refine_right ASSERT_refine_left)
   apply simp
  apply (rule Refine_Basic.intro_spec_refine)
  apply refine_rcg
                apply refine_dref_type
                apply auto
  done
```

### child `kmp_correct`: [`thys/examples/KMP.thy` lines 476-490](https://github.com/lammich/isabelle_llvm/blob/6be37a9c3cae74a1134dbef2979e312abb5f7f42/thys/examples/KMP.thy#L476-L490) ([local copy](code/thys/examples/KMP.thy))

```isabelle
lemma kmp_correct: "s \<noteq> []
  \<Longrightarrow> kmp s t \<le> kmp_SPEC s t"
  unfolding kmp_def kmp_SPEC_def I_outer_def I_in_na_def
  apply (refine_vcg
    WHILEIT_rule[where R="measure (\<lambda>(i,_,pos). length t - i + (if pos = None then 1 else 0))"]
    WHILEIT_rule[where R="measure (\<lambda>(j,_::nat option). length s - j)"]
    )
  apply (all \<open>clarsimp;(auto; fail)?\<close>)
  subgoal by (metis add_Suc_right all_positions_sublist less_antisym)
  subgoal using less_antisym by blast
  subgoal for i jout j using j_le_\<ff>_le[of j s] by simp
  subgoal for i jout j using shift_safe[of i s t j] by fastforce
  subgoal for i jout j using reuse_matches[of j s t i] \<ff>_le by simp
  subgoal by (auto split: option.splits) (metis sublist_lengths add_less_cancel_right leI le_less_trans)
  done
```

How the parts fit. The parent `kmp2_correct` is the conflation lemma: its
whole proof is a chain of three refinement inequalities joined by `also` and
closed with `finally`. The lemma graph is a single spine, one child per link:

```
kmp2_correct (873-881)  ← the main theorem, proved by transitivity alone
├── kmp2_refine (865) : kmp2 s t ≤ kmp1 s t          (link 1)
├── kmp1_refine (524) : kmp1 s t ≤ kmp s t           (link 2)
└── kmp_correct (476) : s ≠ [] ⟹ kmp s t ≤ kmp_SPEC s t   (link 3)
```

Each link is one `have`/`also have` line that closes `by (fact …)`, citing the
named lemma; `finally` discharges the transitivity. The precondition `s ≠ []`
enters only at the last link, passed as `kmp_correct[OF ‹s ≠ []›]`.

Why each child is a good leaf (a self-contained statement whose proof closes on
its own):

- `kmp2_refine` — statement `kmp2 s t ≤ kmp1 s t`. Its proof is `apply (rule
  refine_IdD)` then `refine_rcg`/`refine_dref_type` then `auto`, closing on its
  own; the author notes it is trivial because `compute_butlast_\<ff>s_refine`
  carries the `[refine]` attribute (line 864).
- `kmp1_refine` — statement `kmp1 s t ≤ kmp s t`. Same shape, plus
  `intro_spec_refine` and the ASSERT intro rules; it closes on its own with
  `refine_rcg`/`refine_dref_type`/`auto`.
- `kmp_correct` — statement `s ≠ [] ⟹ kmp s t ≤ kmp_SPEC s t`. Closes with
  `refine_vcg` (two `WHILEIT` termination measures) and six `subgoal`s, each
  discharged by `metis`/`blast`/`simp`/`fastforce`/`auto` that pull in further
  project lemmas: `j_le_\<ff>_le`, `shift_safe`, `reuse_matches`,
  `all_positions_sublist`, `\<ff>_le`.

The longest project-lemma chain below the main theorem I checked is length 3:
`kmp2_correct` → `kmp_correct` (glue link) → `j_le_\<ff>_le` (line 486) →
`intrinsic_border_less` (line 266, cited by `j_le_\<ff>_le`'s `metis` at line
363); each link is a declaration in the same file.

## Why it is good

1. The parent site `kmp2_correct` is 9 lines long (lines 873-881), the whole
   theorem and its transitivity proof in one sitting. *(check)*
2. The parent site cites `kmp1_refine`, the middle link of the chain, at line
   878. *(check)*
3. The lemma `kmp_correct` is declared at lines 476-490 of
   `thys/examples/KMP.thy`. *(check)*
4. No `sorry` occurs anywhere in `thys/examples/KMP.thy` (1046 lines), so every
   link of the chain is a real proof, not a hole. *(check)*
5. The authors explain why `kmp2_refine` is so short: "Using
   compute_butlast_\<ff>s_refine (it has attribute refine), the proof is
   trivial" (line 864). *(author-statement)*

In my opinion the detail worth copying is that the glue is nothing but three
`by (fact …)` links: the conflation theorem has no content of its own beyond
transitivity, which is exactly the shape a bounded prover should be asked to
produce — a skeleton whose only obligations are the named lemmas it cites.

## When to use it, and when not

Use it when the goal is a transitive chain of refinement (or equality)
inequalities `A ≤ C ≤ … ≤ B` and every single step is already proved as its
own named lemma in the same theory; Isar's `also`/`finally` then does all the
work and the conflation theorem is a one-liner per link. This is the natural
closing move of a refinement framework (here the Isabelle Refinement
Framework's `nres` `≤`), where each `kmpN_refine` step was proved once and
reused.

Avoid it when any step is not yet a named lemma (the `by (fact …)` link cannot
close and you must inline or prove the gap); when the steps are not all the
same relation (Isar's `also` does not compose `≥` by default — survey F §10
rule 9); or when a step carries a hypothesis that must be discharged at the use
site (here `kmp_correct` needs `s ≠ []`, so the chain passes it via
`kmp_correct[OF ‹s ≠ []›]`). It also does not apply to a single-step goal: the
value is in conflating *several* already-proved steps.

## Consequences

The move transfers the head step's precondition (`s ≠ []`) into the final
theorem's assumption, and each `also` link must be a named lemma or fact,
applied as `by (fact …)`. The chain is only as strong as its weakest link: if
an intermediate refinement lemma is later weakened, the conflation breaks and
must be re-checked. Obligations: every link must be an inequality in the same
relation so transitivity applies, and the first step's assumptions must be
supplied at the use site. There is no new proof content in the glue itself, so
a reviewer's whole job is to check that each cited name exists and states the
claimed inequality.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: kmp2_refine@thys/examples/KMP.thy:877, kmp1_refine@thys/examples/KMP.thy:878, kmp_correct@thys/examples/KMP.thy:879; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(kmp2_correct, 9) -> lines: site kmp2_correct has 9 lines | check_claims.py |
| 2 | verified | cites(kmp2_correct, kmp1_refine) -> cites: kmp1_refine occurs at thys/examples/KMP.thy:878 | check_claims.py |
| 3 | verified | declared(kmp_correct, thys/examples/KMP.thy, 476-490) -> declared: kmp_correct is declared at thys/examples/KMP.thy:476 | check_claims.py |
| 4 | verified | no_sorry(thys/examples/KMP.thy, 1-1046) -> no_sorry: none of sorry in thys/examples/KMP.thy:1-1046 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/lammich/isabelle_llvm at commit `6be37a9c3cae74a1134dbef2979e312abb5f7f42`, under `BSD-3-Clause`; see the [source note](../../sources/isabelle-llvm/SOURCE.md) for the licence text and attribution.
