# Threading a frame as the key invariant through a raw for-loop

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | isabelle |
| Status | accepted |
| Source | [autocorrode](../../sources/autocorrode/SOURCE.md) at `200f1acf2d26` |
| Licence | `MIT` |

## Intent

A raw for-loop whose per-iteration triple carries an invariant `INV xs i` is
lifted to a whole-loop triple with arbitrary postconditions `psi`, `rho`,
`chi`. The lift works by strengthening the loop invariant to `INV xs i * ?pc`,
where the frame `?pc` is a conjunction of magic wands that, once the loop has
ended, turn the terminal invariant `INV xs (length xs)` and the per-iteration
`tau`/`theta` into the target postconditions.

## The decomposition

### parent `sstriple_raw_for_loop_framed'`: [`Shallow_Separation_Logic/Triple.thy` lines 601-638](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Triple.thy#L601-L638) ([local copy](code/Shallow_Separation_Logic/Triple.thy))

```isabelle
lemma sstriple_raw_for_loop_framed':
    notes aentails_intro [intro]
    fixes INV :: \<open>'t list \<Rightarrow> nat \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>i. (i < length xs) \<Longrightarrow> (\<Gamma> ; INV xs i \<turnstile> f (xs ! i) \<stileturn> (\<lambda>_. INV xs (i+1)) \<bowtie> \<tau> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; INV xs 0 \<star> (INV xs (length xs) \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r) \<turnstile> raw_for_loop xs f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
proof -
  let ?pc = \<open>(INV xs (length xs) \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r)\<close>
  {
    fix i
    assume \<open>i < length xs\<close>
    from this have \<open>\<Gamma> ; INV xs i \<turnstile> f (xs ! i) \<stileturn> (\<lambda>_. INV xs (i+1)) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
      using assms by auto
    moreover have \<open>\<Gamma> ; INV xs i \<star> ?pc \<turnstile> f (xs ! i) \<stileturn>
        (\<lambda>_. INV xs (i+1) \<star> ?pc) \<bowtie> (\<lambda>r. \<tau> r \<star> ?pc) \<bowtie> (\<lambda>a. \<theta> a \<star> ?pc)\<close>
      using calculation assms by (auto intro!: sstriple_frame_rule)
    moreover have \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
    proof -
      have \<open>\<And>r. \<tau> r \<star> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_refl aentails_trans aforall_entailsL asepconj_mono3 awand_counit)
      from this show \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_fold_def aentails_inter_weaken aentails_inter_weaken2 asepconj_mono awand_adjointI)
    qed
    moreover have \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
      by (meson aentails_refl_eq aentails_trans' aentails_inter_weaken aforall_entailsL asepconj_mono3
          awand_counit)
    ultimately have \<open>\<Gamma> ; INV xs i \<star> ?pc \<turnstile> f (xs ! i) \<stileturn> (\<lambda>_. INV xs (i+1) \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
      by (meson aentails_refl sstriple_consequence)
  }
  from this have \<open>\<Gamma> ; INV xs 0 \<star> ?pc
                            \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. INV xs (length xs) \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using assms sstriple_raw_for_loop'[where I=\<open>\<lambda>xs' i'. INV xs' i' \<star> ?pc\<close>] by blast
  moreover have \<open>INV xs (length xs) \<star> ?pc \<longlongrightarrow> \<psi> ()\<close>
    by (metis (no_types, lifting) aentails_refl local.asepconj_comm local.aentails_int local.awand_adjoint)
  moreover have \<open>\<Gamma> ; INV xs 0 \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using calculation local.sstriple_consequence by (fastforce simp add: aentails_refl)
  from this show ?thesis
    using aentails_refl local.asepconj_comm local.awand_mp local.sstriple_consequence by fastforce
qed
```

### child `sstriple_frame_rule`: [`Shallow_Separation_Logic/Triple.thy` lines 186-190](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Triple.thy#L186-L190) ([local copy](code/Shallow_Separation_Logic/Triple.thy))

```isabelle
theorem sstriple_frame_rule:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<star> \<xi> \<turnstile> e \<stileturn> (\<lambda>r. \<psi> r \<star> \<xi>) \<bowtie> (\<lambda>r. \<rho> r \<star> \<xi>)\<bowtie> (\<lambda>a. \<theta> a \<star> \<xi>)\<close>
  using assms by (intro sstriple_from_stripleI; clarsimp simp add: sstriple_striple
      striple_frame_rule is_local_frame)
```

### child `sstriple_raw_for_loop'`: [`Shallow_Separation_Logic/Triple.thy` lines 578-599](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Triple.thy#L578-L599) ([local copy](code/Shallow_Separation_Logic/Triple.thy))

```isabelle
lemma sstriple_raw_for_loop':
    fixes I :: \<open>'t list \<Rightarrow> nat \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>i. i < length xs \<Longrightarrow> (\<Gamma> ; I xs i \<turnstile> f (xs ! i) \<stileturn> (\<lambda>_. I xs (i+1)) \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; I xs 0 \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. I xs (length xs)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms 
proof (induction xs arbitrary: I)
  case Nil
  then show ?case
    by (simp add: raw_for_loop_nil sstriple_skipI)
next
  case (Cons x xs)
  then have \<open>\<Gamma> ; I (x # xs) 0 \<turnstile> f x \<stileturn> (\<lambda>_. I (x # xs) 1) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by fastforce
  moreover have \<open>\<And>i. i < length xs \<Longrightarrow> \<Gamma> ; I (x # xs) (Suc i) \<turnstile> f (xs ! i) \<stileturn> (\<lambda>_. I (x # xs) (Suc (Suc i))) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (metis Cons.prems Suc_eq_plus1 Suc_mono length_Cons nth_Cons_Suc)
  then have \<open>\<Gamma> ; I (x # xs) 1 \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. I (x # xs) (Suc (length xs))) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using  Cons.IH[where I=\<open>\<lambda>_ i. I (x # xs) (i+1)\<close>] by force
  ultimately have \<open>\<Gamma> ; I (x # xs) 0 \<turnstile> (bind (f x) (\<lambda>_. raw_for_loop xs f)) \<stileturn> (\<lambda>_. I (x # xs) (Suc (length xs))) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (auto intro: sstriple_bindI[where \<psi>=\<open>\<lambda> _. I (x # xs) 1\<close>])
  then show ?case
    by (auto simp add: micro_rust_simps sequence_def)
qed
```

### child `sstriple_consequence`: [`Shallow_Separation_Logic/Triple.thy` lines 164-172](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Triple.thy#L164-L172) ([local copy](code/Shallow_Separation_Logic/Triple.thy))

```isabelle
lemma sstriple_consequence:
  assumes \<open>\<Gamma> ; \<phi>' \<turnstile> e \<stileturn> \<psi>' \<bowtie> \<rho>' \<bowtie> \<theta>'\<close>
      and \<open>\<phi> \<longlongrightarrow> \<phi>'\<close>
      and \<open>\<And>r. \<psi>' r \<longlongrightarrow> \<psi> r\<close>
      and \<open>\<And>r. \<rho>' r \<longlongrightarrow> \<rho> r\<close>
      and \<open>\<And>a. \<theta>' a \<longlongrightarrow> \<theta> a\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
using assms is_local_weaken by (intro sstriple_from_stripleI; clarsimp simp add: sstriple_striple
  striple_consequence)
```

How the parts fit. The parent `sstriple_raw_for_loop_framed'` is assembled
from three named lemmas in the same file. The one idea that carries the proof
is the strengthened invariant `INV xs i ⋆ ?pc`: the loop rule needs an
invariant indexed by the list position, and the glue supplies `I = λxs' i'.
INV xs' i' ⋆ ?pc`, so every iteration carries the frame `?pc` alongside the
user's `INV`.

The lemma graph (who uses whom), read top-down:

```
sstriple_raw_for_loop_framed'   (parent, 601-638)
  ├─ sstriple_frame_rule         (186-190)  — frame each iteration step
  ├─ sstriple_consequence        (164-172)  — transport the postconditions
  └─ sstriple_raw_for_loop'      (578-599)  — the unframed loop rule
        ├─ sstriple_skipI        (242-245)  — base case (Nil)
        └─ sstriple_bindI        (225-230)  — step case (Cons)
  sstriple_frame_rule / sstriple_consequence
        └─ sstriple_from_stripleI (112-118)
              └─ sstriple_striple (55-94)
                    └─ sstripleI  (48-53)
```

The glue in the parent's `proof` does three things. First it frames each
iteration: from the assumption `INV xs i ⊢ f (xs ! i) {λ_. INV xs (i+1)} {τ}
{θ}` it derives, with `sstriple_frame_rule`, the framed step
`INV xs i ⋆ ?pc ⊢ f (xs ! i) {λ_. INV xs (i+1) ⋆ ?pc} {λr. τ r ⋆ ?pc} {λa. θ
a ⋆ ?pc}`. Then it transports, with `sstriple_consequence`, the framed
return/abort postconditions down to the target `ρ` and `χ` (proving
`τ r ⋆ ?pc ⟶ ρ r` and `θ a ⋆ ?pc ⟶ χ a` by `aentails` reasoning). Finally it
calls `sstriple_raw_for_loop'` at `I = λxs' i'. INV xs' i' ⋆ ?pc` to close the
loop, and once more `sstriple_consequence` to turn `INV xs (length xs) ⋆ ?pc`
into `ψ ()`.

Why each child is a good leaf: `sstriple_frame_rule` and
`sstriple_consequence` are self-contained structural rules whose proofs close
by a single `intro sstriple_from_stripleI` plus simplification
(`sstriple_striple`, `striple_frame_rule`/`striple_consequence`,
`is_local_frame`/`is_local_weaken`); `sstriple_raw_for_loop'` is a
self-contained loop rule proved by induction on `xs`, whose base case closes
with `sstriple_skipI` and whose step closes with `sstriple_bindI` (both named
siblings in the same file). None of the three depends on the parent or on an
unproved hypothesis beyond its own `assumes`.

## Why it is good

1. `sstriple_frame_rule` occurs in the parent's site (line 615): the glue
   frames each iteration step with `?pc`. *(check —
   `cites(parent, sstriple_frame_rule)`)*
2. `sstriple_raw_for_loop'` occurs in the parent's site (line 631): the glue
   instantiates the unframed loop rule at `I = λxs' i'. INV xs' i' ⋆ ?pc`.
   *(check — `cites(parent, sstriple_raw_for_loop')`)*
3. The parent site is 38 lines long (lines 601-638); this is the `glue_lines`
   of the recorded shape. *(check — `lines(parent, 38)`)*
4. The main proof uses three named lemmas directly — `sstriple_frame_rule`
   (line 615), `sstriple_raw_for_loop'` (line 631), `sstriple_consequence`
   (lines 627, 635, 637) — and the longest chain of project lemmas below it is
   five: `sstriple_raw_for_loop'` → `sstriple_skipI` →
   `sstriple_from_stripleI` → `sstriple_striple` → `sstripleI`.
   *(measurement — counted from the copied file at the pinned commit)*
5. The same framing pattern — strengthen the loop invariant to `INV ⋆ ?pc`,
   frame each step, transport with `sstriple_consequence` — is reused in the
   same file by `sstriple_raw_for_loop_framed` (lines 539-576),
   `sstriple_bounded_while_framed` (lines 693-749) and
   `sstriple_gather_framed` (lines 814-859). *(known-use)*

In my opinion the detail worth copying is the `?pc` frame itself: a
conjunction of magic wands is introduced once (`let ?pc = ...`) and threaded
through the whole induction, so the target postconditions appear nowhere in
the loop invariant except through the frame. The authors state the same idea
in a comment beside the while-loop analogue, "Framed version: carries a frame
through all iterations." (line 692). The move is an instance of survey F §10
rule 6's "strengthen the hypothesis": the strengthened hypothesis here is a
strengthened loop invariant rather than a varied `arbitrary:` set.

## When to use it, and when not

Use it when a loop has a clean per-iteration invariant `INV` but the client
wants different postconditions, and the link between the iteration's
postconditions and the client's can be written as magic wands (`Zsurj`) held
in a separating-conjunct frame. Avoid it when the per-iteration invariant
itself needs strengthening (then strengthen `INV` first, before framing); when
the target postcondition cannot be phrased as a wand that is sound under the
separating conjunction; or when the loop is a bounded while with a separate
condition step, for which the file provides the dedicated
`sstriple_bounded_while_framed`.

## Consequences

The move creates one side condition per component: `τ r ⋆ ?pc ⟶ ρ r` and
`θ a ⋆ ?pc ⟶ χ a` for the return/abort frames, plus
`INV xs (length xs) ⋆ ?pc ⟶ ψ ()` for the terminal invariant, each discharged
by `aentails` reasoning (`meson`/`metis`) over the wand structure. Failure
mode: if the frame `?pc` cannot be separated cleanly from the invariant, the
final `sstriple_consequence` transports fail. The whole proof depends on
`sstriple_frame_rule` distributing `?pc` through all three components of the
per-iteration triple.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/ci.yml build job runs 'isabelle build -v -b -d . -o browser_info -d $AFP_COMPONENT_BASE/Word_Lib AutoCorrode' on push to main (default branch); root ROOT defines 'session AutoCorrode' including Shallow_Separation_Logic, whose ROOT lists 'Triple' as a theory; commit 200f1acf2d264f2dedee33792b986ebe73c224a3 | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: sstriple_frame_rule@Shallow_Separation_Logic/Triple.thy:615, sstriple_raw_for_loop'@Shallow_Separation_Logic/Triple.thy:631, sstriple_consequence@Shallow_Separation_Logic/Triple.thy:627; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 200f1acf2d264f2dedee33792b986ebe73c224a3 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, sstriple_frame_rule) -> cites: sstriple_frame_rule occurs at Shallow_Separation_Logic/Triple.thy:615 | check_claims.py |
| 2 | verified | cites(parent, sstriple_raw_for_loop') -> cites: sstriple_raw_for_loop' occurs at Shallow_Separation_Logic/Triple.thy:631 | check_claims.py |
| 3 | verified | lines(parent, 38) -> lines: site parent has 38 lines | check_claims.py |
| 4 | verified | Read copied Triple.thy at pinned commit: parent site 601-638 uses sstriple_frame_rule at 615, sstriple_raw_for_loop' at 631, sstriple_consequence at 627/635/637. Chain links hold: sstriple_raw_for_loop' (578) base case uses sstriple_skipI; sstriple_skipI (242-244) 'auto intro!: sstriple_from_stripleI'; sstriple_from_stripleI (112-118) 'using assms sstriple_striple'; sstriple_striple (55-94) 'intro sstripleI'. Declarations at 578/242/112/55/48 match the claim. | verifier |
| 5 | verified | Read copied Triple.thy: sstriple_raw_for_loop_framed declared at 539 (qed 576), sstriple_bounded_while_framed at 693 (qed 749), sstriple_gather_framed at 814 (qed 859); each carries 'let ?pc = ...' magic-wand frame and frames steps via sstriple_frame_rule then transports via sstriple_consequence (bounded_while_framed lines 726-745 confirmed). | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition matches the code: parent sstriple_raw_for_loop_framed' (601-638) is assembled from exactly the three recorded children sstriple_frame_rule (186-190), sstriple_raw_for_loop' (578-599), sstriple_consequence (164-172), all statements verbatim. Each child's closed_by matches its code (frame_rule: intro sstriple_from_stripleI+clarsimp; raw_for_loop': induction xs arbitrary: I with simp add: raw_for_loop_nil sstriple_skipI / auto intro: sstriple_bindI; consequence: is_local_weaken+intro sstriple_from_stripleI). Proof closes (qed at 638, no sorry). The three children are exactly the named project lemmas the parent cites (615, 631, 627/635/637); aentails/awand lemmas are from imported Assertion_Language, not project lemmas. Shape numbers verified: direct_lemmas=3, depth=5 (raw_for_loop' 578 -> skipI 242 -> from_stripleI 112 -> striple 55 -> sstripleI 48, all confirmed by grep), glue_lines=38 (601-638), child_lines=[5,22,9] matching frame_rule/raw_for_loop'/consequence in order. Provenance passes. | reviewer-correctness |
| generality | accept | Move is stated to generalise: applicability.goal_shape/use_when/avoid_when abstract to 'a loop with a clean per-iteration invariant INV but different target postconditions linked by magic wands held in a separating-conjunct frame', not to this one lemma. Generality beyond the example is demonstrated by known-use claim 5, which I confirmed in code: sstriple_raw_for_loop_framed (539-576), sstriple_bounded_while_framed (693-749) and sstriple_gather_framed (814-859) all re-run the same 'let ?pc = wand-frame; frame each step; transport via sstriple_consequence' pattern, and the author comment 'Framed version: carries a frame through all iterations.' is at line 692 as cited. When-not-to-use is specific and honest: strengthen INV first; the target postcondition must be a wand sound under separating conjunction; use sstriple_bounded_while_framed for a bounded while with a separate condition step (consistent with the known-use, which reuses the pattern but not this lemma). Consequences name the three concrete side conditions (tau r * ?pc --> rho r, theta a * ?pc --> chi a, INV xs (length xs) * ?pc --> psi ()) and a real failure mode (frame not separable => final consequence transports fail). It says explicitly what makes the children good leaves for a bounded prover: each is self-contained, closes by a single intro + simplification (frame/consequence) or by induction over xs with base sstriple_skipI and step sstriple_bindI, and none depends on the parent or on an unproved hypothesis beyond its own assumes. | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes (1 file byte-identical at 200f1acf2d264f2dedee33792b986ebe73c224a3); local code sha256 94e6b0d1..9ff8 and 65211 bytes match entry.json; commit 200f1acf..c224a3 is consistent across entry.json, source.json, SOURCE.md and every permalink; licence MIT is consistent across all three and backed by upstream-LICENSE (Amazon MIT); all cited line ranges (164-172, 186-190, 578-599, 601-638) resolve to the named declarations. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/awslabs/AutoCorrode at commit `200f1acf2d264f2dedee33792b986ebe73c224a3`, under `MIT`; see the [source note](../../sources/autocorrode/SOURCE.md) for the licence text and attribution.
