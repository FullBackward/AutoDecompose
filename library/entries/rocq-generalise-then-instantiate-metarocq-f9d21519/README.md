# Confluence of PCUIC reduction, transported to the well-scoped presentation

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | rocq |
| Status | accepted |
| Source | [metarocq](../../sources/metarocq/SOURCE.md) at `51b14e4bb5f4` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T12:11:19Z |

## Intent

The parent `red_confluence` (confluence of the raw reduction `red` on PCUIC
terms) is proved with no reduction reasoning of its own: the glue transports
its two `red` hypotheses into the well-scoped presentation `ws_red`, applies
the already-proven confluence of `ws_red`, and transports the two `ws_red`
conclusions back to `red`. All the work lives in the three named children and
the diamond lemma they rest on; the glue is pure assembly.

## The decomposition

### parent `red_confluence`: [`pcuic/theories/PCUICConfluence.v` lines 3936-3944](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/pcuic/theories/PCUICConfluence.v#L3936-L3944) ([local copy](code/pcuic/theories/PCUICConfluence.v))

```coq
  Lemma red_confluence {Γ : closed_context} {t : open_term Γ} {u v} :
    red Σ Γ t u -> red Σ Γ t v ->
    ∑ v', red Σ Γ u v' * red Σ Γ v v'.
  Proof using wfΣ.
    move/red_ws_red_left => [onu redu].
    move/red_ws_red_left => [onv redv].
    destruct (ws_red_confluence redu redv) as [nf [redl redr]].
    now exists nf; split; [eapply ws_red_red in redl | eapply ws_red_red in redr].
  Qed.
```

### child `red_ws_red_left`: [`pcuic/theories/PCUICConfluence.v` lines 3927-3934](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/pcuic/theories/PCUICConfluence.v#L3927-L3934) ([local copy](code/pcuic/theories/PCUICConfluence.v))

```coq
  Lemma red_ws_red_left {Γ : closed_context} {x : ws_term (shiftnP #|Γ| xpred0)} {y} :
    red Σ Γ x y -> ∑ prf, ws_red Σ xpred0 Γ x (exist y prf).
  Proof using wfΣ.
    move=> r.
    have ony : on_free_vars (shiftnP #|Γ| xpred0) y by eauto with fvs.
    exists ony.
    now eapply red_ws_red.
  Qed.
```

### child `ws_red_confluence`: [`pcuic/theories/PCUICConfluence.v` lines 3916-3923](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/pcuic/theories/PCUICConfluence.v#L3916-L3923) ([local copy](code/pcuic/theories/PCUICConfluence.v))

```coq
  Lemma ws_red_confluence {Γ t u v} :
    ws_red Σ xpred0 Γ t u -> ws_red Σ xpred0 Γ t v ->
    ∑ v', ws_red Σ xpred0 Γ u v' * ws_red Σ xpred0 Γ v v'.
  Proof using wfΣ.
    move=> H H'.
    destruct (red1_confluent wfΣ _ _ _ _ H H') as [nf [redl redr]].
    exists nf; intuition auto.
  Qed.
```

### child `ws_red_red`: [`pcuic/theories/PCUICConfluence.v` lines 3404-3416](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/pcuic/theories/PCUICConfluence.v#L3404-L3416) ([local copy](code/pcuic/theories/PCUICConfluence.v))

```coq
  Lemma ws_red_red Γ t u :
    ws_red Σ xpred0 Γ t u ->
    red Σ Γ t u.
  Proof using Type.
    rewrite /ws_red /red.
    destruct t as [t ht], u as [u hu]; cbn.
    intros H; depind H.
    red in r. now constructor.
    constructor 2.
    destruct y as [y hy].
    econstructor 3.
    eapply IHclos_refl_trans1. f_equal. eauto.
  Qed.
```

How the parts fit. The parent `red_confluence` never reasons about reduction:
it only moves between two presentations of the same reduction. `red Σ Γ t u`
is the raw relation on open terms; `ws_red Σ P Γ t u` is the same `clos_refl_trans
(red1 Σ Γ)` restricted to `ws_term` (a term paired with a proof that its free
variables obey `P` — here `on_free_vars`). The lemma graph:

```
red_confluence (parent, 3936-3944) — the glue, 4 tactic lines
  ├─ red_ws_red_left (3927-3934)  red ⇒ ws_red, applied twice (to u, then v)
  │    └─ red_ws_red (3091)        re-closes the reduct under on_free_vars
  ├─ ws_red_confluence (3916-3923) the diamond, in the well-scoped presentation
  │    └─ red1_confluent (3706)    confluent (ws_red1)
  │         └─ pred_rel_confluent (3266) → pred1_rel_alpha_confluent (3261)
  │              → diamond_pred1_rel_alpha (3242) → ws_pred1_diamond (2680)
  │              → pred1_diamond (imported from PCUICParallelReductionConfluence)
  └─ ws_red_red (3404-3416)        ws_red ⇒ red, applied twice (to redl, then redr)
```

The glue takes `red Σ Γ t u` and `red Σ Γ t v`, uses `red_ws_red_left` to get
`ws_red Σ xpred0 Γ t (exist u onu)` and the same for `v` (this is where the
reducts are shown well-scoped), applies `ws_red_confluence` to get a common
well-scoped reduct `nf`, and applies `ws_red_red` to turn the two `ws_red`
conclusions back into `red Σ Γ u nf` and `red Σ Γ v nf`.

Each child is a good leaf because it is self-contained and closes on its own
from earlier named lemmas, not from the other children:

- `red_ws_red_left` closes by `eapply red_ws_red` after `have ony : on_free_vars
  … y by eauto with fvs` — the invariant is preserved by reduction, so the
  transport-in is one automation call plus one library lemma.
- `ws_red_confluence` closes by `red1_confluent` (one-step confluence of
  `ws_red1`) and `exists nf; intuition auto`; the real diamond is pushed one
  level down.
- `ws_red_red` closes by dependent induction (`depind H`) on the
  `clos_refl_trans` proof, closing its three constructors using only its own
  induction hypothesis `IHclos_refl_trans1` — it needs no other lemma (it even
  uses `Proof using Type`, no `wfΣ`).

## Why it is good

1. (`check`, `declared`) `red_confluence` is declared in
   `pcuic/theories/PCUICConfluence.v` within lines 3936-3944.
2. (`check`, `no_sorry`) No `admit`, `Admitted`, `Axiom` or `axiom` token
   occurs in `pcuic/theories/PCUICConfluence.v` lines 3404-3944, the span that
   contains the parent and its three direct children.
3. (`check`, `cites`) `red1_confluent` occurs in the site `ws_red_confluence`,
   showing the diamond is applied one level below the transport.
4. (`measurement`) The theorem-scale shape: 3 direct lemmas, a longest
   project-lemma chain of depth 6 below `red_confluence`, a 9-line parent site
   and child sites of 8, 8 and 13 lines (see the depth chain in "How the parts
   fit").
5. (`author-statement`) The file header says the plan in the authors' own
   words: "we use confluence of reduction on well-scoped terms
   [`ws_red_confluence`] … We can drop the invariants on free variables at each
   step as reduction preserves free-variables, so we also have
   [`red_confluence`]: as long as the starting contexts and terms are
   well-scoped confluence holds." (lines 11-18)

In my opinion the move worth copying is the *transport, not the diamond*: the
glue is four tactic lines that only convert between `red` and `ws_red` and
apply one lemma, so the main theorem is "nearly trivial given the children" —
the shape AutoDecompose is meant to produce, and what survey F §10 rule 14
targets ("one key theorem or a few tactics").

## When to use it, and when not

Use it when a property (confluence, or any closure/diamond property) is easier
to prove in a presentation that carries an invariant — here well-scopedness —
and the invariant is preserved by the relation, so that two cheap transport
lemmas (`red ⇒ ws_red` and `ws_red ⇒ red`) exist and the heavy work can be
done once, where the invariant is available. This is the usual PCUIC shape:
the metatheory is developed over well-scoped terms, and a raw relation is
handled by transporting into that presentation.

Avoid it when the invariant does not hold on the raw relation's range or is
not preserved by reduction (then `red_ws_red_left` cannot even be stated, and
the parent is confined to well-scoped starting terms); or when the transport
lemmas are themselves as hard as the target, in which case the round-trip
saves nothing.

## Consequences

The move leans entirely on the invariant being preserved by reduction:
`red_ws_red_left` must recover `on_free_vars … y` for the reduct `y`, which
holds only because reduction preserves free variables (discharged by `eauto
with fvs`). The parent is therefore restricted to a well-scoped starting term
(`t : open_term Γ`); a raw term outside that presentation cannot be
transported. The glue is only as good as the well-scoped confluence
`ws_red_confluence`, which itself rests on the deep parallel-reduction diamond
`pred1_diamond` (imported from `PCUICParallelReductionConfluence`); any
strengthening of the reduction relation has to be re-proven there, not in this
glue. A known failure mode of this pattern is that the transport back
(`ws_red_red`) must survive the `depind` on `clos_refl_trans`; if the relation
is changed so that reduction no longer preserves the invariant, the whole
round-trip breaks at `red_ws_red_left` first.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (MetaRocq CI, triggers on push/PR) runs ./configure.sh --enable-local|opam then make ci-local|ci-opam, building pcuic/theories/PCUICConfluence.v (listed pcuic/_RocqProject.in:64). Pinned commit 51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56 is HEAD of default branch 9.1 (branches-where-head returns 9.1; compare 9.1...51b14e4 status identical) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: red_ws_red_left@pcuic/theories/PCUICConfluence.v:3940, ws_red_confluence@pcuic/theories/PCUICConfluence.v:3942, ws_red_red@pcuic/theories/PCUICConfluence.v:3943; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(red_confluence, pcuic/theories/PCUICConfluence.v, 3936-3944) -> declared: red_confluence is declared at pcuic/theories/PCUICConfluence.v:3936 | check_claims.py |
| 2 | verified | no_sorry(pcuic/theories/PCUICConfluence.v, 3404-3944) -> no_sorry: none of admit, Admitted, Axiom, axiom in pcuic/theories/PCUICConfluence.v:3404-3944 | check_claims.py |
| 3 | verified | cites(ws_red_confluence, red1_confluent) -> cites: red1_confluent occurs at pcuic/theories/PCUICConfluence.v:3921 | check_claims.py |
| 4 | verified | 3 direct lemmas: red_ws_red_left (3927-3934), ws_red_confluence (3916-3923), ws_red_red (3404-3416). Site lengths: parent red_confluence 3936-3944 = 9 lines; children 3927-3934=8, 3916-3923=8, 3404-3416=13. Depth-6 chain verified link by link: red_confluence@3942 cites ws_red_confluence; ws_red_confluence@3921 cites red1_confluent; red1_confluent@3709 cites pred_rel_confluent; pred_rel_confluent@3269 cites pred1_rel_alpha_confluent; pred1_rel_alpha_confluent@3263 cites diamond_pred1_rel_alpha; diamond_pred1_rel_alpha@3246 cites ws_pred1_diamond (declared 2680, a leaf citing only imported pred1_diamond). | verifier |
| 5 | verified | File header lines 11-18: 'we use confluence of reduction on well-scoped terms [ws_red_confluence]... We can drop the invariants on free variables at each step as reduction preserves free-variables, so we also have [red_confluence]: as long as the starting contexts and terms are well-scoped confluence holds.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition matches the code: parent red_confluence (3936-3944) is 4 tactic lines that only move/red_ws_red_left (twice), destruct ws_red_confluence, and eapply ws_red_red (twice) — the glue uses exactly the three named children, nothing else. The three children are verbatim (statements re-copied by statements.py) and their closed_by notes match the code: red_ws_red_left closes via have ony...eauto with fvs then now eapply red_ws_red; ws_red_confluence via destruct (red1_confluent...) then exists nf; intuition auto; ws_red_red via Proof using Type, intros H; depind H over the three clos_refl_trans constructors using IHclos_refl_trans1. All parent and child sites end in Qed and no_sorry 3404-3944 is verified, so it closes. Shape numbers are right: direct_lemmas=3 (red_ws_red_left, ws_red_confluence, ws_red_red), glue_lines=9 (3936-3944), child_lines=[8,8,13] (3927-3934, 3916-3923, 3404-3416). Depth=6 verified by following citations: red_confluence->ws_red_confluence(3942)->red1_confluent(3921/3706)->pred_rel_confluent(3709/3266)->pred1_rel_alpha_confluent(3269/3261)->diamond_pred1_rel_alpha(3263/3242)->ws_pred1_diamond(3246/2680), six project lemmas below the parent. Minor note (not an objection): claim 4's chain cites use-site lines (3921,3709,3269,3263,3246) while the README graph lists declaration lines (3706,3266,3261,3242,2680); both are internally consistent and depth 6 is correct. | reviewer-correctness |
| generality | accept | Generality lens passes. The move is stated portably: applicability/use_when generalise confluence to 'any closure/diamond property' and well-scopedness to 'an invariant preserved by the relation', with two cheap transport lemmas doing the lifting; the also_known_as names give the general pattern. When-not-to-use is honest and specific: invariant absent from the raw relation's range or not preserved (then red_ws_red_left is unstatable), or transport as hard as the target (no round-trip saving). Consequences name exact loci (eauto with fvs; t : open_term Gamma restriction; dependency on pred1_diamond re-provable only upstream; depind surviving clos_refl_trans as failure mode). Good-leaves-for-a-bounded-prover is explicit: each child is self-contained and closes from earlier named lemmas, not sibling children, with a per-child closure mechanism and the Survey F rule-14 link. | reviewer-generality |
| provenance-licence | accept | Commit pinned consistently across entry.json, README (51b14e4bb5f4, an abbreviation of the same hash), sources/metarocq/SOURCE.md and source.json: 51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56. check_provenance.py passes: PCUICConfluence.v is byte-identical at that commit (153276 bytes matches entry.json files[0].bytes). Licence MIT recorded identically in entry.json, README, SOURCE.md, source.json and confirmed by sources/metarocq/upstream-LICENSE (MIT text, Gregory Malecha / Abhishek Anand / Matthieu Sozeau / Simon Boulier / Nicolas Tabareau / Cyril Cohen). All site and file permalinks use the same pinned commit, correct path pcuic/theories/PCUICConfluence.v and matching line ranges (parent 3936-3944; children 3927-3934, 3916-3923, 3404-3416). Source note present with attribution. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/MetaRocq/metarocq at commit `51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`, under `MIT`; see the [source note](../../sources/metarocq/SOURCE.md) for the licence text and attribution.
