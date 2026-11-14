# Strengthen the goal to A = ordinal for the converse of Schutte 13.6

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | rocq |
| Status | accepted |
| Source | [hydra-battles](../../sources/hydra-battles/SOURCE.md) at `ed8e6048018a` |
| Licence | `MIT` |

## Intent

Prove the converse half of Schutte's characterisation of normal ordering
functions. The proof does not attack `normal f B` head-on: it strengthens the
goal to the convenient equality `A = ordinal` (from `segment A` and `Unbounded
A`), after which `normal f B` collapses to `ordering_function f ordinal B`
(already the hypothesis) and the continuity half `continuous f ordinal B`,
which the already-proved direction `Th_13_5_2` closes.

## The decomposition

### parent `TH_13_6R`: [`theories/ordinals/Schutte/Ordering_Functions.v` lines 1159-1169](https://github.com/coq-community/hydra-battles/blob/ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8/theories/ordinals/Schutte/Ordering_Functions.v#L1159-L1169) ([local copy](code/theories/ordinals/Schutte/Ordering_Functions.v))

```coq
Theorem TH_13_6R (A B : Ensemble Ord) (f : Ord -> Ord) :
  ordering_function f A B ->
  Closed B ->    Unbounded B ->   normal f B.
Proof with auto with schutte.
  intros  H0 H1 H2; assert (A = ordinal).
    {   apply segment_unbounded.
        - eapply SA1;  apply H0.
        - destruct (ordering_unbounded_unbounded H0); auto.
    }
    subst A; split; [trivial | now apply Th_13_5_2].
Qed.
```

### child `segment_unbounded`: [`theories/ordinals/Schutte/Ordering_Functions.v` lines 216-224](https://github.com/coq-community/hydra-battles/blob/ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8/theories/ordinals/Schutte/Ordering_Functions.v#L216-L224) ([local copy](code/theories/ordinals/Schutte/Ordering_Functions.v))

```coq
Theorem segment_unbounded : forall A:Ensemble Ord, segment A ->
                                        Unbounded A ->
                                        A = ordinal.
Proof with eauto with schutte.
 intros A H H0; red in H0; apply Extensionality_Ensembles; split.
 - intros; split.
 -  intros x Hx; destruct (H0 x) as [x0 H1]...
    destruct H1; now apply H with x0.
Qed.
```

### child `SA1`: [`theories/ordinals/Schutte/Ordering_Functions.v` lines 261-262](https://github.com/coq-community/hydra-battles/blob/ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8/theories/ordinals/Schutte/Ordering_Functions.v#L261-L262) ([local copy](code/theories/ordinals/Schutte/Ordering_Functions.v))

```coq
 Remark SA1 : segment A1.
 Proof.   case O1;intuition.  Qed.
```

### child `ordering_unbounded_unbounded`: [`theories/ordinals/Schutte/Ordering_Functions.v` lines 1139-1156](https://github.com/coq-community/hydra-battles/blob/ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8/theories/ordinals/Schutte/Ordering_Functions.v#L1139-L1156) ([local copy](code/theories/ordinals/Schutte/Ordering_Functions.v))

```coq
Lemma ordering_unbounded_unbounded :
  forall A B f,  ordering_function f A B ->
                 (Unbounded B <-> Unbounded A).
Proof with auto with schutte.
  intros A B f  H0;split.
  - intro; apply not_countable_unbounded.
    intro H2;  assert (H3 : Countable B).
    {  apply countable_bij_fun with Ord A  f ...
       apply Ordering_bijection;auto.
    }
    case (countable_not_Unbounded  H3);auto.
  - intro H1;  apply not_countable_unbounded ...
    intro H2;  assert (H3 : Countable A).
    { apply countable_bij_funR with Ord   B  f;auto.
      apply Ordering_bijection;auto.
    }
 case (countable_not_Unbounded (X:= A));auto.
Qed.
```

### child `Th_13_5_2`: [`theories/ordinals/Schutte/Ordering_Functions.v` lines 1107-1115](https://github.com/coq-community/hydra-battles/blob/ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8/theories/ordinals/Schutte/Ordering_Functions.v#L1107-L1115) ([local copy](code/theories/ordinals/Schutte/Ordering_Functions.v))

```coq
 Lemma Th_13_5_2 : continuous f A B.
 Proof.
   split.
   - red.
     case f_ord;tauto.
   - split. red. intros.
     eapply A_closed;auto.
     intros;symmetry;apply f_sup_commutes;auto.
 Qed.
```

How the parts fit. The parent `TH_13_6R` splits `normal f B` into its two
conjuncts only at the very end. Its real work is the single
`assert (A = ordinal)`, which it proves with `segment_unbounded`, discharging
that lemma's two premises:

- `segment A` — closed by `eapply SA1; apply H0` (`SA1` states `segment A1`
  under the hypothesis `ordering_function f1 A1 B`, so `apply H0` instantiates
  `A1` to `A`).
- `Unbounded A` — closed by `destruct (ordering_unbounded_unbounded H0)`,
  which turns the hypothesis `Unbounded B` into `Unbounded A`.

With `A = ordinal` in hand, `subst A` rewrites the goal and the hypotheses;
`split` then produces the two conjuncts of `normal f ordinal B`:
`ordering_function f ordinal B` (closed by `trivial`, i.e. the substituted
hypothesis `H0`) and `continuous f ordinal B` (closed by
`now apply Th_13_5_2`, which consumes `H0` and `H1`).

Why each direct lemma is a good leaf:

- `segment_unbounded` — a self-contained statement (`segment A -> Unbounded A
  -> A = ordinal`) whose proof closes by extensionality and the two inclusions,
  citing no named sibling.
- `SA1` — a one-line `case O1;intuition` that extracts the `segment` field of
  `ordering_function`; its section variables generalise to exactly the shape
  the glue consumes.
- `ordering_unbounded_unbounded` — a self-contained iff transferring
  `Unbounded` across an ordering bijection, closed by `not_countable_unbounded`
  plus `countable_bij_fun`/`countable_bij_funR` with `Ordering_bijection`.
- `Th_13_5_2` — the already-proved forward half (continuity), closed from the
  section hypothesis `f_ord` and `B_closed` via `A_closed` and
  `f_sup_commutes`; the parent reuses it wholesale.

Below `Th_13_5_2` the project lemmas chain down 11 links:
`Th_13_5_2 → f_sup_commutes → R42 → R7 → R6 → R5 → alpha_sup → R3 → R2 →
R1_aux → Ordering_bijection`, each link a citation in the same file (see claim
3 and the `shape.depth`). None of those appear in the glue; they are what
makes `Th_13_5_2` a black box the parent can reuse.

## Why it is good

1. `TH_13_6R` is declared in lines 1159-1169 of `Ordering_Functions.v`
   (check, decided by `check_claims.py` as `declared(TH_13_6R, ...)`).
2. The parent site cites `Th_13_5_2`, so the glue reuses the already-proved
   forward direction rather than re-proving continuity (check, decided as
   `cites(parent, Th_13_5_2)`).
3. The glue is thin on purpose: it cites 4 named lemmas directly, and the
   longest chain of project lemmas below it is 11 links
   (`TH_13_6R → Th_13_5_2 → f_sup_commutes → R42 → R7 → R6 → R5 → alpha_sup →
   R3 → R2 → R1_aux → Ordering_bijection`), so the parent is a skeleton with
   one hole per named lemma (measurement, counted line by line).
4. The lemmas are not ad hoc: the author frames the module as Schutte's
   construction, "Every subset [A] of [Ord] can be enumerated in an unique way
   by a segment of [Ord] ... following Schutte's definitions" (author
   statement, file header lines 4-14).

In my opinion the move's value is in the choice of *which* statement to
strengthen to: `A = ordinal` is far stronger than the goal needs, but it is
exactly the shape that lines the already-proved `Th_13_5_2` and the hypothesis
up with the goal, so the rest of the proof is `subst` plus one split.

## When to use it, and when not

Use it when the goal is phrased over a fixed object (`ordinal`, a canonical
representative) while the hypotheses and the lemmas already proved are phrased
over a free variable (`A`): asserting the equality that pins the free variable
to that object makes everything line up, and the equality itself follows from
small, named lemmas. Avoid it when the pinning equality is no easier than the
original goal, or when the goal does not collapse to a known lemma after the
substitution — a strengthening that does not line the goal up with existing
facts buys nothing.

This is the `suffices`/strengthen move of survey F §10 rule 8 ("Backward rule,
`suffices`, and witnesses as templates"), written here as a forward
`assert (A = ordinal)` plus `subst` rather than a `suffices` keyword.

## Consequences

The move replaces the two conjuncts of `normal f B` with one obligation
`A = ordinal` and two side conditions (`segment A`, `Unbounded A`). It is sound
only because `segment A` + `Unbounded A` force `A = ordinal`; for a mere
subset the `subst A` would not type-check. The strengthened equality is
discharged by two further lemmas (`segment_unbounded`, which itself needs
`SA1` and `ordering_unbounded_unbounded`), so the glue's own proof stays short
while the real content moves into the children — and the continuity half is a
wholesale reuse of `Th_13_5_2` rather than new work.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-default.yml (jobs hydra-battles and build-doc build all theories/, including theories/ordinals/Schutte/Ordering_Functions.v, on push to default branch master); commit ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8 | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: segment_unbounded@theories/ordinals/Schutte/Ordering_Functions.v:1164, SA1@theories/ordinals/Schutte/Ordering_Functions.v:1165, ordering_unbounded_unbounded@theories/ordinals/Schutte/Ordering_Functions.v:1166, Th_13_5_2@theories/ordinals/Schutte/Ordering_Functions.v:1168; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(TH_13_6R, theories/ordinals/Schutte/Ordering_Functions.v, 1159-1169) -> declared: TH_13_6R is declared at theories/ordinals/Schutte/Ordering_Functions.v:1159 | check_claims.py |
| 2 | verified | cites(parent, Th_13_5_2) -> cites: Th_13_5_2 occurs at theories/ordinals/Schutte/Ordering_Functions.v:1168 | check_claims.py |
| 3 | verified | read parent site 1159-1169: 4 direct citations at 1164 (apply segment_unbounded), 1165 (eapply SA1), 1166 (ordering_unbounded_unbounded), 1168 (apply Th_13_5_2). Chain verified link by link: Th_13_5_2->f_sup_commutes (1114 apply f_sup_commutes), f_sup_commutes->R42 (1099 apply R42), R42->R7 (1086 case R7), R7->R6 (1040 apply R6), R6->R5 (1018 case (R5 H)), R5->alpha_sup (1010 rewrite alpha_sup), alpha_sup->R3 (1004 apply R3), R3->R2 (986 apply R2; evidence said 985, off by one), R2->R1_aux (979 apply R1_aux), R1_aux->Ordering_bijection (956 case (Ordering_bijection f_ord)). 11 links confirmed; 'longest' not independently re-derived | verifier |
| 4 | verified | read code/theories/ordinals/Schutte/Ordering_Functions.v lines 4-14: module comment reads 'Every subset [A] of [Ord] can be enumerated in an unique way by a segment of [Ord].' ... 'This module shows the construction of the _ordering function_ of [A], following Schutte's definitions.' — matches the quoted claim | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent TH_13_6R (1159-1169) matches the entry: it asserts (A=ordinal) via segment_unbounded (discharging segment A with SA1 and Unbounded A with ordering_unbounded_unbounded), then subst A; split; [trivial | now apply Th_13_5_2]. The four children are exactly the lemmas the glue cites (segment_unbounded@1164, SA1@1165, ordering_unbounded_unbounded@1166, Th_13_5_2@1168) and their copied statements and closed_by match the code (SA1 case O1;intuition; ordering_unbounded_unbounded split/not_countable_unbounded; Th_13_5_2 split/f_sup_commutes). It closes: normal is defined (line 65) as ordering_function f ordinal B AND continuous f ordinal B, so trivial closes the first conjunct from the substituted H0 and Th_13_5_2 (forall A B f, ordering_function f A B -> Closed B -> continuous f A B) closes the second from H0/H1; Qed at 1169, no sorry. Shape numbers are right: direct_lemmas=4, glue_lines=11 (1159-1169), child_lines=[9,2,18,9] for the four sites, and depth=11 matches the verified chain TH_13_6R->Th_13_5_2->f_sup_commutes->R42->R7->R6->R5->alpha_sup->R3->R2->R1_aux->Ordering_bijection (11 links). One trivial note for a later pass: claim 3 lists line 985 for the R3->R2 link but R2 is cited at line 986; the depth and count are unaffected. | reviewer-correctness |
| generality | accept | Generality is well-served. The move is stated beyond the example: use_when/avoid_when and the README's 'When to use it, and when not' abstract the pattern to 'goal phrased over a fixed object while hypotheses/lemmas are phrased over a free variable; assert the pinning equality so the goal collapses to an already-proved lemma'. avoid_when is honest and specific ('pinning equality no easier than the goal' / 'goal does not collapse to a known lemma after substitution'). Consequences are honest and specific, naming the soundness condition (segment A + Unbounded A force A = ordinal; a mere subset would not let subst type-check) and correctly noting the assert+subst is a forward spelling of suffices, not the keyword. The 'Why each direct lemma is a good leaf' section answers the bounded-prover question: leaves are self-contained (cite no named sibling), small, section-generalised to the exact shape the glue consumes, and Th_13_5_2 hides an 11-link chain so a bounded prover reuses it wholesale as a black box. | reviewer-generality |
| provenance-licence | accept | Provenance and licence consistent and traceable. check_provenance pass: the sole copied file code/theories/ordinals/Schutte/Ordering_Functions.v is byte-identical at pinned commit ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8. Commit, URL (github.com/coq-community/hydra-battles) and MIT licence agree across entry.json, README, sources/hydra-battles/SOURCE.md and source.json; upstream-LICENSE is a real MIT text. All five site permalinks and the files[] permalink use the same commit with correct line anchors (parent 1159-1169, children 216-224/261-262/1139-1156/1107-1115), and sed on the local copy confirms each cited range matches the README excerpt; claim 4's author-statement quote matches header lines 4-14. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/coq-community/hydra-battles at commit `ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8`, under `MIT`; see the [source note](../../sources/hydra-battles/SOURCE.md) for the licence text and attribution.
