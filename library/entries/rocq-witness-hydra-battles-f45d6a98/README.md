# Witness G with one lemma per property for Goedel's first incompleteness theorem

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | rocq |
| Status | accepted |
| Source | [hydra-battles](../../sources/hydra-battles/SOURCE.md) at `ed8e6048018a` |
| Licence | `MIT` |

## Intent

The theorem states that every ω-consistent system `T` extending `NN` has a
closed formula independent of `T`. The decomposition fixes the fixed-point
sentence `G` once (line 66), then proves each conjunct of
`independent T G ∧ closed G` — `closed G`, `SysPrf T G → Inconsistent LNN T`,
and `wConsistent T → ~ SysPrf T (notH G)` — as a separate named lemma, so the
main proof is a 10-line skeleton that poses the three lemmas and closes by
`repeat split; tauto`.

## The decomposition

### parent `Goedel'sIncompleteness1st`: [`theories/goedel/goedel1.v` lines 289-301](https://github.com/coq-community/hydra-battles/blob/ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8/theories/goedel/goedel1.v#L289-L301) ([local copy](code/theories/goedel/goedel1.v))

```coq
Theorem Goedel'sIncompleteness1st :
 wConsistent T ->
 exists f : Formula, independent T f /\ closed f.
Proof.
  intros H; exists G; pose freeVarG.
  pose FirstIncompletenessA.
  pose FirstIncompletenessB.
  assert (H0: ~Inconsistent LNN T).
  { intro H0; destruct (wCon2Con T H) as [x H1]. 
    apply H1; apply H0.
  }
  repeat split; tauto.
Qed.
```

### child `freeVarG`: [`theories/goedel/goedel1.v` lines 87-106](https://github.com/coq-community/hydra-battles/blob/ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8/theories/goedel/goedel1.v#L87-L106) ([local copy](code/theories/goedel/goedel1.v))

```coq
Lemma freeVarG : closed G. 
Proof.
  unfold closed, G.
  destruct (FixPointLNN (notH codeSysPf) 0) as [x [H1 H2]].
  unfold not in |- *; intros.
  destruct (H2 v) as [H0 H3]; rename H3 into foo; rename H0 into H3.
  absurd (v = 0).
  -  eapply in_remove_neq; apply H3; assumption.
  - eapply
      (freeVarCodeSysPf LNN LcodeLNN codeArityLNTF
         codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR). 
    + apply freeVarRepT.
    + assert
        (H5:(forall f : Formula,
                In v (freeVarF (notH f)) ->
                In v (freeVarF f))).
      { intros f H5; apply H5. }
      apply H5; eapply in_remove.
      unfold codeSysPf in H3; apply H3; assumption.
Qed.
```

### child `FirstIncompletenessA`: [`theories/goedel/goedel1.v` lines 108-124](https://github.com/coq-community/hydra-battles/blob/ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8/theories/goedel/goedel1.v#L108-L124) ([local copy](code/theories/goedel/goedel1.v))

```coq
Lemma FirstIncompletenessA : SysPrf T G -> Inconsistent LNN T.
Proof.
  unfold G; intro H.
  destruct (FixPointLNN (notH codeSysPf) 0) as [x [H1 H2]].
  unfold Inconsistent in |- *.
  intros f; apply contradiction with x.
  - assumption.
  - apply impE
      with
      (notH
         (substF (notH codeSysPf) 0
            (codeNatToTerm.natToTermLNN
               (codeFNN x)))).
    + apply cp2, iffE1; apply sysExtend with NN; auto. 
    + rewrite (subFormulaNot LNN); apply nnI; 
      now apply codeSysPfCorrect. 
Qed.
```

### child `FirstIncompletenessB`: [`theories/goedel/goedel1.v` lines 132-286](https://github.com/coq-community/hydra-battles/blob/ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8/theories/goedel/goedel1.v#L132-L286) ([local copy](code/theories/goedel/goedel1.v))

```coq
Lemma FirstIncompletenessB :
  wConsistent T -> ~ SysPrf T (notH G).
Proof.
  intros H; assert (con : (forall f:Formula, SysPrf T f) -> False).
  { intros H0. 
    destruct (wCon2Con T H) as [x H1].
    - apply H1; apply H0.
  }
  unfold G; destruct (FixPointLNN (notH codeSysPf) 0) as [x [H1 H2]].
  unfold not in |- *; intros H0.
  set (codeX := code.codeFormula   x) in *.
  unfold wConsistent in H.
  set (y := 
     notH
       (substF  codeSysPrf 0 (codeNatToTerm.natToTermLNN codeX)))
    in *.
  assert (forall x : nat, In x (freeVarF y) -> 1 = x).
  { intros x0 H3; unfold y in H3.
    assert (H4:
      (In x0
         (freeVarF 
            (substF codeSysPrf 0
               (codeNatToTerm.natToTermLNN codeX))))) by apply H3.
    destruct (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5]. 
    - destruct x0 as [| n].
      elim (in_remove_neq _ _ _ _ _ H5).
      + reflexivity.
      + destruct n as [|n ].
        * reflexivity.
        * elim (Compat815.le_not_lt (S (S n)) 1).
          assert (H6: In (S (S n)) (freeVarF codeSysPrf)).
          { eapply in_remove; apply H5. }
       
apply ( freeVarCodeSysPrf _ _ _ _ _ _ _ _ freeVarRepT _ H6).
          apply Compat815.lt_n_S; apply Nat.lt_0_succ.
    - elim (closedNatToTerm _ _ H5).
  }
  induction (H _ _ H3) as [x0 H4].
  - unfold y in H4.
    destruct 
      (eq_nat_dec
         (checkPrf LNN LcodeLNN  codeArityLNTF codeArityLNNR
            (codeFNN x) x0) 0) as [e |n ].
    + apply H4.
      rewrite (subFormulaNot LNN).
      unfold codeSysPrf, codeX in |- *.
      apply codeSysPrfCorrect3.
      unfold not in |- *; intros A p H5.
      assert (H6:
        (checkPrf LNN LcodeLNN
           codeArityLNTF codeArityLNNR
           (codeFNN x)
           (codePrf A x p) =
           S (cPair.codeList (map codeFNN A)))).
      {
        apply
          (checkPrfCorrect1 LNN LcodeLNN codeArityLNTF
             codeArityLNNR codeArityLNTFIsCorrect1
             codeArityLNNRIsCorrect1 A x p).
      }
      rewrite <- H5 in H6; rewrite H6 in e; discriminate e.
    + assert (H5:
               (checkPrf LNN LcodeLNN codeArityLNTF codeArityLNNR
                  (codeFNN x) x0 <> 0))
        by  assumption.
      clear n; decompose record
        (checkPrfCorrect2 LNN LcodeLNN codeArityLNTF
           codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2
           codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2  _ _ H5) /r;
        intros x1 H7 x2 x3 H8.

      assert (H6: x1 = x).
      { eapply codeFormulaInj.
       
        - apply H7.
      }
      cut (codePrf x2 x1 x3 = x0).
      * generalize x3.  rewrite H6; intros x4 H9.
        clear H6 H8 x3 H7 x1.
        assert
          (H6: ~
             (forall g : fol.Formula LNN,
                 In g x2 -> mem (fol.Formula LNN) T g)).
        {  unfold not in |- *; intros H6.
           assert (H7: SysPrf T x).
           { exists x2; exists x4.
             intros g H7; apply H6; assumption.
           }
           apply con; unfold Inconsistent in |- *.
           intros f; apply contradiction with x; assumption.
        }
        assert (H7: ~ (exists g : Formula, In g x2 /\ ~ mem _ T g)).
       { unfold not in |- *; intros H7; apply H4.
         rewrite (subFormulaNot LNN).
         unfold codeSysPrf, codeX in |- *; rewrite <- H9.
         apply codeSysPrfCorrect2; assumption.
       }
       clear x4 H9; induction x2 as [| a x2 Hrecx2].
       -- apply H6; intros g H8; elim H8.
       -- assert
           (H8: ~ (exists g : Formula, In g x2 /\ ~ mem (fol.Formula LNN) T g)).
          { unfold not in |- *; intros H8;  apply H7.
            destruct H8 as (x1, H8).
            exists x1; simpl in |- *; tauto.
       }
       assert
         (H9: ~
                ~
                (mem (fol.Formula LNN) T a \/ ~ mem (fol.Formula LNN) T a))
         by tauto. 
          apply H9; intros [H10| H10].
      ++ apply Hrecx2.
         ** intros H11; apply H6.
           intros g  [H12| H12].
           { rewrite <- H12; assumption. }
           { apply H11; assumption. }
         ** assumption.
      ++ apply H7; exists a; simpl in |- *.
         split; auto.
      * assumption.
  - apply impE
      with
      (notH
         (substF (notH codeSysPf) 0
            (codeNatToTerm.natToTermLNN codeX))).
    + unfold codeSysPf, codeSysPrf.codeSysPf, y in |- *.
      fold codeSysPrf in |- *.
      rewrite (subFormulaNot LNN).
      apply
        impTrans
        with
        (substF (existH 1 codeSysPrf) 0
           (codeNatToTerm.natToTermLNN codeX)).
      * apply impI; apply nnE; apply Axm; right; constructor.
      * apply sysExtend with NN.
        -- assumption.
        -- apply impI; rewrite (subFormulaExist LNN).
           destruct (eq_nat_dec 1 0) as [e|n].
           ++ discriminate e.
           ++ induction
               (In_dec eq_nat_dec 1 (freeVarT 
                                       (codeNatToTerm.natToTermLNN codeX)))
                 as [a | _]. 
              ** elim (closedNatToTerm _ _ a).
              ** clear n; apply existSys.
                 { apply closedNN. }
                 { unfold not in |- *; intros H4.
                   elim (in_remove_neq _ _ _ _ _ H4).
                   reflexivity. }
                 {apply existSimp; apply nnI.
                  apply Axm; right; constructor. }
    + apply impE with (notH x).
      * apply cp2; apply iffE2; apply sysExtend with NN; assumption.
      * apply H0; assumption.
Qed.
```

### context `G`: [`theories/goedel/goedel1.v` lines 66-66](https://github.com/coq-community/hydra-battles/blob/ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8/theories/goedel/goedel1.v#L66-L66) ([local copy](code/theories/goedel/goedel1.v))

```coq
Definition G := let (a,_) := FixPointLNN (notH codeSysPf) 0 in a.
```

How the parts fit. The parent's goal expands, via
`independent T f := ~ SysPrf T f ∧ ~ SysPrf T (~ f)%fol` and
`closed a := forall v, ~ In v (freeVarF a)`, to
`∃ f, (~ SysPrf T f ∧ ~ SysPrf T (notH f)) ∧ closed f`. The proof names the
witness with `exists G`, poses the three lemmas into the context, asserts
`H0 : ~ Inconsistent LNN T` (proved by `wCon2Con`, i.e. ω-consistency implies
consistency), then runs `repeat split; tauto`. `repeat split` turns the
conjunction into three goals — `closed G`, `~ SysPrf T G`,
`~ SysPrf T (notH G)` — and `tauto` closes each from the posed hypotheses:

```
Goedel'sIncompleteness1st
  ├─ freeVarG              : closed G
  ├─ FirstIncompletenessA  : SysPrf T G -> Inconsistent LNN T
  └─ FirstIncompletenessB  : wConsistent T -> ~ SysPrf T (notH G)
```

- `freeVarG` discharges `closed G` directly.
- `FirstIncompletenessA` gives `SysPrf T G -> Inconsistent`, so against the
  asserted `~ Inconsistent LNN T` it yields `~ SysPrf T G`.
- `FirstIncompletenessB` gives `wConsistent T -> ~ SysPrf T (notH G)`, so
  against the hypothesis `H : wConsistent T` it yields the last conjunct.

Each child is a good leaf because its statement is self-contained and its proof
closes on its own or from imported hydras lemmas, never from a sibling:
`freeVarG` is a local unfold-and-contradiction over the fixed point and the free
variables of `codeSysPf`; `FirstIncompletenessA` closes from `codeSysPfCorrect`
(the correctness of the code predicate); `FirstIncompletenessB` closes from
`wCon2Con`, `codeSysPrfCorrect2/3` and `checkPrfCorrect1/2`. The witness `G` is
built once by the fixed-point construction `FixPointLNN (notH codeSysPf) 0`
(line 66) and is shared by the parent and all three children.

## Why it is good

1. The parent closes in 10 lines — `exists G`, three `pose`s, one `assert`
   discharged by `wCon2Con`, then `repeat split; tauto` — so the three children
   discharge all three conjuncts of `independent T G ∧ closed G` (check, lines
   289-301).
2. The glue is 10 lines (292-301) while the children's proofs span 19, 16 and
   153 lines; the glue hides 188 lines of argument behind three lemma names
   (measurement, line counts of the copied file).
3. The author documents the design of `FirstIncompletenessB` in a comment: "I
   don't believe I can prove (SysPrf T (notH G))->(wInconsistent T). So instead
   I prove:" (author-statement, lines 126-130).
4. Each child closes independently of the others — `freeVarG` uses the fixed
   point and `freeVarCodeSysPrf`, `FirstIncompletenessA` uses
   `codeSysPfCorrect`, `FirstIncompletenessB` uses `wCon2Con` and
   `codeSysPrfCorrect2/3`; no child cites another (check, whole file).

In my opinion the detail worth copying is the one-lemma-per-conjunct shape: the
witness is fixed up front, so the glue never mentions the fixed-point
construction again, and each property is a named lemma with a statement the
final `tauto` can use without unfolding anything.

## When to use it, and when not

Use it when the goal is an existential `∃ f, P f` whose witness can be fixed up
front — a fixed point, a constructed object — and whose target `P f` is a
conjunction of properties that are independent of one another and each provable
as a self-contained named lemma. The glue then collapses to `exists w` plus
`repeat split; tauto`.

Avoid it when the witness has to be adjusted during the proof, when the
properties are interdependent (one lemma needs another's conclusion, so they
cannot be stated and proved in isolation), or when a property does not factor
into a named lemma but needs a bespoke argument in the main proof.

## Consequences

The move creates one obligation per conjunct of the witness's specification —
here `closed G`, `~ SysPrf T G`, `~ SysPrf T (notH G)` — surfaced by
`repeat split`, plus the obligation that the witness is well-defined (here
discharged once by the fixed-point construction `FixPointLNN`). All the real
work is deferred to the children, so the theorem fails if any child is
unprovable, or if a child is stated slightly weaker than its conjunct, in which
case `tauto` cannot use it. The glue does no case analysis of its own beyond the
final `repeat split`.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml (Docker CI) triggers on pushes to master and builds the coq-goedel package via 'opam install coq-goedel' -> 'dune build -p coq-goedel'; theories/goedel/dune declares (coq.theory (name Goedel) (package coq-goedel)) with no modules filter so it builds all of theories/goedel/*.v including goedel1.v. Commit ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8 is the head of master (default branch). | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read the copied file (provenance pass, byte-identical to ed8e604). Lines 289-301: Theorem Goedel'sIncompleteness1st; proof body 292-301 = 10 lines. Line 293 'exists G; pose freeVarG', 294 'pose FirstIncompletenessA', 295 'pose FirstIncompletenessB', 296 'assert (H0: ~Inconsistent LNN T)', 297 discharged by 'wCon2Con T H', 300 'repeat split; tauto'. Matches the claim exactly. | verifier |
| 2 | verified | Counted lines in the copied file: main proof Proof.(292)..Qed.(301)=10; freeVarG Proof.(88)..Qed.(106)=19; FirstIncompletenessA Proof.(109)..Qed.(124)=16; FirstIncompletenessB Proof.(134)..Qed.(286)=153; 19+16+153=188. Matches the claim. | verifier |
| 3 | verified | Read lines 126-130 of the copied file: comment '(*I don't believe I can prove (SysPrf T (notH G))->(wInconsistent T)) So instead I prove: *)'. The author-statement is accurate in substance; the claim's quote inserts a period after 'wInconsistent T)' (source has 'T))' with no period), a trivial punctuation normalization, and the comment directly precedes Lemma FirstIncompletenessB stated as 'wConsistent T -> ~ SysPrf T (notH G)'. | verifier |
| 4 | verified | Read the whole copied file. freeVarG (87-106) destructs the fixed point (FixPointLNN, line 90) and uses freeVarCodeSysPf (96) and freeVarRepT (98); FirstIncompletenessA (108-124) uses codeSysPfCorrect (123); FirstIncompletenessB (132-286) uses wCon2Con (137), codeSysPrfCorrect3 (178), codeSysPrfCorrect2 (227). None of the three lemmas cites any of the others; they are stated independently in the section and only the parent poses all three. The claim's spelling 'freeVarCodeSysPrf' is a one-letter typo for 'freeVarCodeSysPf' and 'uses only the fixed point' omits freeVarRepT, but the independence claim (no child cites another) is correct. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent (289-301) poses exactly freeVarG, FirstIncompletenessA, FirstIncompletenessB, then repeat split; tauto closes all three conjuncts; child statements match code verbatim; glue_lines 10 (292-301); child_lines 19/16/153 = 88-106/109-124/134-286; direct_lemmas 3; depth 1; closed_by matches tactics; provenance passes. | reviewer-correctness |
| generality | accept | Generality is strong and honest. The move is stated beyond the example: goal_shape/use_when/avoid_when abstract to 'exists f, P f' where P f is a conjunction of independent properties and the witness is fixed up front, with the mechanism (exists G + repeat split; tauto) named. avoid_when gives three concrete conditions (witness adjusted mid-proof; interdependent properties; a property that doesn't factor into a named lemma), and consequences enumerate per-conjunct obligations plus well-definedness and the 'child stated slightly weaker than its conjunct, so tauto cannot use it' failure mode — which the entry itself exhibits (FirstIncompletenessA is an implication needing the glue's assert ~Inconsistent, flagged honestly). It says what makes children good leaves: self-contained statement, closes on its own or from imported hydras lemmas, never from a sibling (README). Minor imprecision not worth objecting: 'no case analysis beyond repeat split' overlooks the destruct of wCon2Con in the assert, but that is existential-elimination (no branches), and the 153-line FirstIncompletenessB is honestly recorded. | reviewer-generality |
| provenance-licence | accept | Provenance is consistent and traceable. check_provenance.py passed: code/theories/goedel/goedel1.v is byte-identical at pinned commit ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8 (9666 bytes; sha256 4081bd6d...f4757 matches entry.json). Commit recorded identically in entry.json, source.json and SOURCE.md. Permalinks all use repo coq-community/hydra-battles at that commit with correct path and line ranges (verified against the copied file: G at 66, freeVarG 87-106, FirstIncompletenessA 108-124, FirstIncompletenessB 132-286, parent 289-301). Licence MIT recorded consistently in entry.json, source.json, SOURCE.md and README; upstream LICENSE at the commit is the MIT License and matches sources/hydra-battles/upstream-LICENSE verbatim. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/coq-community/hydra-battles at commit `ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8`, under `MIT`; see the [source note](../../sources/hydra-battles/SOURCE.md) for the licence text and attribution.
