# Sum-check single round: transport the simple verifier's knowledge soundness to the lifted oracle verifier

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | lean |
| Status | verified |
| Source | [arklib](../../sources/arklib/SOURCE.md) at `6f9884a95ae7` |
| Licence | `Apache-2.0` |

## Intent

Round-by-round knowledge soundness of the full single-round oracle verifier is
not proved from scratch: the verifier is first rewritten to its context-lifted
form, then the soundness bound of the simpler "virtual" round is transported
along the oracle-statement lens by instantiating the one general transport
theorem `OracleVerifier.liftContext_rbrKnowledgeSoundness`. The proof is 12
lines of glue around three named lemmas.

## The decomposition

### parent `oracleVerifier_rbrKnowledgeSoundness`: [`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean` lines 1180-1191](https://github.com/Verified-zkEVM/ArkLib/blob/6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6/ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1180-L1191) ([local copy](code/ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean))

```lean
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype R] [IsDomain R] :
    (oracleVerifier R n deg D oSpec i).toVerifier.rbrKnowledgeSoundness init impl
    (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
    (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  rw [oracleVerifier_eq_liftContext]
  exact OracleVerifier.liftContext_rbrKnowledgeSoundness
    (stmtLens := oStmtExecutableLens R n deg D i)
    (witLens := Witness.InvLens.trivial)
    (Simple.oracleVerifier R deg D oSpec)
    (liftContextOutput R n deg D oSpec i)
    (lensKS := by simpa using extractorLens_rbr_knowledge_soundness i)
    (Simple.oracleVerifier_rbrKnowledgeSoundness R deg D oSpec)
```

### child `oracleVerifier_eq_liftContext`: [`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean` lines 893-928](https://github.com/Verified-zkEVM/ArkLib/blob/6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6/ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L893-L928) ([local copy](code/ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean))

```lean
theorem oracleVerifier_eq_liftContext (i : Fin n) :
    oracleVerifier R n deg D oSpec i =
      (Simple.oracleVerifier R deg D oSpec).liftContext
        (oStmtExecutableLens R n deg D i) (liftContextOutput R n deg D oSpec i) := by
  apply OracleVerifier.ext
  · funext stmt challenges
    apply OptionT.ext
    change Option.map (fun result : R × R =>
        (⟨result.1, Fin.snoc stmt.challenges result.2⟩ : StatementRound R n i.succ)) <$>
        simulateQ (verifierQueryImpl R n deg oSpec)
          ((Simple.oracleVerifier R deg D oSpec).verify stmt.target challenges).run =
      Option.map (fun result : R × R =>
        (⟨result.1, Fin.snoc stmt.challenges result.2⟩ : StatementRound R n i.succ)) <$>
        simulateQ (OracleVerifier.liftContextQueryImpl (oStmtExecutableLens R n deg D i) stmt)
          ((Simple.oracleVerifier R deg D oSpec).verify stmt.target challenges).run
    congr 1
    have hb := Simple.oracleVerifier_only_message_queries R deg D oSpec stmt.target challenges
    generalize
      ((Simple.oracleVerifier R deg D oSpec).verify stmt.target challenges).run = oa at hb ⊢
    revert hb
    induction oa using OracleComp.inductionOn with
    | pure x => intro _; rfl
    | query_bind q next ih =>
        intro hb
        obtain ⟨⟨j, rfl⟩, hnext⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).1 hb
        simp only [simulateQ_bind, simulateQ_spec_query]
        have hh : verifierQueryImpl R n deg oSpec (Sum.inr (Sum.inr j)) =
            OracleVerifier.liftContextQueryImpl (oStmtExecutableLens R n deg D i) stmt
              (Sum.inr (Sum.inr j)) := by
          simp only [verifierQueryImpl, OracleVerifier.liftContextQueryImpl,
            QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
        rw [hh]
        congr 1
        funext answer
        exact ih answer (hnext answer)
  · rfl
```

### child `extractorLens_rbr_knowledge_soundness`: [`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean` lines 1115-1131](https://github.com/Verified-zkEVM/ArkLib/blob/6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6/ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1115-L1131) ([local copy](code/ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean))

```lean
instance extractorLens_rbr_knowledge_soundness :
    Extractor.Lens.IsKnowledgeSound
      (relationRound R n deg D i.castSucc) (Simple.inputRelation R deg D)
      (relationRound R n deg D i.succ) (Simple.outputRelation R deg)
      ((Simple.oracleVerifier R deg D oSpec).toVerifier.compatStatement (oStmtLens R n deg D i))
      (fun _ _ => True)
      ⟨oStmtLens R n deg D i, Witness.InvLens.trivial⟩ where
  proj_knowledgeSound := by
    rintro ⟨stmt, os⟩ ⟨⟨target, r⟩, ios⟩ ⟨⟩ hc ho
    left
    have hp := verifier_polynomial i stmt os ((target, r), ios) hc
    have hi := (output_projection i stmt os target r).mp ho
    change ios () = projectedRoundPolynomial R n deg D i stmt.challenges (os ()) at hp
    simpa [Simple.outputRelation, hp] using hi
  lift_knowledgeSound := by
    rintro ⟨stmt, os⟩ ⟨⟩ ⟨⟩ _ h
    exact (input_projection i stmt os).mp h
```

### child `oracleVerifier_rbrKnowledgeSoundness`: [`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean` lines 583-587](https://github.com/Verified-zkEVM/ArkLib/blob/6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6/ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L583-L587) ([local copy](code/ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean))

```lean
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype R] [IsDomain R] :
    (oracleVerifier R deg D oSpec).toVerifier.rbrKnowledgeSoundness init impl
    (inputRelation R deg D) (outputRelation R deg) (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  rw [oracleVerifier_eq_verifier]
  exact verifier_rbrKnowledgeSoundness R deg D oSpec
```

How the parts fit. The glue first rewrites the target object with
`oracleVerifier_eq_liftContext`, exposing it as
`(Simple.oracleVerifier ...).liftContext (oStmtExecutableLens ...) ...`. It
then instantiates the general transport theorem
`OracleVerifier.liftContext_rbrKnowledgeSoundness` (defined in
`ArkLib/OracleReduction/LiftContext/OracleReduction.lean` lines 388-408, copied
under `code/`) with three named arguments:

```text
oracleVerifier_rbrKnowledgeSoundness  (parent, 1180-1191)
└── rw [oracleVerifier_eq_liftContext]                     (child, 893-928)
    exact OracleVerifier.liftContext_rbrKnowledgeSoundness (general transport, LiftContext 388-408)
      ├── stmtLens := oStmtExecutableLens ...              (def, this file 772-792)
      ├── lensKS   := extractorLens_rbr_knowledge_soundness (child, 1115-1131)
      └── h        := Simple.oracleVerifier_rbrKnowledgeSoundness (child, 583-587)
```

Each child is a good leaf because its statement is self-contained and its
proof closes on its own or from named siblings:

- `oracleVerifier_eq_liftContext` (lines 893-928) is an equality of two
  verifiers. It closes by `apply OracleVerifier.ext`, then induction on the
  oracle computation `oa using OracleComp.inductionOn`; the query case is
  discharged by the named sibling `Simple.oracleVerifier_only_message_queries`
  (line 909, declared at 309-384).
- `extractorLens_rbr_knowledge_soundness` (lines 1115-1131) is an `instance` of
  `Extractor.Lens.IsKnowledgeSound` with two fields, each closing from a named
  sibling: `proj_knowledgeSound` cites `verifier_polynomial` (1034) and
  `output_projection` (1023); `lift_knowledgeSound` cites `input_projection`
  (1011).
- `Simple.oracleVerifier_rbrKnowledgeSoundness` (lines 583-587, in namespace
  `Simple`) is the inner round's certificate, closing by
  `rw [oracleVerifier_eq_verifier]` then `exact verifier_rbrKnowledgeSoundness`
  (its non-oracle sibling, 564-580).

Below the parent, the deepest chain of project lemmas I checked runs
`oracleVerifier_rbrKnowledgeSoundness` → `extractorLens_rbr_knowledge_soundness`
→ `output_projection` → `relationRound_output_iff` (675) →
`relationRound_projected_output` (652), a depth of 4; the last lemma closes by
library lemmas (`Polynomial.eval_finsetSum`, `MvPolynomial.eval_evalExcept_append`,
`Fin.sum_piFinset_cast`).

## Why it is good

1. The parent theorem `oracleVerifier_rbrKnowledgeSoundness` is declared at
   lines 1180-1191 of `ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean`
   (check, `declared`; permalink above).
2. The parent site cites the lens certificate
   `extractorLens_rbr_knowledge_soundness` (check, `cites`; line 1190).
3. The glue is 12 lines and cites three named lemmas whose sites are 36, 17 and
   5 lines (58 in total), so the argument is carried by the children and the
   glue only assembles them (measurement; site line ranges in `entry.json`).
4. The same move — transport the soundness bound from the simple round to the
   full round along the statement lens — is applied again at
   `verifier_rbrKnowledgeSoundness` (lines 1146-1157), with
   `Verifier.liftContext_rbrKnowledgeSoundness` in place of the oracle-verifier
   transport (known-use).
5. The blueprint documents the move: node `thm:sumcheck_single_round_soundness`
   names `Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness` and
   states "The round is obtained by lifting the virtual round below along a
   context lens, which transfers both properties."
   ([sumcheck.tex lines 184-191](https://github.com/Verified-zkEVM/ArkLib/blob/6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6/blueprint/src/proof_systems/sumcheck.tex#L184-L191),
   author-statement).

In my opinion the detail worth copying is the division of labour: the *hard*
soundness argument is done once for the univariate "virtual" round and once for
the general lens, and the full round contributes only an equivalence rewrite
and a lens certificate. AutoDecompose should look for this shape — a target
object that is a `liftContext`/transport of a simpler object, with a general
transport lemma already in the library — before attempting the soundness proof
directly.

Survey F §10 has no numbered rule for generalise-then-instantiate; the nearest
described moves are §8's "Generalise / strengthen" (free) and "Reusable schema
instantiation" (mechanical, ProofEvolve), so `entry.json` records `f10_rule:
null`.

## When to use it, and when not

Use it when the goal is a property of a *lifted* object
(`X.liftContext lens output`, or any transport/instantiation of a general
construction), and all three ingredients are already available: a general
transport theorem that lifts the property across the lens, an equivalence
showing the target object is exactly the context-lift, and a certificate that
the lens itself satisfies the lifted class. This is the situation ArkLib built
for its sum-check round: the simple round and the lens framework are proved
once, and every round's soundness is an instantiation.

Avoid it when the lens is not executable or not knowledge-sound (the `lensKS`
argument would be missing), when the inner object's property is not already
proved (you would still have to do the hard work, just relocated), or when the
equivalence rewrite does not hold by `rfl`/`simp` and needs a real argument of
its own — then the "instantiate" step stops being cheap.

## Consequences

The move turns one soundness proof into three named obligations: (1) an
equivalence showing the target object is the context-lift
(`oracleVerifier_eq_liftContext`), (2) a lens knowledge-soundness certificate
(`extractorLens_rbr_knowledge_soundness`, itself split into a projection and a
lift field), and (3) the inner object's certificate
(`Simple.oracleVerifier_rbrKnowledgeSoundness`). The known failure mode is in
the `lensKS := by simpa using extractorLens_rbr_knowledge_soundness i` argument:
it only closes when the executable-lens definition simplifies to exactly the
class instance; a lens that is not `simp`-normal would need its own rewrite
step before the transport can be applied.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/ci.yml build job runs 'lake build' on push to main (default branch); pinned commit 6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6 on main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: oracleVerifier_eq_liftContext@ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1184, extractorLens_rbr_knowledge_soundness@ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1190, oracleVerifier_rbrKnowledgeSoundness@ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1180; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(oracleVerifier_rbrKnowledgeSoundness, ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean, 1180-1191) -> declared: oracleVerifier_rbrKnowledgeSoundness is declared at ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1180 | check_claims.py |
| 2 | verified | cites(parent, extractorLens_rbr_knowledge_soundness) -> cites: extractorLens_rbr_knowledge_soundness occurs at ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1190 | check_claims.py |
| 3 | verified | line ranges checked in copied code: parent 1180-1191 (12 lines), children 893-928 (36), 1115-1131 (17), 583-587 (5); 36+17+5=58 > 12 | verifier |
| 4 | verified | lines 1146-1157 show verifier_rbrKnowledgeSoundness applying Verifier.liftContext_rbrKnowledgeSoundness with stmtLens, witLens, lensKS (citing extractorLens_rbr_knowledge_soundness) and Simple.verifier_rbrKnowledgeSoundness | verifier |
| 5 | verified | blueprint/src/proof_systems/sumcheck.tex#L184-L191: \label{thm:sumcheck_single_round_soundness}, \lean{...Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness}, text 'The round is obtained by lifting the virtual round below along a context lens, which transfers both properties.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent (1180-1191) and three children (oracleVerifier_eq_liftContext 893-928, extractorLens_rbr_knowledge_soundness 1115-1131, Simple.oracleVerifier_rbrKnowledgeSoundness 583-587) match entry.json verbatim; closing methods match (eq_liftContext: apply OracleVerifier.ext + induction citing Simple.oracleVerifier_only_message_queries 309-384; extractorLens: proj cites verifier_polynomial 1034/output_projection 1023, lift cites input_projection 1011; Simple child: rw oracleVerifier_eq_verifier + exact verifier_rbrKnowledgeSoundness 564-580). Parent closes via rw [oracleVerifier_eq_liftContext] then exact OracleVerifier.liftContext_rbrKnowledgeSoundness whose signature (OracleReduction.lean 388-408) matches the named args. Glue cites exactly the 3 children plus the general transport theorem (correctly classed as the reusable schema, not a child). Shape numbers correct: glue_lines 12 (1180-1191), child_lines [36,17,5] (893-928/1115-1131/583-587), depth 4 (extractorLens->output_projection->relationRound_output_iff 675->relationRound_projected_output 652, closing at library lemmas), direct_lemmas 3. No sorry/admit/axiom in copied files. | reviewer-correctness |
| generality | object | Generality is mostly strong: the move is stated over any lifted object (X.liftContext lens output / transport of a general construction), use_when names four concrete ingredients, consequences list three named obligations plus a specific lensKS-simpa failure mode, and the good-leaves paragraph (README 130-146) explicitly answers the bounded-prover question by saying each child is self-contained and closes from named siblings — I confirmed this against the cited code. Known-use is real and verified (SingleRound.lean 1146-1157 reuses the transport shape with Verifier.liftContext_rbrKnowledgeSoundness and the same lens certificate). BUT avoid_when #3 is contradicted by the entry's own example: it says avoid when 'the equivalence rewrite does not hold by rfl/simp and needs a real argument', yet the example's equivalence oracleVerifier_eq_liftContext (893-928) is a 36-line induction, plainly not rfl/simp, and the move is still presented as working because that equivalence is factored into a self-contained child leaf. FIX: reword avoid_when #3 (README and entry.json) to target non-separability — the equivalence cannot be extracted into its own self-contained lemma and would have to be proved inline in the glue — instead of rfl/simp-ness. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable. check_provenance.py passes: 2 files byte-identical at pinned commit 6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6. Copied code/ files have sha256 fb9b4d4e... for SingleRound.lean (60585 B) and 9147d076... for OracleReduction.lean (22155 B), matching entry.json files[].sha256/bytes. Commit hash is identical across SOURCE.md, source.json, entry.json and every permalink; permalink line anchors (1180-1191, 893-928, 1115-1131, 583-587, 1146-1157, and OracleReduction.lean 388-408) all resolve to the named declarations. Licence recorded as Apache-2.0 in SOURCE.md, source.json, entry.json and README, and library/sources/arklib/upstream-LICENSE is the standard Apache-2.0 text, with the upstream LICENSE file listed. Minor cosmetic note: the README source table abbreviates the commit to 6f9884a95ae7 while the full hash is given in the Source-and-licence section and everywhere else; not material to traceability. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/Verified-zkEVM/ArkLib at commit `6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6`, under `Apache-2.0`; see the [source note](../../sources/arklib/SOURCE.md) for the licence text and attribution.
