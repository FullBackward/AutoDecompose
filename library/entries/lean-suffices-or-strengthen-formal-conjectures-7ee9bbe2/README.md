# Strengthen dist_eq_computable to a BFS fuel invariant

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | accepted |
| Source | [formal-conjectures](../../sources/formal-conjectures/SOURCE.md) at `a425ca3eb797` |
| Licence | `Apache-2.0` |

## Intent

The theorem identifies the abstract graph distance `G.dist u v` with the
executable breadth-first-search distance `computable_dist G u v`. Instead of
attacking the equality directly, the proof strengthens the goal with a
`suffices` to an invariant of the BFS accumulator `bfs_dist_aux` (for
arbitrary fuel, depth and reached set), instantiates it at the starting
values, and proves the invariant by induction on fuel, closing the two
interesting cases with the two private BFS lemmas below.

## The decomposition

### parent `dist_eq_computable`: [`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean` lines 302-358](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean#L302-L358) ([local copy](code/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean))

```lean
theorem dist_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] (u v : α) :
    G.dist u v = computable_dist G u v := by
  unfold computable_dist
  split_ifs with h
  · subst h; simp [dist_self]
  · symm
    suffices hsuff : ∀ (fuel depth : ℕ) (reached : Finset α),
        (∀ w, w ∈ reached ↔ w ∈ G.bfsStep^[depth] {u}) →
        (∀ d, d < depth → v ∉ G.bfsStep^[d] {u}) →
        fuel + depth ≥ Fintype.card α + 1 →
        G.bfs_dist_aux v fuel depth reached = G.dist u v by
      exact hsuff (Fintype.card α) 1 (G.bfsStep {u})
        (fun w => by simp)
        (fun d hd => by
          have := Nat.lt_of_lt_of_le hd (Nat.le_refl 1)
          interval_cases d; simp [Finset.mem_singleton]; exact Ne.symm h)
        (by omega)
    intro fuel
    induction fuel with
    | zero =>
      intro depth reached h_inv h_not_found h_fuel
      simp [bfs_dist_aux]
      symm; rw [dist_eq_zero_iff_eq_or_not_reachable]
      right; intro hr
      have hpos := hr.pos_dist_of_ne h
      obtain ⟨p, hp_path, hp_len⟩ := hr.exists_path_of_dist
      have : G.dist u v < depth := by
        calc G.dist u v = p.length := hp_len.symm
          _ < Fintype.card α := hp_path.length_lt
          _ < depth := by omega
      exact h_not_found (G.dist u v) this
        (dist_le_mem_iterate_bfsStep G u v _ (le_refl _) (Or.inr hr))
    | succ fuel ih =>
      intro depth reached h_inv h_not_found h_fuel
      simp only [bfs_dist_aux]
      split_ifs with hv
      · -- v ∈ reached = iterate^depth {u}. Show depth = dist u v.
        have hle := mem_iterate_bfsStep_dist_le G u v depth ((h_inv v).mp hv)
        -- dist u v ≥ depth: if dist < depth, v ∈ iterate^(dist u v), contradicts h_not_found
        by_contra hne
        have hlt : G.dist u v < depth := by omega
        have hreach : G.Reachable u v := G.reachable_of_mem_iterate_bfsStep ((h_inv v).mp hv)
        exact h_not_found (G.dist u v) hlt
          (dist_le_mem_iterate_bfsStep G u v _ le_rfl (Or.inr hreach))
      · -- v ∉ reached. Recurse.
        have h_inv' : ∀ w, w ∈ G.bfsStep reached ↔
            w ∈ G.bfsStep^[depth + 1] {u} := by
          intro w
          have heq : G.bfsStep reached = G.bfsStep (G.bfsStep^[depth] {u}) := by
            ext x; simp only [mem_bfsStep, h_inv]
          rw [heq, Function.iterate_succ', Function.comp]
        exact ih (depth + 1) (G.bfsStep reached) h_inv'
          (fun d hd => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
            · exact h_not_found d (by omega)
            · subst hd; rwa [h_inv] at hv)
          (by omega)
```

### child `mem_iterate_bfsStep_dist_le`: [`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean` lines 250-273](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean#L250-L273) ([local copy](code/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean))

```lean
private lemma mem_iterate_bfsStep_dist_le (G : SimpleGraph α) [DecidableRel G.Adj]
    (u w : α) (n : ℕ) (hw : w ∈ G.bfsStep^[n] {u}) : G.dist u w ≤ n := by
  induction n generalizing w with
  | zero => simp at hw; subst hw; simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp] at hw
    simp only [mem_bfsStep] at hw
    rcases hw with hw | ⟨a, ha_mem, hadj⟩
    · exact Nat.le_succ_of_le (ih w hw)
    · by_cases ha : a = u
      · subst ha
        exact le_trans (dist_le (.cons hadj .nil))
          (by simp [Walk.length_cons])
      · by_cases hd : G.dist u a = 0
        · rw [dist_eq_zero_iff_eq_or_not_reachable] at hd
          rcases hd with rfl | hd
          · exact absurd rfl ha
          · have : ¬G.Reachable u w := fun hr =>
              hd (hr.elim (fun p => (p.append (.cons hadj.symm .nil)).reachable))
            rw [dist_eq_zero_of_not_reachable this]; omega
        · obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero hd
          have ha_dist := ih a ha_mem
          exact le_trans (dist_le (p.append (.cons hadj .nil)))
            (by simp [Walk.length_append, Walk.length_cons, Walk.length_nil, hp]; omega)
```

### child `dist_le_mem_iterate_bfsStep`: [`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean` lines 275-300](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean#L275-L300) ([local copy](code/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean))

```lean
private lemma dist_le_mem_iterate_bfsStep (G : SimpleGraph α) [DecidableRel G.Adj]
    (u w : α) (n : ℕ) (hdist : G.dist u w ≤ n) (hreach : w = u ∨ G.Reachable u w) :
    w ∈ G.bfsStep^[n] {u} := by
  induction n generalizing w with
  | zero =>
    rcases hreach with rfl | hr
    · exact Finset.mem_singleton_self _
    · have h0 := Nat.le_zero.mp hdist
      rw [dist_eq_zero_iff_eq_or_not_reachable] at h0
      rcases h0 with h0 | h0
      · subst h0; exact Finset.mem_singleton_self _
      · exact absurd hr h0
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp]
    simp only [mem_bfsStep]
    by_cases hle : G.dist u w ≤ n
    · left; exact ih w hle hreach
    · right
      have hdist_eq : G.dist u w = n + 1 := by omega
      obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero (by omega : G.dist u w ≠ 0)
      have hlen : p.length = n + 1 := by omega
      refine ⟨p.getVert n, ?_, ?_⟩
      · exact ih _ (le_trans (dist_le (p.take n))
          (by rw [Walk.take_length]; omega)) (Or.inr (p.take n).reachable)
      · have := p.adj_getVert_succ (show n < p.length from by omega)
        rwa [show n + 1 = p.length from by omega, p.getVert_length] at this
```

How the parts fit. The parent unfolds `computable_dist` and splits on `u = v`.
In the `u ≠ v` branch it does not prove the equality directly: it `suffices` a
stronger statement `hsuff`, an invariant of the BFS accumulator,

```lean
    suffices hsuff : ∀ (fuel depth : ℕ) (reached : Finset α),
        (∀ w, w ∈ reached ↔ w ∈ G.bfsStep^[depth] {u}) →
        (∀ d, d < depth → v ∉ G.bfsStep^[d] {u}) →
        fuel + depth ≥ Fintype.card α + 1 →
        G.bfs_dist_aux v fuel depth reached = G.dist u v by
```

and instantiates it at `(fuel, depth, reached) = (Fintype.card α, 1, bfsStep {u})`.
The first premise holds by `simp` (`bfsStep {u}` is the depth-1 iterate), the
second by `interval_cases d` together with `v ≠ u`, the third by `omega`. The
remaining obligation is the induction on `fuel`:

- **zero case** — `bfs_dist_aux v 0 depth reached = 0`. The right side
  `G.dist u v` is shown to be `0` by `dist_eq_zero_iff_eq_or_not_reachable`:
  if `v` were reachable, a shortest path would give `G.dist u v < depth` (its
  length is `< Fintype.card α < depth`), and then
  `dist_le_mem_iterate_bfsStep` puts `v ∈ bfsStep^[dist u v] {u}`, contradicting
  `h_not_found`.
- **successor case** — `split_ifs` on `v ∈ reached`:
  - `v ∈ reached`: `mem_iterate_bfsStep_dist_le` gives `dist u v ≤ depth`; the
    reverse `depth ≤ dist u v` follows because `dist u v < depth` would place
    `v ∈ bfsStep^[dist u v] {u}` via `dist_le_mem_iterate_bfsStep` (after
    `reachable_of_mem_iterate_bfsStep`), contradicting `h_not_found`; hence
    `depth = dist u v`.
  - `v ∉ reached`: re-establish the invariant for `(depth + 1, bfsStep reached)`
    — the rewrite `bfsStep reached = bfsStep (bfsStep^[depth] {u})` uses `h_inv`
    and `mem_bfsStep` — and call the induction hypothesis `ih`.

The lemma graph (in text):

```
dist_eq_computable ──uses── mem_iterate_bfsStep_dist_le   (line 339)
        │
        └───────────uses── dist_le_mem_iterate_bfsStep    (lines 333, 345)

mem_iterate_bfsStep_dist_le ──uses── mem_bfsStep, dist_le, exists_walk_of_dist_ne_zero, …
dist_le_mem_iterate_bfsStep ──uses── mem_bfsStep, dist_le, exists_walk_of_dist_ne_zero, …
```

`mem_bfsStep` (and `bfsStep` itself) are defined in the sibling file
[`Connectivity.lean`](code/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Connectivity.lean)
(lines 106-109); the distance lemmas (`dist_le`, `dist_eq_zero_iff_eq_or_not_reachable`,
`exists_walk_of_dist_ne_zero`) are Mathlib's graph API. The glue also calls
`reachable_of_mem_iterate_bfsStep` (Connectivity.lean line 138) to turn the
`v ∈ reached` fact into `G.Reachable u v`.

Each child is a good leaf. `mem_iterate_bfsStep_dist_le` is a self-contained
statement — `w ∈ G.bfsStep^[n] {u} → G.dist u w ≤ n` — closed by a single
induction on `n` with no use of the other child, each branch a computation on
walks. `dist_le_mem_iterate_bfsStep` is its converse —
`G.dist u w ≤ n → w ∈ G.bfsStep^[n] {u}` (given `w` is `u` or reachable) —
also closed by induction on `n` on its own, using the same Mathlib API plus
`mem_bfsStep`. Together they are the exact two directions of
`w ∈ G.bfsStep^[n] {u} ↔ G.dist u w ≤ n`, which is precisely what the glue
needs to close both the zero case and the `v ∈ reached` case.

## Why it is good

1. `dist_eq_computable` is a real declaration spanning lines 302-358 of
   `VertexDistance.lean` (`check`; [permalink](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean#L302-L358)).
2. The glue cites `mem_iterate_bfsStep_dist_le` at line 339 (`check`;
   [permalink](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean#L302-L358)).
3. The glue cites `dist_le_mem_iterate_bfsStep` at lines 333 and 345 (`check`;
   [permalink](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean#L302-L358)).
4. The whole file `VertexDistance.lean` contains no `sorry`, `admit`,
   `Admitted` or `axiom` (`check` over lines 1-429;
   [permalink](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean)).
5. The `shape` is a measurement: `glue_lines = 57` (lines 302-358) and
   `child_lines = [24, 26]` (lines 250-273 and 275-300), so the 57-line glue
   delegates both directions of the distance bound to 50 lines of child proof
   (`measurement`; [permalink](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean)).

Downstream value (not a claim): `dist_eq_computable` is reused by the later
theorems `distMin_eq_computableDistMin` (lines 371, 373) and
`avg_dist_eq_computable` (line 386), which is why it is worth proving once at
this boundary.

In my opinion the detail worth copying is that the two children are stated as
the *exact two directions* of the correspondence `w ∈ bfsStep^[n] {u} ↔
dist u w ≤ n`, so the parent's `suffices` invariant and its two hard cases
consume them directly, with nothing left over and no extra glue.

## When to use it, and when not

Use it when a goal relates two presentations of the same quantity — here an
abstract shortest-walk distance `G.dist` and an executable recursive loop
`computable_dist` / `bfs_dist_aux` carrying a fuel counter, a depth counter and
an accumulated `reached` set — and the direct equality needs an induction whose
hypothesis must be generalised over the accumulator. State the strengthened
invariant first with `suffices`, instantiate it at the concrete starting
values, and run the induction inside the suffices block.

Avoid it when the strengthened invariant cannot be stated cleanly, when the
induction needs no generalisation so strengthening buys nothing, or when the
strengthened statement does not specialise back to the original goal — a
`suffices` that is not actually stronger than the goal is a false child.

## Consequences

The move creates one obligation (the strengthened invariant `hsuff`) from the
original equality, plus two side conditions when instantiating it at depth 1:
that `bfsStep {u}` is the depth-1 iterate (closed by `simp`) and that `v` is
not seen at depth 0 (closed because `v ≠ u`, from the `split_ifs` branch). The
strengthened statement is quantified over arbitrary fuel/depth/reached, so its
proof is an induction on fuel that must carry the invariant `h_inv` and the
`h_not_found` side condition through each step.

Failure mode: the invariant must be exactly right. If `h_inv` did not tie
`reached` to `bfsStep^[depth] {u}`, the recurse branch could not rewrite
`bfsStep reached` to `bfsStep^[depth + 1] {u}` to re-establish the induction
hypothesis; and the two children must be the exact two directions of
`w ∈ bfsStep^[n] {u}` iff `dist u w ≤ n`, or the zero case and the
`v ∈ reached` case cannot close.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build-and-docs.yml (build job, 'lake --wfail build FormalConjecturesForMathlib FormalConjecturesUtil'); VertexDistance.lean is under FormalConjecturesForMathlib; pinned commit a425ca3eb797fe927cb88c950565fdcbbbbada70 is on default branch main (compare main...a425ca3 = behind 4, ahead 0) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: mem_iterate_bfsStep_dist_le@FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean:339, dist_le_mem_iterate_bfsStep@FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean:333; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at a425ca3eb797fe927cb88c950565fdcbbbbada70 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(dist_eq_computable, FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean, 302-358) -> declared: dist_eq_computable is declared at FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean:302 | check_claims.py |
| 2 | verified | cites(parent, mem_iterate_bfsStep_dist_le) -> cites: mem_iterate_bfsStep_dist_le occurs at FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean:339 | check_claims.py |
| 3 | verified | cites(parent, dist_le_mem_iterate_bfsStep) -> cites: dist_le_mem_iterate_bfsStep occurs at FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean:333 | check_claims.py |
| 4 | verified | no_sorry(FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean, 1-429) -> no_sorry: none of sorry, admit, axiom in FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean:1-429 | check_claims.py |
| 5 | verified | read code/.../VertexDistance.lean: mem_iterate_bfsStep_dist_le spans 250-273 (24), dist_le_mem_iterate_bfsStep spans 275-300 (26), dist_eq_computable spans 302-358 (57); 24+26=50; glue cites both children at lines 339 and 333/345 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent dist_eq_computable (VertexDistance.lean 302-358) strengthens the goal via suffices hsuff (line 308) and instantiates it at (Fintype.card a, 1, bfsStep {u}); matches the suffices-or-strengthen move. The two children are exactly the local lemmas the proof uses: mem_iterate_bfsStep_dist_le (250-273) cited at line 339, dist_le_mem_iterate_bfsStep (275-300) cited at lines 333 and 345; no other local lemma is cited (reachable_of_mem_iterate_bfsStep is a sibling-file API lemma at Connectivity.lean:138, acknowledged in the README). closed_by matches the code branch for branch. The proof closes: induction on fuel closes zero and succ; the succ reached branch derives depth = dist via both children; the recurse branch re-establishes the invariant via h_inv and calls ih. Shape numbers correct: glue 302-358 = 57, child_lines [24,26] = 250-273 and 275-300, sum 50, direct_lemmas 2, depth 1. | reviewer-correctness |
| generality | accept | Move generalised beyond the example ('two presentations of the same quantity' + induction hypothesis generalised over the accumulator; also_known_as: strengthen-the-goal/generalise-before-induction). When-not-to-use has three concrete conditions and consequences name a real failure mode (h_inv must tie reached to bfsStep^[depth]{u} or the recurse rewrite fails; children must be the exact two directions), all matching the copied code. 'Each child is a good leaf' states what makes the leaves bounded: self-contained statement, closed by a single induction, no use of the other child (confirmed in code), exactly the two directions the glue needs. Minor nit, non-blocking: entry.json avoid_when 'not actually implied by (stronger than) the goal' reverses the implication direction, but README states it correctly. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable. check_provenance passes: 2 files byte-identical at pinned commit a425ca3eb797fe927cb88c950565fdcbbbbada70. Commit hash matches across source.json, SOURCE.md, entry.json source.commit and README (a425ca3eb797). Licence Apache-2.0 recorded identically in source.json, SOURCE.md, entry.json source.licence, README table and Source-and-licence section, and upstream-LICENSE is the Apache License 2.0. All permalinks pin the same commit with line ranges matching the entry's sites (302-358, 250-273, 275-300); VertexDistance.lean is 429 lines matching claim 4's 1-429, Connectivity.lean 208 lines covering cited lines 106-109 and 138. SOURCE.md carries correct repo, commit, licence and attribution. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/google-deepmind/formal-conjectures at commit `a425ca3eb797fe927cb88c950565fdcbbbbada70`, under `Apache-2.0`; see the [source note](../../sources/formal-conjectures/SOURCE.md) for the licence text and attribution.
