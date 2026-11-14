# Well-founded accessibility R as the key invariant for constructive indefinite ground description over nat

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | rocq |
| Status | accepted |
| Source | [rocq-stdlib](../../sources/rocq-stdlib/SOURCE.md) at `22fcaa27d17b` |
| Licence | `LGPL-2.1-only` |
| Licence recorded | 2026-11-14T22:40:52Z |

## Intent

Reduce the constructive description `(exists n : nat, P n) -> {n : nat | P n}` to
the accessibility of `0` for the relation `R` (`x = S y /\ ~ P y`): the key
invariant that turns "P holds somewhere" into "the linear search from 0
terminates". The parent glues the two directions of that equivalence —
existence → `acc 0`, and `acc 0` → witness — into one `Defined` proof.

## The decomposition

### parent `constructive_indefinite_ground_description_nat_Acc`: [`theories/Logic/ConstructiveEpsilon.v` lines 362-367](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/ConstructiveEpsilon.v#L362-L367) ([local copy](code/theories/Logic/ConstructiveEpsilon.v))

```coq
Theorem constructive_indefinite_ground_description_nat_Acc :
  (exists n : nat, P n) -> {n : nat | P n}.
Proof.
intros H; apply acc_implies_P_eventually.
apply P_eventually_implies_acc_ex; assumption.
Defined.
```

### child `P_eventually_implies_acc_ex`: [`theories/Logic/ConstructiveEpsilon.v` lines 340-344](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/ConstructiveEpsilon.v#L340-L344) ([local copy](code/theories/Logic/ConstructiveEpsilon.v))

```coq
Corollary P_eventually_implies_acc_ex : (exists n : nat, P n) -> acc 0.
Proof.
intros H; elim H. intros x Px. apply P_eventually_implies_acc with (n := x).
replace (x + 0) with x; auto.
Defined.
```

### child `acc_implies_P_eventually`: [`theories/Logic/ConstructiveEpsilon.v` lines 349-360](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/ConstructiveEpsilon.v#L349-L360) ([local copy](code/theories/Logic/ConstructiveEpsilon.v))

```coq
Theorem acc_implies_P_eventually : acc 0 -> {n : nat | P n}.
Proof.
intros Acc_0. pattern 0. apply Fix_F with (R := R); [| assumption].
clear Acc_0; intros x IH.
destruct (P_decidable x) as [Px | not_Px].
- exists x; simpl; assumption.
- set (y := S x).
  assert (Ryx : R y x).
  + unfold R; split; auto.
  + destruct (IH y Ryx) as [n Hn].
    exists n; assumption.
Defined.
```

### context `R`: [`theories/Logic/ConstructiveEpsilon.v` lines 315-323](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/ConstructiveEpsilon.v#L315-L323) ([local copy](code/theories/Logic/ConstructiveEpsilon.v))

```coq
The relation [R] describes the connection between the two successive
numbers we try. Namely, [y] is [R]-less then [x] if we try [y] after
[x], i.e., [y = S x] and [P x] is false. Then the absence of an
infinite [R]-descending chain from 0 is equivalent to the termination
of our searching algorithm. *)

Let R (x y : nat) : Prop := x = S y /\ ~ P y.

#[local] Abbreviation acc x := (Acc R x).
```

How the parts fit. The key invariant is the relation `R` (line 321), with
`acc x` abbreviating `Acc R x` (line 323): `Acc R x` holds exactly when there is
no infinite `R`-descending chain from `x`, i.e. when the linear search that
tries `P` on `x, S x, S (S x), …` eventually stops. The parent is the two-line
glue that routes the goal through `acc 0`:

```
constructive_indefinite_ground_description_nat_Acc   (parent, 362-367)
├── acc_implies_P_eventually        (child, 349-360)   cited at 365
│       └── Fix_F (library, Coq.Init.Wf) + P_decidable; no project lemma
└── P_eventually_implies_acc_ex     (child, 340-344)   cited at 366
        └── P_eventually_implies_acc  (331-338)
                └── P_implies_acc       (325-329)
```

Each child is one direction of the equivalence "existence ⟺ `acc 0`", and each
is a good leaf:

- `acc_implies_P_eventually` (349-360) is self-contained: it closes on its own
  using `Fix_F` (well-founded recursion over `Acc R`, a library lemma) and the
  decidability hypothesis `P_decidable`; it is the only place decidability is
  used.
- `P_eventually_implies_acc_ex` (340-344) closes by applying its sibling
  `P_eventually_implies_acc` at `n := x` plus the rewrite `x + 0 = x`. The two
  lemmas it rests on are not direct children of the parent — they are the
  support chain below it, each a one-step argument:
  [`P_eventually_implies_acc` (331-338)](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/ConstructiveEpsilon.v#L331-L338)
  is an induction on `n`, and
  [`P_implies_acc` (325-329)](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/ConstructiveEpsilon.v#L325-L329)
  is the base case (one `constructor`). The longest chain below the parent is
  parent → `P_eventually_implies_acc_ex` → `P_eventually_implies_acc` →
  `P_implies_acc`, depth 3.

## Why it is good

1. The parent's proof cites `acc_implies_P_eventually` (check; line 365).
2. The parent's proof cites `P_eventually_implies_acc_ex` (check; line 366).
3. The Acc section of the copied file (lines 301-369) has no closing-by-sorry
   token (check; the whole section closes with `Defined`/`Qed`).
4. The parent site is 6 lines long: two `apply`s and a `Defined`, so all the
   content is in the two children (check; the glue is the measurement recorded
   in `shape`).
5. The authors state the key invariant in the file's own comment: "the absence
   of an infinite [R]-descending chain from 0 is equivalent to the termination
   of our searching algorithm" (author-statement; lines 315-319).

In my opinion the detail worth copying is the choice of the invariant itself:
`R` is the "step to the next number tried" relation, so that `Acc R 0` *is*
termination of the search, and the two directions of the description theorem
become two almost-obvious lemmas.

## When to use it, and when not

Use it when a goal `(exists x : A, P x) -> {x : A | P x}` cannot be opened by
eliminating the `Prop` existential directly (the goal is in `Type`), the domain
supports a linear search (a decidable `P` over `nat` or a countable domain), and
the search's termination can be certified by a well-founded relation that you
state once as a key invariant and prove in both directions.

Avoid it when you want a directly executable linear-search program and accept
the longer, more ad-hoc direct development: the same file's "Direct version"
section (lines 110-295) programs the search explicitly (`prog_linear_search`,
lines 142-147) over the ad-hoc inductive predicate `before_witness` instead of
`Acc`, and is far longer than the `Acc` section (lines 301-369). Also avoid it
when `P` is not decidable, or when you need only the `Prop`-level existence and
not the computational witness `{x : A | P x}`.

## Consequences

The move splits the goal into the two directions of an equivalence through the
key invariant `acc 0`, each a lemma that must close on its own; a broken
direction shows up as a leaf that does not close, not as a parent that does not
glue. The `acc 0 -> witness` direction is the only place decidability of `P` is
used (`Fix_F` branches on `P_decidable`). The whole argument rests on `R` being
well-founded: here `R` is "step to the successor when `P` fails", so `Acc R x`
holds exactly when `P` holds somewhere at or after `x`; if `R` were not
well-founded the accessibility hypothesis would be unprovable.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-rocq-9.2.yml (Nix CI for bundle rocq-9.2): on push to master (default branch), the 'stdlib' job runs 'nix-build --argstr bundle rocq-9.2 --argstr job stdlib', which builds theories/Logic/ConstructiveEpsilon.v; workflow present at pinned commit 22fcaa27d17bc28ab4be728ed10a1fb73afb23ee | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: P_eventually_implies_acc_ex@theories/Logic/ConstructiveEpsilon.v:366, acc_implies_P_eventually@theories/Logic/ConstructiveEpsilon.v:365; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 22fcaa27d17bc28ab4be728ed10a1fb73afb23ee | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, acc_implies_P_eventually) -> cites: acc_implies_P_eventually occurs at theories/Logic/ConstructiveEpsilon.v:365 | check_claims.py |
| 2 | verified | cites(parent, P_eventually_implies_acc_ex) -> cites: P_eventually_implies_acc_ex occurs at theories/Logic/ConstructiveEpsilon.v:366 | check_claims.py |
| 3 | verified | no_sorry(theories/Logic/ConstructiveEpsilon.v, 301-369) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/Logic/ConstructiveEpsilon.v:301-369 | check_claims.py |
| 4 | verified | lines(parent, 6) -> lines: site parent has 6 lines | check_claims.py |
| 5 | verified | Read lines 315-319 of the copied file: the comment block states 'Then the absence of an infinite [R]-descending chain from 0 is equivalent to the termination of our searching algorithm.', tying the R-descending chain to search termination as the claim says | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against code/theories/Logic/ConstructiveEpsilon.v: parent constructive_indefinite_ground_description_nat_Acc (362-367) is 6 lines, glues exactly two children — apply acc_implies_P_eventually at 365 then apply P_eventually_implies_acc_ex;assumption at 366 — matching the entry's decomposition (existence -> acc 0 -> witness). Child statements verbatim (340, 349); closed_by fields match code (P_eventually_implies_acc_ex: apply P_eventually_implies_acc with (n:=x); replace (x+0) with x; auto; acc_implies_P_eventually: Fix_F R + destruct P_decidable x, ~P x branch via IH y Ryx). Section closes with Defined./Qed., no sorry/admit/Admitted/axiom in 301-369. Children are exactly the two lemmas the parent cites, no others. Shape numbers right: direct_lemmas=2, glue_lines=6 (362-367), child_lines=[5,12] (340-344, 349-360), depth=3 via P_eventually_implies_acc_ex -> P_eventually_implies_acc(331-338) -> P_implies_acc(325-329). | reviewer-correctness |
| generality | accept | Move is stated generally: goal_shape is (exists x:A, P x) -> {x:A | P x} over a decidable P on a natural-indexed/countable domain, with the invariant as a well-founded relation (acc 0 = Acc R 0) proved in two directions; also_known_as lists termination certificate / well-founded ranking / accessibility argument. 'When not to use' is now honest and specific: it drops the unsupported 'shorter alternative' and author attribution, and instead says avoid the longer, more ad-hoc direct development (Direct version section 109-295 vs Acc section 301-369, ~186 vs ~68 lines, confirmed against the copied file: before_witness/O_witness/inv_before_witness/prog_linear_search/rel_ls live at 120-146+ vs 4 short Acc lemmas at 325-360), or when P is not decidable / only Prop-level existence is needed. Consequences are honest and specific: only acc_implies_P_eventually (349-360) branches on P_decidable (line 353), matching the author comment at 346-347 'This is also where decidability of [P] is used'; the well-foundedness requirement is stated (R = step-to-successor-when-P-fails, so Acc R x iff P holds at/after x). 'How the parts fit' names what makes the lemmas good leaves for a bounded prover: self-contained (closes via Fix_F), one-step, only place decidability is used, parent glue is two applys + Defined, depth 3. Objection resolved. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent. check_provenance.py reports the copied file byte-identical at pinned commit 22fcaa27d17bc28ab4be728ed10a1fb73afb23ee; local sha256 11cd2ef3...6aeab9 and 18080 bytes match entry.json. All permalinks use that commit and theories/Logic/ConstructiveEpsilon.v; cited line ranges verified against the copied file (R=315-323 with Let R at 321, acc at 323; P_implies_acc=325-329; P_eventually_implies_acc=331-338; P_eventually_implies_acc_ex=340-344; acc_implies_P_eventually=349-360; parent=362-367, 6 lines). Licence LGPL-2.1 consistent across entry.json, README, source.json, SOURCE.md; sources/rocq-stdlib/upstream-LICENSE is the LGPL-2.1 text. Source note records repo, pinned commit, language, licence and attribution; relative links resolve. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-prover/stdlib at commit `22fcaa27d17bc28ab4be728ed10a1fb73afb23ee`, under `LGPL-2.1-only`; see the [source note](../../sources/rocq-stdlib/SOURCE.md) for the licence text and attribution.
