# Key invariant `infinite_from P l` for the constructive Weak König's Lemma

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | rocq |
| Status | accepted |
| Source | [rocq-stdlib](../../sources/rocq-stdlib/SOURCE.md) at `22fcaa27d17b` |
| Licence | `LGPL-2.1` |

## Intent

Prove a constructive Weak König's Lemma: from `infinite_from P []` (arbitrarily
long `P`-avoiding paths above `[]`) plus a De Morgan decidability hypothesis,
exhibit a predicate `X` with `has_infinite_path P`. The single idea is the
strengthened invariant `infinite_from P l` for an arbitrary prefix `l`, which
the glue asserts and proves by induction on `l`, dispatching each case to six
named lemmas. Definitions live at the top of the file: [`is_path_from` lines
33-36](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L33-L36),
[`infinite_from` line 71](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L71),
[`has_infinite_path` lines 76-77](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L76-L77),
[`inductively_barred_at` lines 82-87](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L82-L87),
[`Y` lines 94-100](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L94-L100),
[`X` line 191](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L191);
`approx` is imported from `WeakFan` (line 25).

## The decomposition

### parent `PreWeakKonigsLemma`: [`theories/Logic/WKL.v` lines 211-235](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L211-L235) ([local copy](code/theories/Logic/WKL.v))

```coq
Theorem PreWeakKonigsLemma : forall P,
  demorgan_inductively_barred_at P -> infinite_from P [] -> has_infinite_path P.
Proof.
intros P DeMorgan Hinf.
exists (X P). intros l Hl.
assert (infinite_from P l).
{ induction l.
  - assumption.
  - destruct Hl as (Hl,Ha).
    intros n.
    pose proof (IHl Hl) as IHl'. clear IHl.
    apply Y_approx in Hl; [|assumption].
    destruct a.
    + destruct Ha as (l'&Hl'&HY'&n'&Hbar).
      rewrite (Y_unique _ DeMorgan _ _ Hl' HY' Hl) in Hbar.
      destruct (le_lt_dec n n') as [Hle|Hlt].
      * specialize (IHl' (S n')).
        apply is_path_from_restrict with n'; [assumption|].
        apply find_left_path; trivial.
      * specialize (IHl' (S n)).
        apply inductively_barred_at_monotone with (n:=n) in Hbar; [|apply Nat.lt_le_incl, Hlt].
        apply find_left_path; trivial.
    + apply inductively_barred_at_imp_is_path_from; firstorder. }
specialize (H 0). inversion H. assumption.
Qed.
```

### child `is_path_from_restrict`: [`theories/Logic/WKL.v` lines 104-117](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L104-L117) ([local copy](code/theories/Logic/WKL.v))

```coq
Lemma is_path_from_restrict : forall P n n' l, n <= n' ->
  is_path_from P n' l -> is_path_from P n l.
Proof.
intros * Hle H; induction H in n, Hle, H |- * ; intros.
- apply Nat.le_0_r in Hle as ->. apply here. assumption.
- destruct n.
  + apply here. assumption.
  + apply Nat.succ_le_mono in Hle.
    apply next_left; auto.
- destruct n.
  + apply here. assumption.
  + apply Nat.succ_le_mono in Hle.
    apply next_right; auto.
Qed.
```

### child `inductively_barred_at_monotone`: [`theories/Logic/WKL.v` lines 119-128](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L119-L128) ([local copy](code/theories/Logic/WKL.v))

```coq
Lemma inductively_barred_at_monotone : forall P l n n', n' <= n ->
  inductively_barred_at P n' l -> inductively_barred_at P n l.
Proof.
intros * Hle Hbar.
induction Hbar in n, l, Hle, Hbar |- *.
- apply now_at; auto.
- destruct n; [apply Nat.nle_succ_0 in Hle; contradiction|].
  apply Nat.succ_le_mono in Hle.
  apply propagate_at; auto.
Qed.
```

### child `inductively_barred_at_imp_is_path_from`: [`theories/Logic/WKL.v` lines 135-147](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L135-L147) ([local copy](code/theories/Logic/WKL.v))

```coq
Lemma inductively_barred_at_imp_is_path_from :
  forall P, demorgan_inductively_barred_at P -> forall n l,
  ~ inductively_barred_at P n l -> is_path_from P n l.
Proof.
intros P Hdemorgan; induction n; intros l H.
- apply here.
  intro. apply H.
  apply now_at. auto.
- assert (H0:~ (inductively_barred_at P n (true::l) /\ inductively_barred_at P n (false::l)))
  by firstorder using inductively_barred_at.
  assert (HnP:~ P l) by firstorder using inductively_barred_at.
  apply Hdemorgan in H0 as [H0|H0]; apply IHn in H0; auto using is_path_from.
Qed.
```

### context `is_path_from_imp_inductively_barred_at`: [`theories/Logic/WKL.v` lines 149-161](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L149-L161) ([local copy](code/theories/Logic/WKL.v))

```coq
Lemma is_path_from_imp_inductively_barred_at : forall P n l,
   is_path_from P n l -> inductively_barred_at P n l -> False.
Proof.
intros P; induction n; intros l H1 H2.
- inversion_clear H1. inversion_clear H2. auto.
- inversion_clear H1.
  + inversion_clear H2.
    * auto.
    * apply IHn with (true::l); auto.
  + inversion_clear H2.
    * auto.
    * apply IHn with (false::l); auto.
Qed.
```

### child `find_left_path`: [`theories/Logic/WKL.v` lines 163-169](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L163-L169) ([local copy](code/theories/Logic/WKL.v))

```coq
Lemma find_left_path : forall P l n,
  is_path_from P (S n) l -> inductively_barred_at P n (false :: l) -> is_path_from P n (true :: l).
Proof.
inversion 1; subst; intros.
- auto.
- exfalso. eauto using is_path_from_imp_inductively_barred_at.
Qed.
```

### child `Y_unique`: [`theories/Logic/WKL.v` lines 171-187](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L171-L187) ([local copy](code/theories/Logic/WKL.v))

```coq
Lemma Y_unique : forall P, demorgan_inductively_barred_at P ->
  forall l1 l2, length l1 = length l2 -> Y P l1 -> Y P l2 -> l1 = l2.
Proof.
intros * DeMorgan. induction l1, l2.
- trivial.
- discriminate.
- discriminate.
- intros [= H] (HY1,H1) (HY2,H2).
  pose proof (IHl1 l2 H HY1 HY2). clear HY1 HY2 H IHl1.
  subst l1.
  f_equal.
  destruct a, b; try reflexivity.
  + destruct H1 as (n,Hbar).
    destruct (is_path_from_imp_inductively_barred_at _ _ _ (H2 n) Hbar).
  + destruct H2 as (n,Hbar).
    destruct (is_path_from_imp_inductively_barred_at _ _ _ (H1 n) Hbar).
Qed.
```

### child `Y_approx`: [`theories/Logic/WKL.v` lines 193-207](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WKL.v#L193-L207) ([local copy](code/theories/Logic/WKL.v))

```coq
Lemma Y_approx : forall P, demorgan_inductively_barred_at P ->
  forall l, approx (X P) l -> Y P l.
Proof.
intros P DeMorgan. induction l.
- trivial.
- intros (H,Hb). split.
  + auto.
  + unfold X in Hb.
    destruct a.
    * destruct Hb as (l',(Hl',(HYl',HY))).
      rewrite <- (Y_unique P DeMorgan l' l Hl'); auto.
    * intro n. apply inductively_barred_at_imp_is_path_from.
      -- assumption.
      -- firstorder.
Qed.
```

How the parts fit. The parent's goal is `has_infinite_path P`, i.e.
`exists X, forall l, approx X l -> ~ P l`. The glue introduces the witness
`X P` and must show `~ P l` for an arbitrary `l` with `approx (X P) l`. To do
so it strengthens the hypothesis to the invariant `infinite_from P l` (that
from `l` there are arbitrarily long `P`-avoiding paths) and proves it by
induction on `l`; then `specialize (H 0); inversion H; assumption` turns the
`n = 0` instance `is_path_from P 0 l` into `~ P l` and closes the goal.

The invariant is carried by induction on the prefix `l`, and each obligation
in the step is discharged by one named lemma:

- **Base case** `l = []`: `infinite_from P []` is exactly the hypothesis
  `Hinf`, closed by `assumption` (line 218).
- **Step case** `l = a :: l0`, goal `is_path_from P n (a::l0)` for arbitrary
  `n`. The induction hypothesis applied at `l0` is `IHl' : infinite_from P l0`,
  and `Y_approx` turns `approx (X P) l0` into `Y P l0` (line 222). Then a case
  split on the next bit `a`:
  - **`a = true`** (lines 224-232): the hypothesis `Ha : X P (length l0)`
    unfolds to a same-length prefix `l'` with `Y P l'` and a bar
    `inductively_barred_at P n' (false::l')`. `Y_unique` rewrites `l'` to `l0`
    (equal length + both satisfy `Y`), re-targeting the bar to
    `inductively_barred_at P n' (false::l0)`. The bound comparison
    `le_lt_dec n n'` then chooses between two ways to shorten `IHl'` to the
    needed length: `is_path_from_restrict` (when `n <= n'`) or
    `inductively_barred_at_monotone` lifting the bar to depth `n` (when
    `n' < n`); either way `find_left_path` yields
    `is_path_from P n (true::l0)`.
  - **`a = false`** (line 233): `Ha : ~ X P (length l0)`; `firstorder` closes
    `~ inductively_barred_at P n (false::l0)` (a bar at `false::l0` would build
    `X P (length l0)`, contradicting `Ha`), and
    `inductively_barred_at_imp_is_path_from` converts that into
    `is_path_from P n (false::l0)`.

Lemma graph (which lemma uses which):

```
PreWeakKonigsLemma  (parent, 211-235)
├── Y_approx  (193-207)  ── uses Y_unique, inductively_barred_at_imp_is_path_from
├── Y_unique  (171-187)  ── uses is_path_from_imp_inductively_barred_at
├── is_path_from_restrict  (104-117)
├── find_left_path  (163-169)  ── uses is_path_from_imp_inductively_barred_at
├── inductively_barred_at_monotone  (119-128)
└── inductively_barred_at_imp_is_path_from  (135-147)

shared helper (a context site, not applied by the glue directly)
is_path_from_imp_inductively_barred_at  (149-161)  ── used by Y_unique and find_left_path
```

Each child is a good leaf because its statement is self-contained and its
proof closes on its own or from named siblings:

- `is_path_from_restrict` and `inductively_barred_at_monotone` are pure
  structural lemmas: induction on the inductive relation, then the
  constructors, closed with no other project lemma (lines 106-117, 122-128).
- `inductively_barred_at_imp_is_path_from` closes by induction on `n` using the
  constructors `here`/`now_at` and its own induction hypothesis (lines 139-146).
- `find_left_path` is two lines of glue over the no-overlap helper
  `is_path_from_imp_inductively_barred_at`: `inversion` on the path, then
  `exfalso; eauto` (lines 165-168).
- `Y_unique` closes by `f_equal` plus the same no-overlap helper in the two
  symmetric `true`/`false` cases (lines 174-187).
- `Y_approx` closes each bit by a named sibling: the `true` case by `Y_unique`,
  the `false` case by `inductively_barred_at_imp_is_path_from` (lines 196-206).

## Why it is good

1. *check* — The parent `PreWeakKonigsLemma` (lines 211-235) closes by
   asserting the invariant `infinite_from P l`, proving it by induction on
   `l`, and finishing with `specialize (H 0). inversion H. assumption.`; the
   induction step applies the six children by name: `Y_approx` (222),
   `Y_unique` (225), `is_path_from_restrict` (228), `find_left_path` (229,
   232), `inductively_barred_at_monotone` (231),
   `inductively_barred_at_imp_is_path_from` (233).
2. *measurement* — The decomposition's shape is: 6 direct lemmas, glue 25
   lines, child proof lengths `[14, 10, 13, 7, 17, 15]` lines, and a longest
   checked chain of project lemmas below the theorem of length 3
   (`PreWeakKonigsLemma -> Y_approx -> Y_unique ->
   is_path_from_imp_inductively_barred_at`).
3. *author-statement* — The authors state the idea in a comment: "The proof
   proceeds by building a set [Y] of finite paths approximating either the
   smallest unbarred infinite path in [P], if there is one (taking
   [true]>[false]), or the path true::true::... if [P] happens to be
   inductively_barred" (lines 89-92).
4. *check* — The copied file contains no `admit`, `Admitted` or `Axiom`: all
   six children and their shared helper end in `Qed`, so the constructive
   proof closes without any axiom.
5. *known-use* — The same prefix-set construction (a fixpoint `Y` with
   `Y_unique` and `Y_approx` and the witness `X`) appears at the simpler
   unindexed type in the sibling file
   [`WeakFan.v`](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/Logic/WeakFan.v#L88-L101),
   whose `WeakFanTheorem` (lines 88-101) `WKL.v` re-derives with the indexed
   relations `inductively_barred_at` / `is_path_from`.

## When to use it, and when not

Use it when the conclusion is an existential over an infinite object (a path
or stream, here represented as a predicate over finite prefixes, `has_infinite_path
P = exists X, forall l, approx X l -> ~ P l`), and the hypotheses pin one
finite instance (`infinite_from P []` here) that a restriction or monotonicity
lemma can reduce an arbitrary prefix to. The move needs a way to move between
the two dual relations (here `inductively_barred_at` and `is_path_from`): a De
Morgan / decidability hypothesis (`demorgan_inductively_barred_at P`) is what
lets `inductively_barred_at_imp_is_path_from` and the `false` case close.

Avoid it when the invariant cannot be stated as one predicate over prefixes
(so there is no single `l` to generalise over), when no decidability link
between the dual relations is available, or when the prefix set `Y` is not
unique so the re-targeting rewrite (`Y_unique`) does not apply. The move also
assumes the invariant proof splits cleanly on the next bit and a bound
comparison; if those cases need materially different arguments, the two-line
`find_left_path` dispatch will not carry them.

## Consequences

The move creates one strengthened-invariant obligation: the glue must prove
`infinite_from P l` for every `l`, not just `[]`, so the induction step splits
on the next bit `a` (true/false) and, in the `true` case, on the bound
comparison `le_lt_dec n n'` to choose between `is_path_from_restrict` (when
`n <= n'`) and `inductively_barred_at_monotone` lifting the bar to depth `n`
(when `n' < n`). Every lemma that reasons across the two dual predicates rests
on the no-overlap helper `is_path_from_imp_inductively_barred_at`. Failure
modes: without `demorgan_inductively_barred_at P`, the `false` case of
`Y_approx` and the step of `inductively_barred_at_imp_is_path_from` cannot
close; without `Y_unique`, the rewrite that re-targets the bar to the current
prefix `l0` in the `true` case does not go through. The final `~ P l` step
depends on `is_path_from P 0 l` inverting to exactly the `here` case, so the
definition of `is_path_from` at length 0 must have no `next_*` constructors.

## Survey F rule

This entry supports survey F §10 rule 6 (induction with the induction variable
and the generalised set as parameters): the glue generalises the fixed instance
`infinite_from P []` to the invariant `forall l, infinite_from P l` and proves
it by induction on `l` — the "strengthen the hypothesis" move that rule 6
names via "varying `arbitrary:`".

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-rocq-9.3.yml 'stdlib' job (nix-build bundle rocq-9.3 job stdlib) compiles the whole rocq stdlib incl. theories/Logic/WKL.v, on push to master (default branch); pinned commit 22fcaa27d17bc28ab4be728ed10a1fb73afb23ee is on master (API compare master...22fcaa27 = identical) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 22fcaa27d17bc28ab4be728ed10a1fb73afb23ee | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | byte-identical local copy (check_provenance pass) of theories/Logic/WKL.v: parent 211-235, assert (infinite_from P l) at 216, induction l at 217, Y_approx 222, Y_unique 225, is_path_from_restrict 228, find_left_path 229 & 232, inductively_barred_at_monotone 231, inductively_barred_at_imp_is_path_from 233, specialize (H 0). inversion H. assumption. 234 | verifier |
| 2 | verified | local copy: parent 211-235 = 25 lines; child sites 104-117/119-128/135-147/163-169/171-187/193-207 = [14,10,13,7,17,15] lines; 6 direct children; chain PreWeakKonigsLemma(222 apply Y_approx)->Y_approx(200 rewrite Y_unique)->Y_unique(181,184 is_path_from_imp_inductively_barred_at), 3 edges, no longer chain exists | verifier |
| 3 | verified | local copy lines 89-92 contain the quoted comment verbatim: 'The proof proceeds by building a set [Y] ... true::true::... if [P] happens to be inductively_barred' | verifier |
| 4 | verified | grep -E 'admit|Admitted|Axiom' over local copy: no matches; Qed present at 117,128,147,161,169,187,207,235 (6 children + helper + parent) | verifier |
| 5 | verified | fetched WeakFan.v at 22fcaa27: WeakFanTheorem 88-101, Fixpoint Y at 49, Y_unique 57-69, Y_approx 75-86, Definition X at 73; same unindexed Y/Y_unique/Y_approx/X pattern as WKL.v | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Opened code/theories/Logic/WKL.v (copied, 273 lines). Parent statement and all six child statements match entry.json verbatim (PreWeakKonigsLemma L211-235; is_path_from_restrict L104-117; inductively_barred_at_monotone L119-128; inductively_barred_at_imp_is_path_from L135-147; find_left_path L163-169; Y_unique L171-187; Y_approx L193-207). Glue (L216-233) asserts infinite_from P l, proves by induction on l, closes with 'specialize (H 0). inversion H. assumption.' (L234); it applies exactly the six named children by name (Y_approx L222, Y_unique L225, is_path_from_restrict L228, find_left_path L229+L232, inductively_barred_at_monotone L231, inductively_barred_at_imp_is_path_from L233); the helper is_path_from_imp_inductively_barred_at (L149-161) is NOT applied by the glue directly, matching its 'context' role. Each child's closed_by matches its proof (induction/inversion/f_equal steps as stated). All proofs end in Qed; no admit/Admitted/Axiom in the file. Shape numbers correct: direct_lemmas 6; glue_lines 25 (L211-235); child_lines [14,10,13,7,17,15] = site ranges 104-117,119-128,135-147,163-169,171-187,193-207 in the children-array order; depth 3 = PreWeakKonigsLemma -> Y_approx (uses Y_unique L203) -> Y_unique (uses is_path_from_imp_inductively_barred_at L184,L186). | reviewer-correctness |
| generality | accept | Move is stated generally: the glue is characterised as strengthening the fixed instance infinite_from P [] to the invariant forall l, infinite_from P l and inducting on l, and use_when is abstracted to an existential over an infinite object over finite prefixes with one pinned finite instance reducible by a restriction/monotonicity lemma plus a decidability link between dual relations; it maps to Survey F rule 6 and cites the sibling WeakFan.v as known-use, so it does not stay tied to the example. When-not-to-use and consequences are honest and specific: they name the exact failure modes tied to named lemmas (no demorgan_inductively_barred_at closes the false case of Y_approx and the step of inductively_barred_at_imp_is_path_from; no Y_unique breaks the re-targeting rewrite; a non-unique prefix set Y). It explicitly says what makes children good leaves: self-contained statements, each closes on its own or from named siblings, with two purely structural lemmas and a two-line find_left_path over a shared no-overlap helper. | reviewer-generality |
| provenance-licence | accept | Permalink, commit, licence and source note are all consistent and traceable. check_provenance.py reports the single copied file theories/Logic/WKL.v is byte-identical at commit 22fcaa27d17bc28ab4be728ed10a1fb73afb23ee. Raw view of LICENSE at that commit is LGPL-2.1 (matches entry.json licence, SOURCE.md, source.json and the copied upstream-LICENSE); the WKL.v header itself states 'GNU Lesser General Public License Version 2.1'. All site permalinks point at the pinned commit and the correct path. source.json and SOURCE.md agree on url, commit, licence and licence_files. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-prover/stdlib at commit `22fcaa27d17bc28ab4be728ed10a1fb73afb23ee`, under `LGPL-2.1`; see the [source note](../../sources/rocq-stdlib/SOURCE.md) for the licence text and attribution.
