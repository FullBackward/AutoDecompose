# Iff-split of IMO 1964 P1(a): n % 3 = 0 iff 2^n = 1 (mod 7)

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | lean |
| Status | accepted |
| Source | [compfiles](../../sources/compfiles/SOURCE.md) at `1745e6ced3e6` |
| Licence | `Apache-2.0` |

## Intent

Split the iff `n ∈ solution_set ↔ 2^n ≡ 1 [MOD 7]` into its two directions
with `constructor`. The forward direction builds the congruence from a
divisibility witness of `n % 3 = 0`; the reverse direction refutes the
non-zero residues of `n % 3` with a further case split.

## The decomposition

### parent `imo1964_p1a`: [`Compfiles/Imo1964P1.lean` lines 32-47](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1964P1.lean#L32-L47) ([local copy](code/Compfiles/Imo1964P1.lean))

```lean
problem imo1964_p1a (n : ℕ) : n ∈ solution_set ↔ 2^n ≡ 1 [MOD 7] := by
  constructor
  · intro hn
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hn
    change 2^n % 7 = 1
    rw [hm, Nat.pow_mul, Nat.pow_mod]
    norm_num
  · intro hn
    change n % 3 = 0
    change 2^n % 7 = 1 at hn
    rw [(Nat.div_add_mod' n 3).symm] at hn
    rw [pow_add, pow_mul', Nat.mul_mod, Nat.pow_mod] at hn
    mod_cases H : n % 3
    · exact H
    · rw [H] at hn; norm_num at hn
    · rw [H] at hn; norm_num at hn
```

### context `solution_set`: [`Compfiles/Imo1964P1.lean` lines 30-30](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1964P1.lean#L30-L30) ([local copy](code/Compfiles/Imo1964P1.lean))

```lean
determine solution_set : Set ℕ := { n | n % 3 = 0 }
```

How the parts fit. `constructor` (line 33) on the `↔` goal produces exactly two
children: the forward implication `n ∈ solution_set → 2^n ≡ 1 [MOD 7]` and the
reverse `2^n ≡ 1 [MOD 7] → n ∈ solution_set`. Because `solution_set` is defined
as `{ n | n % 3 = 0 }` (line 30), membership unfolds to `n % 3 = 0`, and the
`≡ … [MOD …]` notation unfolds to an equation of remainders (the proof writes it
as `2^n % 7 = 1`, lines 36 and 41).

The forward child (lines 34-38) is a construction: `Nat.dvd_of_mod_eq_zero hn`
turns the hypothesis `n % 3 = 0` into the divisibility `3 ∣ n`, and
`obtain ⟨m, hm⟩` names the witness with `hm : n = 3 * m`. Rewriting `n` along
`hm` and then `Nat.pow_mul`/`Nat.pow_mod` reduces the goal to `(2 ^ 3) ^ m % 7`,
which `norm_num` closes since `2 ^ 3 % 7 = 1`.

The reverse child (lines 39-47) is a refutation by cases. After `change n % 3 = 0`
and `change 2^n % 7 = 1 at hn`, the hypothesis is rewritten with
`(Nat.div_add_mod' n 3).symm` (so `n` becomes `n / 3 * 3 + n % 3`) and then
`pow_add`, `pow_mul'`, `Nat.mul_mod`, `Nat.pow_mod`, leaving a statement about
`2 ^ (n % 3) % 7`. `mod_cases H : n % 3` splits into the three residues: residue
0 is exactly the goal, closed by `exact H`; residues 1 and 2 are closed by
`rw [H] at hn; norm_num at hn`, which turns the hypothesis into a false numeral
equation and closes by contradiction. No auxiliary lemma is stated: the two
children are the two goals `constructor` creates, and the reverse child embeds
the further `mod_cases` split.

## Why it is good

1. `constructor` (line 33) turns the `↔` goal into exactly two subgoals, and
   both close: the forward direction in five lines (34-38) and the reverse in
   nine (39-47), with no auxiliary lemma stated between them. (`check`)
2. The problem's docstring asks "(a) Find all natural numbers n for which
   2ⁿ - 1 is divisible by 7" (lines 21-26), and the formalisation answers it as
   the iff `n ∈ solution_set ↔ 2^n ≡ 1 [MOD 7]` with `solution_set :=
   { n | n % 3 = 0 }` (line 30): the iff *is* the problem statement, not an
   internal helper. (`author-statement`)
3. The reverse direction embeds a second decomposition: `mod_cases H : n % 3`
   (line 44) splits into three residues; residue 0 closes by `exact H`, and
   residues 1 and 2 close by rewriting the hypothesis to a false numeral
   equality and `norm_num` (lines 45-47). (`check`)
4. The same move — state a problem as `P ↔ x ∈ solution_set` and split it with
   `constructor` — is used in [`Compfiles/Usa1973P4.lean` lines 29-33](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa1973P4.lean#L29-L33). (`known-use`)

In my opinion the detail worth copying is the asymmetry the split makes
visible: the forward direction is a one-rewrite construction, the reverse is a
case analysis, and `constructor` keeps them apart so each can be closed with
the tool that fits it.

## When to use it, and when not

Use `constructor` on a `↔` goal when the two directions want genuinely
different arguments — a construction in one direction and a refutation in the
other, as here — so that splitting lets each side be closed by its own tactic
chain. It is also the natural shape when the goal is a "characterise the
solutions" problem: one direction shows the candidate solutions work, the other
shows nothing else works.

Avoid it when one direction is definitional or follows by symmetry (then
`constructor` leaves a trivial child and the split adds nothing), when the two
directions share the same rewriting (a single `rw`/`calc` chain often proves
both at once), or when the equivalence is definitional and `rfl` suffices.

## Consequences

`constructor` on an iff creates exactly two obligations — the forward and the
reverse implication — and each must be closed on its own; if the two directions
share structure, that structure is proved twice. The reverse direction here is
not self-contained: it needs a further case split `mod_cases H : n % 3`, so the
two children are of very different difficulty (5 lines versus 9). A known
failure mode is splitting an iff whose two directions are the same argument in
mirror image, which doubles the proof instead of shortening it.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push-main.yaml runs 'lake build' on pushes to main; pinned commit 1745e6ced3e671bd74417548494b034eb2c87da8 is the tip of the default branch main (API confirms default_branch=main and main HEAD = pinned commit). File Compfiles/Imo1964P1.lean is a module built by lake build. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read code/Compfiles/Imo1964P1.lean: line 33 is constructor, forward child lines 34-38, reverse child lines 39-47, no auxiliary lemma between them; CI push-main.yaml runs lake build on main. | verifier |
| 2 | verified | Docstring lines 21-26 quote '(a) Find all natural numbers n for which 2^n - 1 is divisible by 7'; line 30 defines solution_set as the set of n with n % 3 = 0; line 32 states the iff n in solution_set iff 2^n congruent 1 mod 7. | verifier |
| 3 | verified | Line 44 mod_cases H : n % 3 splits into three residues; line 45 closes residue 0 by exact H; lines 46 and 47 close residues 1 and 2 by rw [H] at hn; norm_num at hn. | verifier |
| 4 | verified | Fetched Compfiles/Usa1973P4.lean at the pinned commit: lines 29-32 state problem usa1973_p4 as a conjunction iff membership in solution_set, line 33 is constructor. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent imo1964_p1a is the iff n ∈ solution_set ↔ 2^n ≡ 1 [MOD 7]; line 33 "constructor" splits it into exactly the two children the entry lists (forward 34-38, reverse 39-47), matching the copied code/Compfiles/Imo1964P1.lean byte-for-byte. Forward closes via obtain ⟨m,hm⟩ := Nat.dvd_of_mod_eq_zero hn, change 2^n%7=1, rw [hm, Nat.pow_mul, Nat.pow_mod], norm_num (2^3%7=1). Reverse closes via change to n%3=0, rewrite to 2^(n%3)%7=1, mod_cases H : n%3 into 0/1/2: exact H, and rw[H] at hn; norm_num at hn (2%7≠1, 4%7≠1). All line refs in README/entry.json match the file; the argument closes and CI builds the module. | reviewer-correctness |
| generality | accept | The move is stated generically, not tied to this IMO problem: applicability.goal_shape names the general goal form 'P iff Q', use_when gives a portable criterion (the two directions want genuinely different arguments - construction vs refutation - and each closes independently), and the README adds the reusable 'characterise the solutions' framing. avoid_when is honest and specific (definitional/symmetric direction; shared rewriting provable by one rw/calc chain; definitional equivalence). Consequences are honest and concrete: two obligations, shared structure proved twice, reverse child needs a further mod_cases split and the children differ in difficulty (5 vs 9 lines, matching the copied code at lines 34-38 and 39-47), plus a real failure mode (mirror-image directions double the proof). The description clearly generalises beyond IMO 1964 P1(a). | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes: 1 file byte-identical at pinned commit 1745e6ced3e671bd74417548494b034eb2c87da8. Commit, permalinks (files + sites #L32-L47, #L30), and sha256 in entry.json all match the copied file. Licence consistent everywhere: code header says 'Released under Apache 2.0', entry.json/source.json/SOURCE.md/README all say Apache-2.0, and sources/compfiles/upstream-LICENSE is the Apache 2.0 text. Source note points to the correct repo, pinned commit and licence. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/dwrensha/compfiles at commit `1745e6ced3e671bd74417548494b034eb2c87da8`, under `Apache-2.0`; see the [source note](../../sources/compfiles/SOURCE.md) for the licence text and attribution.
