# Calc chain reduces 2^n mod 7 to 2^(n % 3) (IMO 1964 Q1)

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |

## Intent

Show that `2 ^ n` modulo 7 depends only on `n % 3` by rewriting `n` as
`3 * (n / 3) + n % 3`, then pushing the period `2 ^ 3 ≡ 1 (mod 7)` through a
four-link `calc` chain that ends at `2 ^ (n % 3)`. Each link closes with one
tactic, and no auxiliary lemma is stated.

## The decomposition

### parent `two_pow_mod_seven`: [`Archive/Imo/Imo1964Q1.lean` lines 28-33](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1964Q1.lean#L28-L33) ([local copy](code/Archive/Imo/Imo1964Q1.lean))

```lean
theorem two_pow_mod_seven (n : ℕ) : 2 ^ n ≡ 2 ^ (n % 3) [MOD 7] :=
  let t := n % 3
  calc 2 ^ n = 2 ^ (3 * (n / 3) + t) := by rw [Nat.div_add_mod]
    _ = (2 ^ 3) ^ (n / 3) * 2 ^ t := by rw [pow_add, pow_mul]
    _ ≡ 1 ^ (n / 3) * 2 ^ t [MOD 7] := by gcongr; decide
    _ = 2 ^ t := by ring
```

### child `step1-div-add-mod`: [`Archive/Imo/Imo1964Q1.lean` lines 30-30](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1964Q1.lean#L30-L30) ([local copy](code/Archive/Imo/Imo1964Q1.lean))

```lean
  calc 2 ^ n = 2 ^ (3 * (n / 3) + t) := by rw [Nat.div_add_mod]
```

### child `step2-pow-add-mul`: [`Archive/Imo/Imo1964Q1.lean` lines 31-31](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1964Q1.lean#L31-L31) ([local copy](code/Archive/Imo/Imo1964Q1.lean))

```lean
    _ = (2 ^ 3) ^ (n / 3) * 2 ^ t := by rw [pow_add, pow_mul]
```

### child `step3-gcongr`: [`Archive/Imo/Imo1964Q1.lean` lines 32-32](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1964Q1.lean#L32-L32) ([local copy](code/Archive/Imo/Imo1964Q1.lean))

```lean
    _ ≡ 1 ^ (n / 3) * 2 ^ t [MOD 7] := by gcongr; decide
```

### child `step4-ring`: [`Archive/Imo/Imo1964Q1.lean` lines 33-33](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1964Q1.lean#L33-L33) ([local copy](code/Archive/Imo/Imo1964Q1.lean))

```lean
    _ = 2 ^ t := by ring
```

How the parts fit. The parent first names the residue `let t := n % 3`, then a
single `calc` walks from `2 ^ n` to `2 ^ t` in four links, each link its own
child:

1. Link 1 rewrites `n` as `3 * (n / 3) + n % 3` with `Nat.div_add_mod`, so the
   period `3` becomes visible.
2. Link 2 splits `2 ^ (3 * (n/3) + t)` into `(2 ^ 3) ^ (n/3) * 2 ^ t` with
   `pow_add, pow_mul`.
3. Link 3 is the only link that uses the modulus 7: `gcongr` lifts the pointwise
   congruence `2 ^ 3 ≡ 1 [MOD 7]` to the whole product, and `decide` discharges
   that base congruence because both sides are numerals.
4. Link 4 reduces `1 ^ (n/3) * 2 ^ t` to `2 ^ t` by `ring`.

Each link closes with a single tactic. Transitivity — that the chain proves
`2 ^ n ≡ 2 ^ t [MOD 7]` — is discharged by the `calc` elaborator itself, not by a
named lemma; the proof is these four links and nothing else.

## Why it is good

1. The universally quantified congruence is reduced to a four-link chain, one
   tactic per link, with no auxiliary lemma in between (lines 28-33). *(check)*
2. The authors state the period the chain encodes in the module docstring: "the
   order of 2 mod 7 is 3" (lines 18-19). *(author-statement)*
3. The lemma is referenced twice more in the file — line 45 and line 54 — so the
   chain is also the key fact the two later proofs hang on. *(measurement)*
4. The same calc-chain move appears twice more in the file: `imo1964_q1a`
   (lines 42-47) chains equivalences over `↔`, and `imo1964_q1b` (lines 53-55)
   chains congruences over `≡ [MOD 7]`, so the move generalises across relation
   kinds. *(known-use)*

In my opinion the detail worth copying is that the period `2 ^ 3 ≡ 1 [MOD 7]`
is discharged *inline* by `decide` inside link 3 rather than stated as a separate
fact, which is what keeps the whole reduction to four lines.

## When to use it, and when not

Use it when a congruence can be reduced to a residue by pushing a known,
computable period through a chain of equalities and congruences, where each link
is one rewrite or a normalising tactic (`decide`, `ring`, `gcongr`). Avoid it
when a link needs a non-rewrite argument (induction, a case split, a named lemma)
that would not sit on one `calc` line; when the period is not a closed
computation that `decide` can close (a symbolic base or modulus); or when the
congruence does not respect the operation a link performs (link 3 relies on
`≡ [MOD 7]` being a congruence for `^` and `*`).

## Consequences

The chain replaces one congruence with four sub-goals — the links — but none is
a named lemma: each link's justification is an inline tactic, and the `calc`
elaborator supplies transitivity, so no separate transitivity proof is owed. The
one substantive obligation is the period `2 ^ 3 ≡ 1 [MOD 7]`, discharged inline
by `decide`; with a symbolic base or modulus that link would not close and would
have to be extracted into its own lemma. The chain mixes `=` and `≡` links, which
typechecks only because an equality implies the congruence reflexively; reordering
the relations would break the chain.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (push to master/default branch) uses build_template.yml, which builds Archive via 'lake build --no-build --wfail Archive' (build_template.yml:297); Archive.lean:20 'public import Archive.Imo.Imo1964Q1' pulls in the entry's file; commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is on master (GitHub compare API: behind master by 1, merge base = the commit) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read local copy code/Archive/Imo/Imo1964Q1.lean lines 28-33 (byte-identical to upstream at e1545ebed per provenance). two_pow_mod_seven is exactly a let t := n%3 followed by a four-link calc: rw [Nat.div_add_mod], rw [pow_add, pow_mul], gcongr; decide, ring; no have or auxiliary lemma intervenes. | verifier |
| 2 | verified | Read local copy lines 18-19: docstring states "the order of 2 mod 7 is 3. Therefore for (b), it suffices to check n = 0, 1, 2." Matches the claim; only the LaTeX math delimiters are stripped. | verifier |
| 3 | verified | Read local copy: line 45 in imo1964_q1a uses (two_pow_mod_seven n).symm.trans and .trans; line 54 in imo1964_q1b uses (two_pow_mod_seven n).symm. Two reference sites as claimed. | verifier |
| 4 | verified | Read local copy: imo1964_q1a (lines 42-47) is a calc chain over iff; imo1964_q1b (lines 53-55) is a calc chain over Nat.ModEq congruence. Two further calc-chain uses over different relations, as claimed. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent two_pow_mod_seven (lines 28-33) is exactly a let t := n%3 followed by a four-link calc; the four children in entry.json match the copied code verbatim: link1 2^n = 2^(3*(n/3)+t) by rw [Nat.div_add_mod] (L30), link2 = (2^3)^(n/3)*2^t by rw [pow_add, pow_mul] (L31), link3 ≡ 1^(n/3)*2^t [MOD 7] by gcongr; decide (L32), link4 = 2^t by ring (L33). Closing methods match the code exactly, no auxiliary lemma/have intervenes, and the chain ends at 2^(n%3) so it closes: build is ci-record (mathlib CI builds Archive, Archive.lean imports Archive.Imo.Imo1964Q1, commit on master). | reviewer-correctness |
| generality | accept | Generality lens: the move is stated beyond the 2^n mod 7 example. applicability.goal_shape abstracts to 'a congruence a ≡ b [MOD m] (or equality) where a can be rewritten so that a periodic subterm appears, collapsing to a residue depending on n only through n % k'; use_when/avoid_when are general, not number-theory-specific. Known-use claim 4 (verified) shows the calc-chain works over two further relation kinds (↔ in q1a L42-47, ≡ in q1b L53-55). When-not-to-use lists three specific, honest conditions (non-rewrite link that won't sit on one calc line; period not decide-closable i.e. symbolic base/modulus; congruence not respecting the operation used). Consequences are honest and specific: four link sub-goals, no named lemma, calc elaborator supplies transitivity, the one substantive obligation is the decide-discharged period, and the =/≡ mix typechecks only via reflexive implication so reordering breaks. No grounds to object under this lens. | reviewer-generality |
| provenance-licence | accept | Commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is recorded identically in entry.json source.commit, sources/mathlib4/source.json and SOURCE.md; all permalinks point to that commit at Archive/Imo/Imo1964Q1.lean with line numbers matching the local copy (L28-33 parent, L30-33 children, L18-19 and L42-47/L53-55 for claims). Licence is consistent across entry source.licence=Apache-2.0, source.json licence, SOURCE.md, the file header 'Released under Apache 2.0 license' and upstream-LICENSE (Apache License 2.0). files.bytes=1755 and sha256 aee9931a... match the local copy; check_provenance reports 1 file byte-identical at the pinned commit. Everything is traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
