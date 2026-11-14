# Iff-split of the Kleene theorem: regular languages and regexp languages coincide

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | rocq |
| Status | accepted |
| Source | [reglang](../../sources/reglang/SOURCE.md) at `dd7521632d84` |
| Licence | `CECILL-B` |
| Licence recorded | 2026-11-14T15:41:41Z |

## Intent

State the Kleene theorem as an inhabitation equivalence between "L is
regular" and "there is a regexp for L", then close each direction by applying
one named correctness lemma — `dfa_to_re_correct` (DFA to regexp) for the
forward direction and `re_to_dfa_correct` (regexp to DFA) for the backward —
so that the iff adds nothing beyond pairing the two constructions already
proved earlier in the file.

## The decomposition

### parent `regularP`: [`theories/regexp.v` lines 359-365](https://github.com/rocq-community/reglang/blob/dd7521632d849ef1d143398262d0fb98e536dd6c/theories/regexp.v#L359-L365) ([local copy](code/theories/regexp.v))

```coq
Lemma regularP (char : finType) (L : lang char) :
  regular L <-T->  { e : regexp char | forall x, L x <-> x \in e}.
Proof.
  split => [[A HA]|[e He]].
  - exists (dfa_to_re A) => x. by rewrite -dfa_to_re_correct.
  - exists (re_to_dfa e) => x. by rewrite re_to_dfa_correct.
Qed.
```

### child `dfa_to_re_correct`: [`theories/regexp.v` lines 307-312](https://github.com/rocq-community/reglang/blob/dd7521632d849ef1d143398262d0fb98e536dd6c/theories/regexp.v#L307-L312) ([local copy](code/theories/regexp.v))

```coq
  Lemma dfa_to_re_correct : dfa_lang A =i dfa_to_re.
  Proof.
    move => w. apply/idP/big_plusP => [H|[x Hx]].
    - exists (delta_s A w) => //. by rewrite -L_R set_enum dfa_L.
    - by rewrite -L_R set_enum dfa_L inE /dfa_accept => /eqP ->.
  Qed.
```

### child `re_to_dfa_correct`: [`theories/regexp.v` lines 134-135](https://github.com/rocq-community/reglang/blob/dd7521632d849ef1d143398262d0fb98e536dd6c/theories/regexp.v#L134-L135) ([local copy](code/theories/regexp.v))

```coq
Lemma re_to_dfa_correct (r : regexp char) : dfa_lang (re_to_dfa r) =i r.
Proof. move => w. by rewrite -nfa_to_dfa_correct re_to_nfa_correct. Qed.
```

How the parts fit. `regularP` is an inhabitation equivalence: `regular L`
(`{ A : dfa | forall x, L x <-> x \in dfa_lang A }`, defined in
`theories/dfa.v`) is equivalent, via the project's `iffT`
(`Variant iffT T1 T2 := IffT of (T1 -> T2) & (T2 -> T1)`, `theories/misc.v`),
to `{ e : regexp char | forall x, L x <-> x \in e }`. The proof is a single
`split` that produces the two directions of `iffT`, and each direction is one
line:

- **Forward (DFA → regexp)**: from `A : dfa` and `HA : forall x, L x <-> x \in
  dfa_lang A`, it produces the regexp `dfa_to_re A` and closes the goal
  `forall x, L x <-> x \in dfa_to_re A` by rewriting with
  `dfa_to_re_correct` (which states `dfa_lang A =i dfa_to_re`) against `HA`.
- **Backward (regexp → DFA)**: from `e : regexp` and `He : forall x, L x <->
  x \in e`, it produces the DFA `re_to_dfa e` and closes by rewriting with
  `re_to_dfa_correct` against `He`.

Lemma graph (which lemma uses which, read from each proof's citations):

```
regularP
├── dfa_to_re_correct ── L_R ── L_rec ── L_star ── L_catL ── L_cat ── LP
│         └── (also: big_plusP, dfa_L)
└── re_to_dfa_correct ── re_to_nfa_correct, nfa_to_dfa_correct
```

`dfa_to_re_correct` is a good leaf: its statement `dfa_lang A =i dfa_to_re`
is self-contained (it says the Kleene construction's regexp accepts exactly
the DFA's language), and its proof closes on its own — a reflection split via
`big_plusP`, then each branch closed by rewriting with the sibling lemma `L_R`
(regexp.v:291) and `dfa_L` (regexp.v:166). So the parent's forward direction
is one lemma away, and that lemma carries the real content. `re_to_dfa_correct`
is also a good leaf: `dfa_lang (re_to_dfa r) =i r` closes by a single rewrite
composing two named correctness lemmas, `nfa_to_dfa_correct` (nfa.v) and
`re_to_nfa_correct` (regexp.v:111), so the regexp→NFA→DFA path is compressed
into one fact. The two children are asymmetric in content — one is a deep
Kleene construction, the other a composition of two translations — yet each
presents the parent with exactly one rewrite, which is why the iff glue can be
four lines.

## Why it is good

1. `regularP`, the Kleene theorem, is a declared lemma at regexp.v:359-365
   (check, `declared`).
2. No goal in `theories/regexp.v` is closed by `admit`, `Admitted`, `Axiom` or
   `axiom`: the whole 556-line file has no hole (check, `no_sorry`).
3. The glue is 7 lines including the statement, and the proof body is a
   `split` plus one line per direction (check, `lines`).
4. The decomposition is shallow at the top but deep below: the two directions
   are two named lemmas, but the forward direction rests on a chain of 7
   project lemmas (regularP → dfa_to_re_correct → L_R → L_rec → L_star →
   L_catL → L_cat → LP), which I traced line-by-line (measurement).
5. The same move is reused one level down: `nfa_regular` (nfa.v:416-421) is the
   DFA↔NFA analogue of the same iff-split, again one correctness lemma per
   direction (known-use).

In my opinion the detail worth copying is the naming discipline: each
direction of the equivalence is a *separately named* correctness lemma stated
where its construction is defined, so the head theorem is a pure two-way
wiring. The iff-split is not where the work is; it is where the two
already-proved halves are combined.

## When to use it, and when not

Use it when a theorem states that two notions are equivalent by construction,
and each direction is already proved as its own named lemma (`x_to_y_correct`,
`y_to_x_correct`) whose statement is a language/function equality closed by a
rewrite. The two sides should be constructible types — here `regular L` and
the regexp sig type are both inhabited records — so that the equivalence is an
`iffT` between inhabitants, not a bare logical `iff`.

Avoid it when one direction still needs real work that no lemma proves (the
split then leaves that goal at full difficulty, and the move has not bought
anything); when the equivalence is a plain `Prop` `A <-> B`, which is split
with `split`/`constructor` on `iff` rather than on an `iffT`; or when the two
directions are not symmetric constructions, so a one-line glue with two
rewrites will not close them.

## Consequences

The move creates two obligations — the two directions of the equivalence —
each discharged by a pre-existing named lemma, so the split adds no content of
its own; the theorem is exactly as strong as its two correctness lemmas.
Failure modes: a direction that is not already a lemma leaves a goal with the
full difficulty; and `<-T->` is a Type-level `iffT` between constructible
types, so a plain `Prop` equivalence `A <-> B` must be split with
`split`/`constructor` on `iff`, or the split will not apply. The glue also
assumes the two correctness lemmas have the same shape (`f x =i ...`), so a
direction whose lemma needs side conditions would not close by the single
rewrite shown here.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml (Docker CI, push to master) builds coq-reglang.opam via coq-community/docker-coq-action, which compiles theories/regexp.v (listed in _CoqProject); also .github/workflows/nix-action-8.16.yml and nix-action-8.17.yml build job 'reglang' on push to master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: dfa_to_re_correct@theories/regexp.v:363, re_to_dfa_correct@theories/regexp.v:364; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 5 file(s) byte-identical at dd7521632d849ef1d143398262d0fb98e536dd6c | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(regularP, theories/regexp.v, 359-365) -> declared: regularP is declared at theories/regexp.v:359 | check_claims.py |
| 2 | verified | no_sorry(theories/regexp.v, 1-556) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/regexp.v:1-556 | check_claims.py |
| 3 | verified | lines(parent, 7) -> lines: site parent has 7 lines | check_claims.py |
| 4 | verified | read theories/regexp.v at pinned commit: regularP cites dfa_to_re_correct at :363, dfa_to_re_correct cites L_R at :310, L_R cites L_rec at :298, L_rec cites L_star at :262, L_star cites L_catL at :242, L_catL cites L_cat at :233, L_cat cites LP at :223; that is 7 lemmas below regularP | verifier |
| 5 | verified | read theories/nfa.v:416-421 at pinned commit: Lemma nfa_regular L : regular L <-T-> {N : nfa | ...}; Proof. split => [[A]|[N]] H. exists (dfa_to_nfa A) => x. by rewrite -dfa_to_nfa_correct. exists (nfa_to_dfa N) => x. by rewrite -nfa_to_dfa_correct. Qed. — same iff-split, one correctness lemma per direction | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent regularP (regexp.v:359-365) is one split on the project's iffT type, forward by dfa_to_re_correct and backward by re_to_dfa_correct, which are exactly the two children and the only lemmas the parent cites (lines 363 and 364). Both children's statements and closed_by match the copied code: dfa_to_re_correct (307-312) closes via apply/idP/big_plusP then rewrite -L_R set_enum dfa_L; re_to_dfa_correct (134-135) closes via rewrite -nfa_to_dfa_correct re_to_nfa_correct. All three end in Qed with no admit/Admitted/Axiom, so the decomposition closes. Shape numbers are correct: direct_lemmas=2; glue_lines=7 (359-365); child_lines=[6,2] (307-312 and 134-135); depth=7 matches the chain regularP, dfa_to_re_correct, L_R, L_rec, L_star, L_catL, L_cat, LP (edges at :310, :298, :262, :242, :233, :223 all present, and LP is a leaf). | reviewer-correctness |
| generality | accept | Move generalises: applicability states the pattern as an inhabitation equivalence via the Type-level iffT record (misc.v:34) between two constructible sig types (regular L is a dfa sig type, dfa.v:70), each direction already a named correctness lemma closed by one rewrite - confirmed in regularP (regexp.v:359-365) and the analogue nfa_regular (nfa.v:416-421). When-not-to-use is honest and specific: flags the plain-Prop A iff B case (needs Prop iff, not iffT), a direction still needing real work, and asymmetric constructions. Consequences are honest (split adds no content, proof only as strong as the two lemmas) and name concrete failure modes. It says what makes the leaves good for a bounded prover: dfa_to_re_correct and re_to_dfa_correct are self-contained language-equalities closed by one rewrite each, so the glue is four lines. | reviewer-generality |
| provenance-licence | accept | check_provenance passes: all 5 copied files byte-identical at commit dd7521632d849ef1d143398262d0fb98e536dd6c, matching the commit in entry.json, sources/reglang/source.json and SOURCE.md; permalinks all pin that commit with the correct paths and line anchors, and sed -n of the cited ranges (regexp.v 359-365, 307-312, 134-135; nfa.v 416-421) matches the statements/claims verbatim; licence CECILL-B is recorded consistently across entry.json source.licence, README, source.json, SOURCE.md and the copied upstream-LICENSE (CeCILL-B text). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-community/reglang at commit `dd7521632d849ef1d143398262d0fb98e536dd6c`, under `CECILL-B`; see the [source note](../../sources/reglang/SOURCE.md) for the licence text and attribution.
