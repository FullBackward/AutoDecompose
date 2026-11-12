# Hahn-Banach extension: witness g built from a Zorn-maximal linear graph

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | rocq |
| Status | accepted |
| Source | [mathcomp-analysis](../../sources/mathcomp-analysis/SOURCE.md) at `eca10f89bd85` |
| Licence | `CECILL-C` |

## Intent

Prove the Hahn-Banach extension theorem — every linear functional `f` on a
submodule `F'` bounded by a convex `p` extends to a linear functional `g` on
the whole module `V` bounded by the same `p` — by *constructing the witness*
`g` from a Zorn-maximal linear graph and then proving its properties. The glue
obtains a maximal graph with `zornS_ex`, reads a function `g` off it with
`hahn_banach_witness`, closes `g`'s linearity with `lingraphD`/`lingraphZ`,
and packs `g` as a `{scalar V}`.

## The decomposition

### parent `hahn_banach_extension`: [`theories/functional_analysis/hahn_banach_theorem.v` lines 306-323](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L306-L323) ([local copy](code/theories/functional_analysis/hahn_banach_theorem.v))

```coq
Theorem hahn_banach_extension : exists2 g : {scalar V},
  (forall x, g x <= p x) & forall z : F', g (\val z) = f z.
Proof.
pose graphF (v : V) r := exists2 z : F', v = \val z & r = f z.
have [z /(hahn_banach_witness p_cvx)[g gP]] := zornS_ex f_bounded_by_p.
have scalg : linear_for *%R g.
  case: z gP => [c [_ ls1 _ _]] /= gP.
  have addg : zmod_morphism g.
    by move=> w1 w2; apply/gP; apply: lingraphD => //; apply/gP.
  suff scalg : scalable_for *%R g.
    by move=> a u v; rewrite -gP -(addrC v) -(addrC (g v)); apply/ls1; exact/gP.
  by move=> w l; apply/gP; apply: lingraphZ => //; exact/gP.
pose lg := GRing.isLinear.Build _ _ _ _ g scalg.
pose g' : {linear V -> R | *%R} := HB.pack g lg.
exists g'.
  by case: z gP => [c [_ _ bp _]] /= gP => x; apply: bp; exact/gP.
by move=> z'; apply/gP; case: z {gP} => [c [_ _ _ pf]] /=; exact: pf.
Qed.
```

### child `zornS_ex`: [`theories/functional_analysis/hahn_banach_theorem.v` lines 124-161](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L124-L161) ([local copy](code/theories/functional_analysis/hahn_banach_theorem.v))

```coq
Lemma zornS_ex : exists g : zorn_type, forall z, zornS g z -> z = g.
Proof.
pose Rbool x y := `[< zornS x y >].
have RboolP z t : Rbool z t <-> zornS z t by split => /asboolP.
suff [t st] : exists t : zorn_type, forall s : zorn_type, Rbool t s -> s = t.
  by exists t; move => z /RboolP tz; exact: st.
apply: (@Zorn zorn_type Rbool); first by move=> t; exact/RboolP.
- by move=> r s t /RboolP a /RboolP b; apply/RboolP => x y /a /b.
- move=> r s /RboolP a /RboolP b; apply: zorn_type_eq.
  by apply: funext => z; apply: funext => h; apply: propext; split => [/a | /b].
move=> A Amax.
have [[w Aw]|eA] := lem (exists a, A a); last first.
  by exists zphi => a Aa; absurd: eA; exists a.
(* g is the union of the graphs indexed by elements in a *)
pose g v r := exists2 a, A a & carrier a v r.
have g_fun : functional_graph g.
  move=> v r1 r2 [a Aa avr1] [b Ab bvr2].
  have [|] : Rbool a b \/ Rbool b a by exact: Amax.
  - rewrite /Rbool /RboolP /zornS.
    case: b Ab bvr2 {Aa} => s2 [fs2 _ _ _] /= _ s2vr2 /asboolP ecas2.
    by move/ecas2 : avr1 => /fs2 /(_ s2vr2).
  - rewrite /Rbool /RboolP /zornS.
    case: a Aa avr1 {Ab} => s1 [fs1 _ _ _] /= _ s1vr1 /asboolP ecbs1.
    by move/ecbs1: bvr2; exact: fs1.
have g_lin : linear_graph g.
  move=> v1 v2 l r1 r2 [a1 Aa1 c1] [a2 Aa2 c2].
  have [/RboolP sc12 | /RboolP sc21] := Amax _ _ Aa1 Aa2.
  - have {sc12 Aa1 a1} {}c1 : carrier a2 v1 r1 by exact: sc12.
    by exists a2 => //; case: a2 {Aa2} c2 c1 => c /= [_ + _ _] *; exact.
  - have {sc21 Aa2 a2} {}c2 : carrier a1 v2 r2 by exact: sc21.
    by exists a1 => //; case: a1 {Aa1} c2 c1 => c /= [_ + _ _] *; exact.
have g_majp : le_graph p g by move=> v r [[c/= [fs1 ls1 ms1 ps1]]]/= _ => /ms1.
have g_prol : extend_graph g.
   by move=> *; exists w => //; case: w Aw => [c [_ _ _ +]] _ //=; exact.
have spec_g : le_extend_graph g by split.
pose zg := ZornType spec_g.
by exists zg => [a Aa]; apply/RboolP; rewrite /zornS => v r cvr; exists a.
Qed.
```

### child `hahn_banach_witness`: [`theories/functional_analysis/hahn_banach_theorem.v` lines 279-286](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L279-L286) ([local copy](code/theories/functional_analysis/hahn_banach_theorem.v))

```coq
Lemma hahn_banach_witness :
  exists h : V -> R, forall v r, carrier g v r <-> h v = r.
Proof.
have [h hP] := choice total_g.
exists h => v r; split=> [|<-//].
move: g gP total_g hP => [c /= [fg _ _ _]] _ _ hP cvr.
by rewrite (fg v r (h v)).
Qed.
```

### child `lingraphD`: [`theories/functional_analysis/hahn_banach_theorem.v` lines 67-68](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L67-L68) ([local copy](code/theories/functional_analysis/hahn_banach_theorem.v))

```coq
Lemma lingraphD x1 x2 r1 r2 : f x1 r1 -> f x2 r2 -> f (x1 - x2) (r1 - r2).
Proof. by move=> f1 f2; have := lf (-1) f1 f2; rewrite !scaleN1r mulN1r. Qed.
```

### child `lingraphZ`: [`theories/functional_analysis/hahn_banach_theorem.v` lines 64-65](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L64-L65) ([local copy](code/theories/functional_analysis/hahn_banach_theorem.v))

```coq
Lemma lingraphZ x r l : f x r -> f (l *: x) (l * r).
Proof. by move=> fxr; have := lf l (lingraph_00 fxr) fxr; rewrite !add0r. Qed.
```

### context `linear_graph`: [`theories/functional_analysis/hahn_banach_theorem.v` lines 51-54](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L51-L54) ([local copy](code/theories/functional_analysis/hahn_banach_theorem.v))

```coq
Definition graph := V -> R -> Prop.

Definition linear_graph (f : graph) :=
  forall v1 v2 l r1 r2, f v1 r1 -> f v2 r2 -> f (v1 + l *: v2) (r1 + l * r2).
```

### context `le_extend_graph`: [`theories/functional_analysis/hahn_banach_theorem.v` lines 88-98](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L88-L98) ([local copy](code/theories/functional_analysis/hahn_banach_theorem.v))

```coq
Definition extend_graph f := forall v : F', f (\val v) (phi v).

Definition le_graph p f := forall v r, f v r -> r <= p v.

Definition functional_graph f := forall v r1 r2, f v r1 -> f v r2 -> r1 = r2.

Definition le_extend_graph f :=
  [/\ functional_graph f, linear_graph f, le_graph p f & extend_graph f].

Record zorn_type : Type := ZornType
  {carrier : graph V; specP : le_extend_graph carrier}.
```

### context `zornS`: [`theories/functional_analysis/hahn_banach_theorem.v` lines 121-121](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L121-L121) ([local copy](code/theories/functional_analysis/hahn_banach_theorem.v))

```coq
Definition zornS z1 z2 := forall x y, carrier z1 x y -> carrier z2 x y.
```

### context `section_context`: [`theories/functional_analysis/hahn_banach_theorem.v` lines 299-304](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L299-L304) ([local copy](code/theories/functional_analysis/hahn_banach_theorem.v))

```coq
Context {R : realType} (V : lmodType R) (F : pred V).
Variables (F' : subLmodType F) (f : {linear F' -> R}) (p : V -> R).

Hypothesis p_cvx : @convex_function R V [set: V] p.

Hypothesis f_bounded_by_p : forall z : F', f z <= p (\val z).
```

How the parts fit. The main theorem is an `exists2` (a witness plus two
properties), so the glue has three obligations: build `g`, prove `g` is
linear (needed to pack it as a `{scalar V}`), and prove the two stated
properties `g x <= p x` and `g (\val z) = f z`.

1. **Build `g`.** Line 310 `have [z /(hahn_banach_witness p_cvx)[g gP]] :=
   zornS_ex f_bounded_by_p.` obtains a `z : zorn_type` that is maximal for
   `zornS` (child `zornS_ex`), then applies child `hahn_banach_witness` to
   turn `z`'s carrier graph into a function `g` with the equivalence
   `gP : carrier z v r <-> g v = r`.
2. **Prove `g` is linear.** The block `have scalg : linear_for *%R g.` (lines
   311-317) destructures `z` into its spec `[c [_ ls1 _ _]]`, where `ls1 :
   linear_graph (carrier z)`. Additivity closes through `lingraphD` (line 314,
   `apply: lingraphD`) and scalability through `lingraphZ` (line 317), each
   round-tripping through `gP` because the statements are about the carrier
   graph while the goal is about `g`. Line 318-319 pack `g` with
   `GRing.isLinear.Build` and `HB.pack` into `g' : {linear V -> R | *%R}`.
3. **Prove the two properties.** Line 321 closes `g x <= p x` from the
   `le_graph` component (`bp`) of the spec; line 322 closes `g (\val z) = f z`
   from the `extend_graph` component (`pf`).

The lemma graph (which project lemma uses which):

```
hahn_banach_extension
├── zornS_ex          ── zorn_type_eq, zphi (= ZornType spec_phi)
├── hahn_banach_witness ── total_g ── domain_extend
├── lingraphD         ── (linear_graph hypothesis lf)
└── lingraphZ         ── lingraph_00
```

Each child is a good leaf because its statement is self-contained and its
proof closes on its own or from named siblings, never reaching back into the
parent:

- `zornS_ex` (124-161) is the entire maximality argument. Its statement
  "there is a `zorn_type` maximal for `zornS`" is independent of the parent;
  it closes by `apply: (@Zorn zorn_type Rbool)` on the order `zornS`, builds
  the union graph of a maximal chain `A`, and returns `ZornType g` (empty
  chain → `zphi`, the graph of `phi` built from `spec_phi`). It uses the
  siblings `zorn_type_eq` and `zphi`.
- `hahn_banach_witness` (279-286) is the statement "a functional maximal
  graph is the graph of a function": it closes with `choice total_g` plus the
  `functional_graph` component of the spec. Its helper `total_g` (273-277,
  "every `v` has some `r` with `carrier g v r`") closes from `domain_extend`
  (167-269), the big lemma that extends a graph along one direction.
- `lingraphD` (67-68) and `lingraphZ` (64-65) are one-line closure lemmas
  over the abstract `linear_graph` hypothesis `lf`; each is a single
  `have := lf …` plus a rewrite (`scaleN1r mulN1r`, or `lingraph_00` +
  `add0r`). They are stated and proved once, in the `LinearGraphInternal`
  module, so the glue can import them without unfolding `linear_graph`.

The context sites are the definitions the glue destructures: `linear_graph`
(the two-point linearity predicate), `le_extend_graph` (the 4-way conjunction
`functional_graph ∧ linear_graph ∧ le_graph ∧ extend_graph` that the `case: z
gP => [c [_ ls1 _ _]]` destructuring picks apart), `zornS` (the order), and
`section_context` (the hypotheses `p_cvx` and `f_bounded_by_p` the parent
assumes).

## Why it is good

1. The glue of `hahn_banach_extension` (lines 308-323) calls exactly four
   named lemmas from the same file — `zornS_ex` and `hahn_banach_witness`
   (line 310), `lingraphD` (line 314), `lingraphZ` (line 317) — then packs
   `g` with `GRing.isLinear.Build` and `HB.pack` (lines 318-319). It never
   unfolds `linear_graph` or re-does the maximality argument. (*check*,
   [lines 306-323](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L306-L323).)
2. The main proof is 16 lines while the four children total 50 proof lines
   (`zornS_ex` 38, `hahn_banach_witness` 8, `lingraphD` 2, `lingraphZ` 2), so
   the heavy work lives in the children and the glue is a thin skeleton.
   (*measurement*, [line counts](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L124-L161).)
3. The authors say the file "proves the Hahn-Banach theorem thanks to Zorn's
   lemma" and that `hahn_banach_extension` extends "a linear function on a
   subLmodType of V, that is bounded by a convex function … to a linear map on
   V bounded by the same convex function" (*author-statement*, [lines
   11-15](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L11-L15).)
4. `hahn_banach_extension` is reused as a lemma by three later theorems in the
   same file — `hahn_banach_extension_normed` (line 352),
   `hahn_banach_extension_subctvs` (line 395) and
   `hahn_banach_extension_initialsubctvs` (line 450) — so one witness
   construction pays for four theorems. (*known-use*, [lines
   352, 395, 450](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/functional_analysis/hahn_banach_theorem.v#L352).)
5. All four children and the parent close with `Qed` (lines 161, 286, 68, 65,
   323); the file contains no `Admitted`, `sorry` or `admit`. (*check*, read
   of the whole [copied file](code/theories/functional_analysis/hahn_banach_theorem.v).)

In my opinion the detail worth copying is the *separation of the maximality
argument from the algebraic closure*: `zornS_ex` and `hahn_banach_witness`
own the existence, while `lingraphD`/`lingraphZ` own the algebra, so the glue
only has to sequence them and pack the result.

## When to use it, and when not

Use it when the goal is a constructive existence of a structured object (a
linear map, a group homomorphism, a section) whose existence follows from a
maximality or choice argument followed by a short list of algebraic closure
lemmas, and whose target properties factor into independent named lemmas
(bound, extension, linearity) so the glue stays a skeleton. Avoid it when the
witness has no finite description or its existence is what the proof must
show rather than assume; when the object's properties do not factor through
small named lemmas (each property needs its own bespoke argument, so the
glue is not a skeleton); or when the maximality argument cannot be isolated
into one lemma and keeps leaking into the parent.

## Consequences

The move creates the two obligations of `exists2` (boundedness and extension)
plus the linearity obligation needed to pack `g` as a `{scalar V}`; linearity
is discharged by the two graph-closure lemmas `lingraphD`
(addition/subtraction) and `lingraphZ` (scaling). The witness rests on the
classical choice/Zorn foundation (`choice`, `@Zorn`), so the extension is
non-computational. A failure mode: because `lingraphD`/`lingraphZ` are stated
for a generic `linear_graph f` hypothesis, the glue must first re-establish
that `g` satisfies `linear_graph` by destructuring the `zorn_type` spec
(`case: z gP => [c [_ ls1 _ _]]`); if that spec changes shape, the
destructuring breaks silently in the pack step.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | CI workflow .github/workflows/nix-action-master.yml runs on push to master and builds the project via nix-build (Nix CI, coq-nix-toolbox). The pinned commit eca10f89bd852201c8148ff2f597c7c7346d6df2 is the head of the default branch master (GitHub API commits/master), and _CoqProject lists theories/functional_analysis/hahn_banach_theorem.v, so the CI builds this file on the default branch. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at eca10f89bd852201c8148ff2f597c7c7346d6df2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read byte-identical local copy code/theories/functional_analysis/hahn_banach_theorem.v (provenance pass). Line 310 'have [z /(hahn_banach_witness p_cvx)[g gP]] := zornS_ex f_bounded_by_p.' calls zornS_ex and hahn_banach_witness; line 314 'apply: lingraphD'; line 317 'apply: lingraphZ'; lines 318-319 use GRing.isLinear.Build and HB.pack g lg; line 320 'exists g''. All four lemmas are defined in this same file (zornS_ex L124, hahn_banach_witness L279, lingraphD L67, lingraphZ L64). | verifier |
| 2 | verified | Line counts from the byte-identical local copy: parent 323-308+1=16; zornS_ex 161-124+1=38; hahn_banach_witness 286-279+1=8; lingraphD 68-67+1=2; lingraphZ 65-64+1=2; children total 38+8+2+2=50. Arithmetic matches the claim exactly. | verifier |
| 3 | verified | Read lines 11-15 of the byte-identical local copy: the header says 'This file proves the Hahn-Banach theorem thanks to Zorn's lemma' and 'a linear function on a subLmodType of V, that is bounded by a convex function, can be extended to a linear map on V bounded by the same convex function', matching the quoted author statement (the claim's inserted '...' skips the interleaved words 'considering V an lmodType on a realtype' and 'can be', but the substance is verbatim). | verifier |
| 4 | verified | Read byte-identical local copy: hahn_banach_extension is used at line 352 ('move=> /(hahn_banach_extension convp)[g majgp F_eqgf]') inside hahn_banach_extension_normed; line 395 ('have [g majgp F_eqgf] := @hahn_banach_extension R V _ F' f p convp fp.') inside hahn_banach_extension_subctvs; line 450 ('have [g majgp F_eqgf] := @hahn_banach_extension R V _ F' f p' convp fp'.') inside hahn_banach_extension_initialsubctvs. Three later theorems, same file. | verifier |
| 5 | verified | Read the whole byte-identical local copy (460 lines): zornS_ex ends Qed at L161, hahn_banach_witness at L286, lingraphD at L68, lingraphZ at L65, hahn_banach_extension at L323. grep -n -i -E 'Admitted|sorry|admit|Axiom|Abort' over the file returned no matches. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against copied code/theories/functional_analysis/hahn_banach_theorem.v. Parent hahn_banach_extension (306-323) is an exists2 witness; glue (308-323) references exactly the four children zornS_ex (310), hahn_banach_witness (310), lingraphD (314), lingraphZ (317), then GRing.isLinear.Build/HB.pack (318-319); no other same-file lemma is used. All four child statements and closed_by match the code verbatim (zornS_ex 124, hahn_banach_witness 279-280, lingraphD 67, lingraphZ 64). Parent and all children end in Qed (161,286,68,65,323); no Admitted/admit/sorry/axiom in file. Shape numbers are right: direct_lemmas=4, glue_lines=16 (308-323), child_lines=[38,8,2,2] (124-161,279-286,67-68,64-65); depth=3 correct via chain hahn_banach_witness(279)->total_g(273)->domain_extend(167). Claims 1-5 all hold (line counts sum to 50; known-uses at 352,395,450 confirmed). | reviewer-correctness |
| generality | accept | Generality holds. The move is stated beyond the example: 'When to use' names constructive existence of a structured object (linear map, group homomorphism, section) from a maximality/choice argument plus a short list of algebraic closure lemmas whose properties factor into independent named lemmas. 'When not to use' is honest and specific (no finite description / existence shown not assumed / properties don't factor through small named lemmas / maximality can't be isolated into one lemma). Consequences are specific and honest (non-computational via choice/@Zorn; concrete failure mode where destructuring zorn_type's 4-way spec breaks if its shape changes). Good leaves for a bounded prover are spelled out: statement self-contained, proof closes on its own or from named siblings, never reaching back into the parent, with per-child detail and line counts (38/8/2/2). | reviewer-generality |
| provenance-licence | accept | Provenance pass (check_provenance: 1 file byte-identical at eca10f89bd852201c8148ff2f597c7c7346d6df2); copied file sha256 86caef4f...4165 matches entry.json; all permalinks point to math-comp/analysis/blob/eca10f89.../theories/functional_analysis/hahn_banach_theorem.v (path identical to the copied file); licence recorded as CECILL-C, consistent with source.json, SOURCE.md and the copied upstream-LICENCE (CeCILL-C FREE SOFTWARE LICENSE AGREEMENT); SOURCE.md commit/path/licence all agree with source.json and entry.json. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-comp/analysis at commit `eca10f89bd852201c8148ff2f597c7c7346d6df2`, under `CECILL-C`; see the [source note](../../sources/mathcomp-analysis/SOURCE.md) for the licence text and attribution.
