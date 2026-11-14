# Extensionality over block indices for the equal-incidence-matrix isomorphism

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | isabelle |
| Status | draft |
| Source | [afp](../../sources/afp/SOURCE.md) at `07cd9ca548d1` |
| Licence | `BSD-3-Clause` |

## Intent

Reduce the claim that two ordered incidence systems with the same incidence
matrix are isomorphic to the two obligations of the
`incidence_system_isomorphism` locale, and discharge the block-multiset
equality pointwise, one block index at a time, rewriting each side through the
block-representation lemmas.

## The decomposition

### parent `equal_inc_mat_isomorphism`: [`thys/Fishers_Inequality/Incidence_Matrices.thy` lines 1997-2040](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Fishers_Inequality/Incidence_Matrices.thy#L1997-L2040) ([local copy](code/thys/Fishers_Inequality/Incidence_Matrices.thy))

```isabelle
lemma equal_inc_mat_isomorphism: 
  assumes "D1.N = D2.N"
  shows "incidence_system_isomorphism D1.\<V> D1.\<B> D2.\<V> D2.\<B> (\<lambda> x . \<V>s' ! (List_Index.index \<V>s x))"
proof (unfold_locales)
  show "bij_betw (\<lambda>x. \<V>s' ! List_Index.index \<V>s x) D1.\<V> D2.\<V>" 
  proof -
    have comp: "(\<lambda>x. \<V>s' ! List_Index.index \<V>s x) = (\<lambda> i. \<V>s' ! i) \<circ> (\<lambda> y . List_Index.index \<V>s y)"
      by (simp add: comp_def)
    have leq: "length \<V>s = length \<V>s'" 
      using assms D1.dim_row_is_v D1.points_list_length D2.dim_row_is_v D2.points_list_length by force 
    have bij1: "bij_betw (\<lambda> i. \<V>s' !i) {..<length \<V>s} (set \<V>s') " using leq
      by (simp add: bij_betw_nth D2.distinct) 
    have "bij_betw (List_Index.index \<V>s) (set \<V>s) {..<length \<V>s}" using D1.distinct
      by (simp add: bij_betw_index lessThan_atLeast0) 
    thus ?thesis using bij_betw_trans comp bij1 by simp
  qed
next
  have len:  "length (map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) = length \<B>s'"
    using length_map assms D1.dim_col_is_b by force 
  have mat_eq: "\<And> i j . D1.N $$ (i, j) = D2.N $$ (i, j)" using assms
    by simp 
  have vslen: "length \<V>s = length \<V>s'" using assms
      using D1.dim_row_is_v D1.points_list_length D2.dim_row_is_v D2.points_list_length by force 
  have "\<And> j. j < length \<B>s' \<Longrightarrow> (map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = \<B>s' ! j"
  proof -
    fix j assume a: "j < length \<B>s'" 
    then have "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = (\<lambda>x. \<V>s' ! List_Index.index \<V>s x) ` (\<B>s ! j)"
      by (metis D1.blocks_list_length D1.dim_col_is_b D2.blocks_list_length D2.dim_col_is_b assms nth_map) 
    also have "... = (\<lambda> i . \<V>s' ! i) ` ((\<lambda> x. List_Index.index \<V>s x) ` (\<B>s ! j))" 
      by blast
    also have "... = ((\<lambda> i . \<V>s' ! i) ` {i . i < length \<V>s \<and> D1.N $$ (i, j) = 1})" 
      using D1.block_mat_cond_rev a assms
      by (metis (no_types, lifting) D1.blocks_list_length D1.dim_col_is_b D2.blocks_list_length D2.dim_col_is_b) 
    also have "... = ((\<lambda> i . \<V>s' ! i) ` {i . i < length \<V>s' \<and> D2.N $$ (i, j) = 1})" 
      using vslen mat_eq by simp
    finally have "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = (\<B>s' ! j)" 
      using D2.block_mat_cond_rep' a by presburger
    then show "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = (\<B>s' ! j)" by simp
  qed
  then have "map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s = \<B>s'" 
    using len nth_equalityI[of "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s)" "\<B>s'"] by simp
  then show "image_mset ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) D1.\<B> = D2.\<B>"
    using mset_map by auto
qed
```

### child `block_mat_cond_rev`: [`thys/Fishers_Inequality/Incidence_Matrices.thy` lines 1105-1125](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Fishers_Inequality/Incidence_Matrices.thy#L1105-L1125) ([local copy](code/thys/Fishers_Inequality/Incidence_Matrices.thy))

```isabelle
lemma block_mat_cond_rev: 
  assumes "j < length \<B>s"
  shows "{i . i < length \<V>s \<and> N $$ (i, j) = 1} = ((List_Index.index) \<V>s) ` (\<B>s ! j)"
proof (intro Set.set_eqI iffI)
  fix i assume a1: "i \<in> {i. i < length \<V>s \<and> N $$ (i, j) = 1}"
  then have ilt1: "i < length \<V>s" and Ni1: "N $$ (i, j) = 1" by auto
  then obtain x where "\<V>s ! i = x" and "x \<in> (\<B>s ! j)"
    using assms inc_matrix_point_in_block by blast  
  then have "List_Index.index \<V>s x = i" using distinct  index_nth_id ilt1 by auto
  then show "i \<in> List_Index.index \<V>s ` \<B>s ! j" by (metis \<open>x \<in> \<B>s ! j\<close> imageI) 
next
  fix i assume a2: "i \<in> List_Index.index \<V>s ` \<B>s ! j"
  then obtain x where ieq: "i = List_Index.index \<V>s x" and xin: "x \<in> \<B>s !j"
    by blast 
  then have ilt: "i < length \<V>s"
    by (smt (z3) assms index_first index_le_size nat_less_le nth_mem_mset points_list_length 
        valid_points_index_cons wf_invalid_point)
  then have "N $$ (i, j) = 1" using xin inc_matrix_point_in_block_one
    by (metis ieq assms index_conv_size_if_notin less_irrefl_nat nth_index)
  then show "i \<in> {i. i < length \<V>s \<and> N $$ (i, j) = 1}" using ilt by simp
qed
```

### child `block_mat_cond_rep'`: [`thys/Fishers_Inequality/Incidence_Matrices.thy` lines 1102-1103](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Fishers_Inequality/Incidence_Matrices.thy#L1102-L1103) ([local copy](code/thys/Fishers_Inequality/Incidence_Matrices.thy))

```isabelle
lemma block_mat_cond_rep': "j < length \<B>s \<Longrightarrow> (\<B>s ! j) = ((!) \<V>s) ` {i . i < length \<V>s \<and> N $$ (i, j) = 1}"
  by (simp add: block_mat_cond_rep setcompr_eq_image)
```

### context `block_mat_cond_rep`: [`thys/Fishers_Inequality/Incidence_Matrices.thy` lines 1089-1100](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Fishers_Inequality/Incidence_Matrices.thy#L1089-L1100) ([local copy](code/thys/Fishers_Inequality/Incidence_Matrices.thy))

```isabelle
lemma block_mat_cond_rep:
  assumes "j < length \<B>s"
  shows "(\<B>s ! j) = {\<V>s ! i | i. i < length \<V>s \<and> N $$ (i, j) = 1}"
proof -
  have cond: "\<And> i. i < length \<V>s \<and> N $$ (i, j) = 1 \<longleftrightarrow>i \<in> {..< \<v>} \<and> (col N j) $ i = 1"
    using assms points_list_length by auto
  have "(\<B>s ! j) = (\<lambda> k . \<V>s ! k) ` {i \<in> {..< \<v>} . (col N j) $ i = 1}" 
    using matrix_col_to_block assms by simp
  also have "... = {\<V>s ! i | i. i \<in> {..< \<v>} \<and> (col N j) $ i = 1}" by auto
  finally show "(\<B>s ! j) = {\<V>s ! i | i. i < length \<V>s \<and> N $$ (i, j) = 1}"
    using Collect_cong cond by auto
qed
```

How the parts fit. The parent `equal_inc_mat_isomorphism` is an
`incidence_system_isomorphism` goal, so `proof (unfold_locales)` turns it into
the two obligations of that locale: a bijection of the point sets, and equality
of the block multisets. The bijection half (lines 2001-2012) composes the
point-index function `List_Index.index` with the lookup `(!) Vs'` and closes as
a chain of `bij_betw` facts — not the extensionality move. The block half
(lines 2014-2039) is the extensionality move: it proves
`map ((`) f) Bs = Bs'` pointwise, one `fix j` at a time, then lifts the
pointwise equality to the whole list by `nth_equalityI` (line 2037) and to the
multiset by `mset_map` (line 2039).

The lemma graph (each arrow reads "cites"):

```
equal_inc_mat_isomorphism (parent)
├── block_mat_cond_rev   (child, D1)  ── inc_matrix_point_in_block (l.101) ── inc_matrix_point_not_in_block_zero (l.97)
│                                      ── inc_matrix_point_in_block_one (l.93)
└── block_mat_cond_rep'  (child, D2)  ── block_mat_cond_rep (l.1089)
```

- `block_mat_cond_rev` (applied at `D1`, line 2028) rewrites the left side —
  the image of block `j` under `List_Index.index` — into the index set
  `{i. i < length Vs ∧ D1.N $$ (i,j) = 1}`.
- `block_mat_cond_rep'` (applied at `D2`, line 2033) rewrites the right side —
  the block `Bs' ! j` — into the same index set, now for `D2`. Between them,
  line 2031 uses `vslen mat_eq` to swap `D1.N` for `D2.N`.

Why each child is a good leaf. `block_mat_cond_rep'` is a one-line leaf whose
proof closes by `simp add: block_mat_cond_rep setcompr_eq_image` — it is just
the image form of the sibling lemma `block_mat_cond_rep` (shown as context),
restated so the parent can apply it directly; it contributes no new
mathematics. `block_mat_cond_rev` is self-contained: `intro Set.set_eqI iffI`
splits the set equality into two directions, each closed by a project lemma
already proved in the same file (`inc_matrix_point_in_block`,
`inc_matrix_point_in_block_one`), which themselves close on the `inc_mat_of`
definition. The two `fix j` subgoals inside the block half are not named
lemmas: they are the pointwise obligations the extensionality move creates.

The parent is then wrapped unchanged into `equal_inc_mat_isomorphism_ex`
(line 2042) and `equal_inc_mat_isomorphism_obtain` (line 2045); the converse
direction — an isomorphism implies some ordering with equal incidence matrices
— is `exists_eq_inc_mats` (line 2055), a separate locale.

## Why it is good

1. The parent lemma `equal_inc_mat_isomorphism` is declared in
   `thys/Fishers_Inequality/Incidence_Matrices.thy` in lines 1997-2040
   (`check`, `declared` form).
2. The parent's proof (the glue) cites the child `block_mat_cond_rev`
   (`check`, `cites` form).
3. The parent's proof (the glue) cites the child `block_mat_cond_rep'`
   (`check`, `cites` form).
4. The parent site (declaration plus proof) is 44 lines long — a measurement of
   the glue's size (`check`, `lines` form).
5. The decomposition has depth 3 below the main theorem:
   `equal_inc_mat_isomorphism` → `block_mat_cond_rev` →
   `inc_matrix_point_in_block` → `inc_matrix_point_not_in_block_zero`, all in
   the one file (`measurement`; the two `using` lines are cited in the claim's
   evidence).

In my opinion the detail worth copying is the pairing of one forward and one
reverse block-representation lemma: the pointwise step only works because both
sides of the equality can be rewritten to the *same* index-set form, so the
rest of the proof is a pure swap of `D1.N` for `D2.N`.

## When to use it, and when not

Use it when the goal is an equality of images — `image_mset f Bs = Bs'` or
`map f Bs = Bs'` — where each side can be rewritten to the same common
index-set form by one named lemma, so that the pointwise step closes by
rewriting alone. Avoid it when the two sides have different representations (a
set comprehension on one side and an image on the other) with no single lemma
bridging them, or when the equality is not an image-of-common-index equality,
so a case split or a different witness is needed. Also avoid it when the point
list is not distinct: the index step depends on `List_Index.index` being a
bijection between the point set and `{..<length Vs}` (from `D1.distinct`), so
duplicate points break the inversion.

## Consequences

The pointwise proof creates one obligation per block index `j` (the `fix j`
subgoal inside the `have "\<And> j. ..."`), plus a length-match obligation
(`len`) that `nth_equalityI` requires, and finally the lift from list equality
to multiset equality via `mset_map`. It relies on `List_Index.index` being a
bijection between the point set and `{..<length Vs}`, which needs the point
list to be distinct (`D1.distinct`); with duplicate points the index step no
longer inverts the block lookup. The move is only half of the locale: the point
bijection is a separate obligation closed by `bij_betw` facts, not by
extensionality.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: block_mat_cond_rev@thys/Fishers_Inequality/Incidence_Matrices.thy:2028, block_mat_cond_rep'@thys/Fishers_Inequality/Incidence_Matrices.thy:2033; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(equal_inc_mat_isomorphism, thys/Fishers_Inequality/Incidence_Matrices.thy, 1997-2040) -> declared: equal_inc_mat_isomorphism is declared at thys/Fishers_Inequality/Incidence_Matrices.thy:1997 | check_claims.py |
| 2 | verified | cites(parent, block_mat_cond_rev) -> cites: block_mat_cond_rev occurs at thys/Fishers_Inequality/Incidence_Matrices.thy:2028 | check_claims.py |
| 3 | verified | cites(parent, block_mat_cond_rep') -> cites: block_mat_cond_rep' occurs at thys/Fishers_Inequality/Incidence_Matrices.thy:2033 | check_claims.py |
| 4 | verified | lines(parent, 44) -> lines: site parent has 44 lines | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/isabelle-prover/mirror-afp-devel at commit `07cd9ca548d180f234c63f06bf5d1cb85c7fc5df`, under `BSD-3-Clause`; see the [source note](../../sources/afp/SOURCE.md) for the licence text and attribution.
