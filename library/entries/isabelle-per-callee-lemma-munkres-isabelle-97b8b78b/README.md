# One basis lemma per topology: box and product (Munkres Theorem 19.2)

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | isabelle |
| Status | draft |
| Source | [munkres-isabelle](../../sources/munkres-isabelle/SOURCE.md) at `90d108779e83` |
| Licence | `LicenseRef-unknown` |
| Licence recorded | 2026-11-14T10:44:24Z |

## Intent

Munkres Theorem 19.2 says two things at once: the box basis is a basis for
the box topology, and the product basis is a basis for the product topology.
The formalisation gives each half its own named lemma — `Theorem_19_2_box`
and `Theorem_19_2_product` — proved earlier in the same theory, so the parent
`Theorem_19_2` is just the two-conjunct wrapper that applies each lemma to the
shared hypothesis `hB` with one rule application per case.

## The decomposition

### parent `Theorem_19_2`: [`tst/i/Top1_Ch2.thy` lines 11382-11399](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/i/Top1_Ch2.thy#L11382-L11399) ([local copy](code/tst/i/Top1_Ch2.thy))

```isabelle
theorem Theorem_19_2:
  assumes hB: "\<forall>i\<in>I. basis_for (X i) (B i) (T i)"
  shows "basis_for (top1_PiE I X)
           {top1_PiE I U | U. \<forall>i\<in>I. U i \<in> B i}
           (top1_box_topology_on I X T)"
    and "basis_for (top1_PiE I X)
           {top1_PiE I U | U. (\<forall>i\<in>I. U i = X i \<or> U i \<in> B i) \<and> finite {i \<in> I. U i \<noteq> X i}}
           (top1_product_topology_on I X T)"
proof -
  show "basis_for (top1_PiE I X)
           {top1_PiE I U | U. \<forall>i\<in>I. U i \<in> B i}
           (top1_box_topology_on I X T)"
    by (rule Theorem_19_2_box[OF hB])
  show "basis_for (top1_PiE I X)
           {top1_PiE I U | U. (\<forall>i\<in>I. U i = X i \<or> U i \<in> B i) \<and> finite {i \<in> I. U i \<noteq> X i}}
           (top1_product_topology_on I X T)"
    by (rule Theorem_19_2_product[OF hB])
qed
```

### child `Theorem_19_2_box`: [`tst/i/Top1_Ch2.thy` lines 9286-9450](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/i/Top1_Ch2.thy#L9286-L9450) ([local copy](code/tst/i/Top1_Ch2.thy))

```isabelle
theorem Theorem_19_2_box:
  assumes hB: "\<forall>i\<in>I. basis_for (X i) (B i) (T i)"
  shows "basis_for (top1_PiE I X)
           {top1_PiE I U | U. \<forall>i\<in>I. U i \<in> B i}
           (top1_box_topology_on I X T)"
proof -
  define Cc where "Cc = {top1_PiE I U | U. \<forall>i\<in>I. U i \<in> B i}"

  have hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have hBi: "basis_for (X i) (B i) (T i)"
      using hB hi by blast
    show "is_topology_on (X i) (T i)"
      by (rule basis_for_is_topology_on[OF hBi])
  qed

  have hTopBox: "is_topology_on (top1_PiE I X) (top1_box_topology_on I X T)"
    by (rule top1_box_topology_on_is_topology_on[OF hTop])

  have hCcT: "Cc \<subseteq> top1_box_topology_on I X T"
  proof (rule subsetI)
    fix W assume hW: "W \<in> Cc"
    obtain U where hWdef: "W = top1_PiE I U" and hUiB: "\<forall>i\<in>I. U i \<in> B i"
      using hW unfolding Cc_def by blast

    have hUiT: "\<forall>i\<in>I. U i \<in> T i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hBi: "basis_for (X i) (B i) (T i)"
        using hB hi by blast
      show "U i \<in> T i"
        by (rule basis_elem_open_if_basis_for[OF hBi], rule hUiB[rule_format, OF hi])
    qed

    have hUiX: "\<forall>i\<in>I. U i \<subseteq> X i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hBi: "basis_for (X i) (B i) (T i)"
        using hB hi by blast
      have hBasis_i: "is_basis_on (X i) (B i)"
        using hBi unfolding basis_for_def by blast
      have hsub: "\<forall>b\<in>B i. b \<subseteq> X i"
        using hBasis_i unfolding is_basis_on_def by blast
      show "U i \<subseteq> X i"
        by (rule bspec[OF hsub], rule hUiB[rule_format, OF hi])
    qed

    have hUbox: "top1_PiE I U \<in> top1_box_basis_on I X T"
      unfolding top1_box_basis_on_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      using hUiT hUiX by blast

    have hBasisBox: "is_basis_on (top1_PiE I X) (top1_box_basis_on I X T)"
      by (rule top1_box_basis_is_basis_on[OF hTop])
    have hOpen: "top1_PiE I U \<in> top1_box_topology_on I X T"
      unfolding top1_box_topology_on_def
      by (rule basis_elem_open_in_generated_topology[OF hBasisBox hUbox])
    show "W \<in> top1_box_topology_on I X T"
      unfolding hWdef using hOpen by simp
  qed

  have hTX: "\<forall>U\<in>top1_box_topology_on I X T. U \<subseteq> top1_PiE I X"
    unfolding top1_box_topology_on_def topology_generated_by_basis_def by blast

  have hrefine:
    "\<And>U x. U \<in> top1_box_topology_on I X T \<Longrightarrow> x \<in> U \<Longrightarrow>
      \<exists>C\<in>Cc. C \<in> top1_box_topology_on I X T \<and> x \<in> C \<and> C \<subseteq> U"
  proof -
    fix U x
    assume hU: "U \<in> top1_box_topology_on I X T"
    assume hxU: "x \<in> U"

    have hxX: "x \<in> top1_PiE I X"
      using hTX hU hxU by blast

    have hUgen: "U \<in> topology_generated_by_basis (top1_PiE I X) (top1_box_basis_on I X T)"
      using hU unfolding top1_box_topology_on_def by simp
    have hcov: "\<forall>y\<in>U. \<exists>b\<in>top1_box_basis_on I X T. y \<in> b \<and> b \<subseteq> U"
      using hUgen unfolding topology_generated_by_basis_def by blast

    obtain b where hb: "b \<in> top1_box_basis_on I X T" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
      using hcov hxU by blast

    obtain U0 where hbdef: "b = top1_PiE I U0"
      and hU0: "\<forall>i\<in>I. U0 i \<in> T i \<and> U0 i \<subseteq> X i"
      using hb unfolding top1_box_basis_on_def by blast

    have hxU0: "\<forall>i\<in>I. x i \<in> U0 i"
      using hxb unfolding hbdef top1_PiE_iff by blast

    have hchoose: "\<forall>i\<in>I. \<exists>V. V \<in> B i \<and> x i \<in> V \<and> V \<subseteq> U0 i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hBi: "basis_for (X i) (B i) (T i)"
        using hB hi by blast
	      have hU0i: "U0 i \<in> T i"
	        using hU0 hi by blast
	      have hxi: "x i \<in> U0 i"
	        using hxU0 hi by blast
	      show "\<exists>V. V \<in> B i \<and> x i \<in> V \<and> V \<subseteq> U0 i"
	      proof -
	        have hTeq: "T i = topology_generated_by_basis (X i) (B i)"
	          using hBi unfolding basis_for_def by blast
	        have hU0gen: "U0 i \<in> topology_generated_by_basis (X i) (B i)"
	          using hU0i unfolding hTeq by simp
	        have hcov: "\<forall>y\<in>U0 i. \<exists>b\<in>B i. y \<in> b \<and> b \<subseteq> U0 i"
	          using hU0gen unfolding topology_generated_by_basis_def by blast
	        obtain V where hV: "V \<in> B i" and hxV: "x i \<in> V" and hVsub: "V \<subseteq> U0 i"
	          using hcov hxi by blast
	        show ?thesis
	          using hV hxV hVsub by blast
	      qed
	    qed
	
	    obtain V where hV: "\<forall>i\<in>I. V i \<in> B i \<and> x i \<in> V i \<and> V i \<subseteq> U0 i"
	      using bchoice[OF hchoose] by blast

    have hCmem: "top1_PiE I V \<in> Cc"
      unfolding Cc_def
      apply (rule CollectI)
      apply (rule exI[where x=V])
      using hV by blast

    have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
      using hxX unfolding top1_PiE_iff by blast
    have hxV: "\<forall>i\<in>I. x i \<in> V i"
      using hV by blast
    have hxC: "x \<in> top1_PiE I V"
      unfolding top1_PiE_iff using hxV hxext by blast

    have hVsub: "\<forall>i\<in>I. V i \<subseteq> U0 i"
      using hV by blast
    have hCsub_b: "top1_PiE I V \<subseteq> top1_PiE I U0"
      by (rule top1_PiE_mono[OF hVsub])
    have hCsubU: "top1_PiE I V \<subseteq> U"
      using hCsub_b hbdef hbU by blast

    have hCopen: "top1_PiE I V \<in> top1_box_topology_on I X T"
      using hCcT hCmem by blast

    show "\<exists>C\<in>Cc. C \<in> top1_box_topology_on I X T \<and> x \<in> C \<and> C \<subseteq> U"
      apply (rule bexI[where x="top1_PiE I V"])
       apply (intro conjI)
         apply (rule hCopen)
        apply (rule hxC)
       apply (rule hCsubU)
      apply (rule hCmem)
      done
  qed

	  have hBF: "basis_for (top1_PiE I X) Cc (top1_box_topology_on I X T)"
	    apply (rule Lemma_13_2)
	       apply (rule hTopBox)
	      apply (rule hCcT)
	     apply (rule hTX)
	    apply (rule hrefine)
	     apply assumption
	    apply assumption
	    done

  show ?thesis
    by (rule hBF[unfolded Cc_def])
qed
```

### child `Theorem_19_2_product`: [`tst/i/Top1_Ch2.thy` lines 9452-9743](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/i/Top1_Ch2.thy#L9452-L9743) ([local copy](code/tst/i/Top1_Ch2.thy))

```isabelle
theorem Theorem_19_2_product:
  assumes hB: "\<forall>i\<in>I. basis_for (X i) (B i) (T i)"
  shows "basis_for (top1_PiE I X)
           {top1_PiE I U | U. (\<forall>i\<in>I. U i = X i \<or> U i \<in> B i) \<and> finite {i \<in> I. U i \<noteq> X i}}
           (top1_product_topology_on I X T)"
proof -
  define Cc where
    "Cc = {top1_PiE I U | U. (\<forall>i\<in>I. U i = X i \<or> U i \<in> B i) \<and> finite {i \<in> I. U i \<noteq> X i}}"

  have hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have hBi: "basis_for (X i) (B i) (T i)"
      using hB hi by blast
    show "is_topology_on (X i) (T i)"
      by (rule basis_for_is_topology_on[OF hBi])
  qed

  have hTopProd: "is_topology_on (top1_PiE I X) (top1_product_topology_on I X T)"
    by (rule top1_product_topology_on_is_topology_on[OF hTop])

  have hCcT: "Cc \<subseteq> top1_product_topology_on I X T"
  proof (rule subsetI)
    fix W assume hW: "W \<in> Cc"
    obtain U where hWdef: "W = top1_PiE I U"
      and hUiB: "(\<forall>i\<in>I. U i = X i \<or> U i \<in> B i)"
      and hfin: "finite {i \<in> I. U i \<noteq> X i}"
      using hW unfolding Cc_def by blast

    have hUiT: "\<forall>i\<in>I. U i \<in> T i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hBi: "basis_for (X i) (B i) (T i)"
        using hB hi by blast
      have hTopi: "is_topology_on (X i) (T i)"
        using hTop hi by blast
      have hXi: "X i \<in> T i"
        using hTopi unfolding is_topology_on_def by blast
      show "U i \<in> T i"
      proof (cases "U i = X i")
        case True
        show ?thesis
          unfolding True using hXi by simp
      next
        case False
        have hUiBi: "U i \<in> B i"
          using hUiB hi False by blast
        show ?thesis
          by (rule basis_elem_open_if_basis_for[OF hBi hUiBi])
      qed
    qed

    have hUiX: "\<forall>i\<in>I. U i \<subseteq> X i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      show "U i \<subseteq> X i"
      proof (cases "U i = X i")
        case True
        show ?thesis
          unfolding True by simp
      next
        case False
        have hBi: "basis_for (X i) (B i) (T i)"
          using hB hi by blast
        have hBasis_i: "is_basis_on (X i) (B i)"
          using hBi unfolding basis_for_def by blast
        have hsub: "\<forall>b\<in>B i. b \<subseteq> X i"
          using hBasis_i unfolding is_basis_on_def by blast
        have hUiBi: "U i \<in> B i"
          using hUiB hi False by blast
        show ?thesis
          by (rule bspec[OF hsub hUiBi])
      qed
    qed

    have hUprod: "top1_PiE I U \<in> top1_product_basis_on I X T"
      unfolding top1_product_basis_on_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      using hUiT hUiX hfin by blast

    have hBasisProd: "is_basis_on (top1_PiE I X) (top1_product_basis_on I X T)"
      by (rule top1_product_basis_is_basis_on[OF hTop])
    have hOpen: "top1_PiE I U \<in> top1_product_topology_on I X T"
      unfolding top1_product_topology_on_def
      by (rule basis_elem_open_in_generated_topology[OF hBasisProd hUprod])

    show "W \<in> top1_product_topology_on I X T"
      unfolding hWdef using hOpen by simp
  qed

  have hTX: "\<forall>U\<in>top1_product_topology_on I X T. U \<subseteq> top1_PiE I X"
    unfolding top1_product_topology_on_def topology_generated_by_basis_def by blast

  have hrefine:
    "\<And>U x. U \<in> top1_product_topology_on I X T \<Longrightarrow> x \<in> U \<Longrightarrow>
      \<exists>C\<in>Cc. C \<in> top1_product_topology_on I X T \<and> x \<in> C \<and> C \<subseteq> U"
  proof -
    fix U x
    assume hU: "U \<in> top1_product_topology_on I X T"
    assume hxU: "x \<in> U"

    have hxX: "x \<in> top1_PiE I X"
      using hTX hU hxU by blast

    have hUgen:
      "U \<in> topology_generated_by_basis (top1_PiE I X) (top1_product_basis_on I X T)"
      using hU unfolding top1_product_topology_on_def by simp
    have hcov:
      "\<forall>y\<in>U. \<exists>b\<in>top1_product_basis_on I X T. y \<in> b \<and> b \<subseteq> U"
      using hUgen unfolding topology_generated_by_basis_def by blast

    obtain b where hb: "b \<in> top1_product_basis_on I X T" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
      using hcov hxU by blast

    obtain U0 where hbdef: "b = top1_PiE I U0"
      and hU0: "(\<forall>i\<in>I. U0 i \<in> T i \<and> U0 i \<subseteq> X i)"
      and hfin0: "finite {i \<in> I. U0 i \<noteq> X i}"
      using hb unfolding top1_product_basis_on_def by blast

    define S where "S = {i \<in> I. U0 i \<noteq> X i}"
    have hSfin: "finite S"
      using hfin0 unfolding S_def by simp

    have hxU0: "\<forall>i\<in>I. x i \<in> U0 i"
      using hxb unfolding hbdef top1_PiE_iff by blast

    have hchoose: "\<forall>i\<in>S. \<exists>V. V \<in> B i \<and> x i \<in> V \<and> V \<subseteq> U0 i"
    proof (intro ballI)
      fix i assume hiS: "i \<in> S"
      have hi: "i \<in> I"
        using hiS unfolding S_def by blast
      have hBi: "basis_for (X i) (B i) (T i)"
        using hB hi by blast
      have hU0i: "U0 i \<in> T i"
        using hU0 hi by blast
      have hxi: "x i \<in> U0 i"
        using hxU0 hi by blast

      (* unfold continuity in the topology generated by a basis to obtain a basis element around x i *)
      have hTeq: "T i = topology_generated_by_basis (X i) (B i)"
        using hBi unfolding basis_for_def by blast
      have hU0gen: "U0 i \<in> topology_generated_by_basis (X i) (B i)"
        using hU0i unfolding hTeq by simp
      have hcov': "\<forall>y\<in>U0 i. \<exists>b\<in>B i. y \<in> b \<and> b \<subseteq> U0 i"
        using hU0gen unfolding topology_generated_by_basis_def by blast
      obtain V where hV: "V \<in> B i" and hxV: "x i \<in> V" and hVsub: "V \<subseteq> U0 i"
        using hcov' hxi by blast
      show "\<exists>V. V \<in> B i \<and> x i \<in> V \<and> V \<subseteq> U0 i"
        using hV hxV hVsub by blast
    qed

    obtain W where hW: "\<forall>i\<in>S. W i \<in> B i \<and> x i \<in> W i \<and> W i \<subseteq> U0 i"
      using bchoice[OF hchoose] by blast

    define V where "V = (\<lambda>i. if i \<in> S then W i else X i)"

    have hV_prop: "(\<forall>i\<in>I. V i = X i \<or> V i \<in> B i) \<and> finite {i \<in> I. V i \<noteq> X i}"
    proof (intro conjI)
      show "\<forall>i\<in>I. V i = X i \<or> V i \<in> B i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        show "V i = X i \<or> V i \<in> B i"
        proof (cases "i \<in> S")
          case True
          have "V i = W i"
            unfolding V_def using True by simp
          moreover have "W i \<in> B i"
            using hW True by blast
          ultimately show ?thesis
            by simp
        next
          case False
          have "V i = X i"
            unfolding V_def using False by simp
          thus ?thesis
            by simp
        qed
      qed

      have "{i \<in> I. V i \<noteq> X i} \<subseteq> S"
      proof (rule subsetI)
        fix i assume hi: "i \<in> {i \<in> I. V i \<noteq> X i}"
        have hiI: "i \<in> I" and hneq: "V i \<noteq> X i"
          using hi by blast+
        have "i \<in> S"
        proof (rule ccontr)
          assume hin: "i \<notin> S"
          have "V i = X i"
            unfolding V_def using hin by simp
          thus False
            using hneq by contradiction
        qed
        thus "i \<in> S" .
      qed
      thus "finite {i \<in> I. V i \<noteq> X i}"
        using hSfin finite_subset by blast
    qed

    have hCmem: "top1_PiE I V \<in> Cc"
      unfolding Cc_def
      apply (rule CollectI)
      apply (rule exI[where x=V])
      using hV_prop by blast

    have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
      using hxX unfolding top1_PiE_iff by blast
    have hxV: "\<forall>i\<in>I. x i \<in> V i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      show "x i \<in> V i"
      proof (cases "i \<in> S")
        case True
        have "V i = W i"
          unfolding V_def using True by simp
        moreover have "x i \<in> W i"
          using hW True by blast
        ultimately show ?thesis
          by simp
      next
        case False
        have "V i = X i"
          unfolding V_def using False by simp
        moreover have "x i \<in> X i"
          using hxX hi unfolding top1_PiE_iff by blast
        ultimately show ?thesis
          by simp
      qed
    qed
    have hxC: "x \<in> top1_PiE I V"
      unfolding top1_PiE_iff using hxV hxext by blast

    have hVsub: "\<forall>i\<in>I. V i \<subseteq> U0 i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      show "V i \<subseteq> U0 i"
      proof (cases "i \<in> S")
        case True
        have "V i = W i"
          unfolding V_def using True by simp
        moreover have "W i \<subseteq> U0 i"
          using hW True by blast
        ultimately show ?thesis
          by simp
      next
        case False
        have hU0eq: "U0 i = X i"
        proof -
          have "i \<notin> {i \<in> I. U0 i \<noteq> X i}"
            using False unfolding S_def by simp
          hence "\<not> (U0 i \<noteq> X i)"
            using hi by blast
          thus ?thesis by simp
        qed
        have "V i = X i"
          unfolding V_def using False by simp
        thus ?thesis
          unfolding hU0eq by simp
      qed
    qed

    have hCsub_b: "top1_PiE I V \<subseteq> top1_PiE I U0"
      by (rule top1_PiE_mono[OF hVsub])
    have hCsubU: "top1_PiE I V \<subseteq> U"
      using hCsub_b hbdef hbU by blast

    have hCopen: "top1_PiE I V \<in> top1_product_topology_on I X T"
      using hCcT hCmem by blast

    show "\<exists>C\<in>Cc. C \<in> top1_product_topology_on I X T \<and> x \<in> C \<and> C \<subseteq> U"
      apply (rule bexI[where x="top1_PiE I V"])
       apply (intro conjI)
         apply (rule hCopen)
        apply (rule hxC)
       apply (rule hCsubU)
      apply (rule hCmem)
      done
  qed

  have hBF: "basis_for (top1_PiE I X) Cc (top1_product_topology_on I X T)"
    apply (rule Lemma_13_2)
       apply (rule hTopProd)
      apply (rule hCcT)
     apply (rule hTX)
    apply (rule hrefine)
     apply assumption
    apply assumption
    done

  show ?thesis
    by (rule hBF[unfolded Cc_def])
qed
```

### context `Lemma_13_2`: [`tst/i/Top1_Ch2.thy` lines 1257-1364](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/i/Top1_Ch2.thy#L1257-L1364) ([local copy](code/tst/i/Top1_Ch2.thy))

```isabelle
theorem Lemma_13_2:
  assumes hT: "is_topology_on X T"
  assumes hCcT: "Cc \<subseteq> T"
  assumes hTX: "\<forall>U\<in>T. U \<subseteq> X"
  assumes hrefine: "\<And>U x. U \<in> T \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>C\<in>Cc. C \<in> T \<and> x \<in> C \<and> C \<subseteq> U"
  shows "basis_for X Cc T"
proof -
  have hXT: "X \<in> T"
    by (rule conjunct1[OF conjunct2[OF hT[unfolded is_topology_on_def]]])
  have hunion: "\<forall>U. U \<subseteq> T \<longrightarrow> \<Union>U \<in> T"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  have hinter: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> T \<longrightarrow> \<Inter>F \<in> T"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  have hbas: "is_basis_on X Cc"
  proof -
    have hc_sub: "\<forall>c\<in>Cc. c \<subseteq> X"
    proof (rule ballI)
      fix c assume hc: "c \<in> Cc"
      have hcT: "c \<in> T" using hCcT hc by blast
      show "c \<subseteq> X" using hTX hcT by blast
    qed
    have hcov: "\<forall>x\<in>X. \<exists>c\<in>Cc. x \<in> c"
    proof (rule ballI)
      fix x assume hxX: "x \<in> X"
      obtain C where hCCc: "C \<in> Cc" and hxC: "x \<in> C"
        using hrefine[OF hXT hxX] by blast
      show "\<exists>c\<in>Cc. x \<in> c" using hCCc hxC by blast
    qed
    have hinter_cond: "\<forall>c1\<in>Cc. \<forall>c2\<in>Cc. \<forall>y\<in>(c1 \<inter> c2). \<exists>c3\<in>Cc. y \<in> c3 \<and> c3 \<subseteq> (c1 \<inter> c2)"
    proof (intro ballI)
      fix c1 c2 assume hc1: "c1 \<in> Cc" and hc2: "c2 \<in> Cc"
      fix y assume hy: "y \<in> c1 \<inter> c2"
      have hc1T: "c1 \<in> T" using hCcT hc1 by blast
      have hc2T: "c2 \<in> T" using hCcT hc2 by blast
      have hc12T: "c1 \<inter> c2 \<in> T"
      proof -
        have hF: "{c1, c2} \<subseteq> T" using hc1T hc2T by blast
        have hIT: "\<Inter>{c1, c2} \<in> T"
          apply (rule hinter[rule_format])
          apply (intro conjI)
            apply simp
           apply (rule insert_not_empty)
          apply (rule hF)
          done
        show "c1 \<inter> c2 \<in> T" using hIT by simp
      qed
      obtain C where hCCc: "C \<in> Cc" and hyC: "y \<in> C" and hCsub: "C \<subseteq> c1 \<inter> c2"
        using hrefine[OF hc12T hy] by blast
      show "\<exists>c3\<in>Cc. y \<in> c3 \<and> c3 \<subseteq> c1 \<inter> c2" using hCCc hyC hCsub by blast
    qed
    show "is_basis_on X Cc"
      unfolding is_basis_on_def
      apply (intro conjI)
        apply (rule hc_sub)
       apply (rule hcov)
      apply (rule hinter_cond)
      done
  qed
  have hTeq: "T = topology_generated_by_basis X Cc"
  proof (rule set_eqI)
    fix W
    show "W \<in> T \<longleftrightarrow> W \<in> topology_generated_by_basis X Cc"
    proof (rule iffI)
      assume hWT: "W \<in> T"
      show "W \<in> topology_generated_by_basis X Cc"
        unfolding topology_generated_by_basis_def
      proof (rule CollectI, rule conjI)
        show "W \<subseteq> X" using hTX hWT by blast
      next
        show "\<forall>x\<in>W. \<exists>c\<in>Cc. x \<in> c \<and> c \<subseteq> W"
        proof (rule ballI)
          fix x assume hxW: "x \<in> W"
          obtain C where hCCc: "C \<in> Cc" and hxC: "x \<in> C" and hCW: "C \<subseteq> W"
            using hrefine[OF hWT hxW] by blast
          show "\<exists>c\<in>Cc. x \<in> c \<and> c \<subseteq> W" using hCCc hxC hCW by blast
        qed
      qed
    next
      assume hWtgb: "W \<in> topology_generated_by_basis X Cc"
      have hWcov: "\<forall>x\<in>W. \<exists>c\<in>Cc. x \<in> c \<and> c \<subseteq> W"
        using hWtgb unfolding topology_generated_by_basis_def by blast
      have hWeq: "W = \<Union>{C \<in> Cc. C \<subseteq> W}"
      proof (rule set_eqI)
        fix z
        show "z \<in> W \<longleftrightarrow> z \<in> \<Union>{C \<in> Cc. C \<subseteq> W}"
        proof (rule iffI)
          assume hzW: "z \<in> W"
          obtain C where hCCc: "C \<in> Cc" and hzC: "z \<in> C" and hCW: "C \<subseteq> W"
            using hWcov[rule_format, OF hzW] by blast
          show "z \<in> \<Union>{C \<in> Cc. C \<subseteq> W}" using hCCc hzC hCW by blast
        next
          assume hz: "z \<in> \<Union>{C \<in> Cc. C \<subseteq> W}"
          obtain C where hCmem: "C \<in> {C \<in> Cc. C \<subseteq> W}" and hzC: "z \<in> C" using hz by blast
          show "z \<in> W" using hzC hCmem by blast
        qed
      qed
      have hsubT: "{C \<in> Cc. C \<subseteq> W} \<subseteq> T" using hCcT by blast
      have hbigT: "\<Union>{C \<in> Cc. C \<subseteq> W} \<in> T" using hunion[rule_format, OF hsubT] by blast
      show "W \<in> T" using hWeq hbigT by simp
    qed
  qed
  show "basis_for X Cc T"
    unfolding basis_for_def
    apply (intro conjI)
     apply (rule hbas)
    apply (rule hTeq)
    done
qed
```

How the parts fit. The parent `Theorem_19_2` is a conjunction of two
obligations, one per topology constructor, and its proof is two `show` blocks,
each a single `by (rule …[OF hB])` that discharges one conjunct by the matching
per-topology lemma:

```
Theorem_19_2 (parent, 11382-11399)
├─ box conjunct      → Theorem_19_2_box (9286-9450)     [line 11394]
└─ product conjunct  → Theorem_19_2_product (9452-9743) [line 11398]
    Theorem_19_2_box     ──uses── Lemma_13_2 (9439)
    Theorem_19_2_product ──uses── Lemma_13_2 (9732)
    Lemma_13_2 (1257-1364) closes by unfolding the topology/basis definitions alone
```

Each child is a good leaf: a self-contained `theorem … qed` whose proof closes
on its own and never cites its sibling or the parent. `Theorem_19_2_box`
assembles the four ingredients Munkres Lemma 13.2 needs — the topology is a
topology (`hTopBox`), the candidate collection lies inside it (`hCcT`), its
elements cover the carrier (`hTX`), and it refines any open set (`hrefine`) —
and then applies `Lemma_13_2` (line 9439) to conclude `basis_for … Cc …`,
finally unfolding `Cc`. `Theorem_19_2_product` is the same shape; the extra
finite-support condition of the product basis is absorbed entirely inside the
lemma (its `hrefine` builds the finite set `S` and the choice `V`), so the
parent never has to see it. `Lemma_13_2` is the shared leaf at depth 2: it
packs Munkres Lemma 13.2 (a collection is a basis for `T` iff it is open,
covers `X`, and refines intersections) and closes purely by unfolding
`is_topology_on_def`, `is_basis_on_def` and `topology_generated_by_basis_def`,
citing no further project lemma.

## Why it is good

1. `Theorem_19_2_box` occurs in the parent site, at line 11394, as the sole
   step of the box-topology `show` block
   (`check`, [lines 11382-11399](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/i/Top1_Ch2.thy#L11382-L11399)).
2. `Theorem_19_2_product` occurs in the parent site, at line 11398, as the sole
   step of the product-topology `show` block (`check`, same lines).
3. The box child closes by the shared lemma: `Lemma_13_2` occurs at line 9439
   of `Theorem_19_2_box`'s site, and likewise at line 9732 of
   `Theorem_19_2_product`'s site, so the per-topology split reduces two
   near-identical proofs to one shared leaf (`check`,
   [lines 9286-9450](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/i/Top1_Ch2.thy#L9286-L9450)).
4. The shape is a measurement: an 18-line parent whose proof body is two rule
   applications delegates 457 lines to the two children — `Theorem_19_2_box`
   is 165 lines (9286-9450) and `Theorem_19_2_product` is 292 lines
   (9452-9743) (`measurement`, line counts at the pinned commit).
5. The pairing is the file's convention for the whole of §19: `Theorem_19_3`
   (11401-11415), `Theorem_19_4` (11417-11426) and `Theorem_19_5`
   (11428-11442) each repeat the one-box-plus-one-product conjunction wrapper,
   closed by `by (rule Theorem_19_N_box[OF …])` and
   `by (rule Theorem_19_N_product[OF …])` (`known-use`,
   [lines 11401-11442](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/i/Top1_Ch2.thy#L11401-L11442)).

In my opinion the detail worth copying is the wrapper-plus-family shape, not
any single theorem: because the box and product lemmas carry exactly the same
`assumes`, the parent collapses to two `[OF hB]` applications, and adding a new
construction to the family is a matter of adding one more named lemma and one
more `show`. The source file is sorry-free in this region (the two children and
`Lemma_13_2` contain no `sorry`/`oops`/`admit`).

## When to use it, and when not

Use it when a theorem is naturally a family of near-identical statements over
a set of constructions — the box and product topologies here, the passes of a
compiler, the components of a `crunch` run — and each member's proof is long
enough to deserve its own lemma. The wrapper pattern pays off because the
members share one hypothesis context, so the parent becomes one rule
application per member and each member can be proved, checked and reused
independently.

Avoid it when the members share a substantial common sub-proof: factor that
sub-proof into its own shared lemma first (here `Lemma_13_2`), or the two
lemmas will duplicate it. Avoid it also when the cases are short enough that
a single `intro conjI` with two in-place proofs is clearer than two named
lemmas, or when the members do not share a hypothesis context, so the parent
cannot instantiate them uniformly with one `[OF hB]` each.

## Consequences

The move creates one named obligation per construction, each of which must
restate the shared hypotheses exactly (both children carry the same
`assumes hB: ∀i∈I. basis_for (X i) (B i) (T i)`), so a child that adds, drops
or reorders a hypothesis breaks the parent's one-line `[OF hB]`. The parent
adds no content beyond the rule applications, so a child whose statement
drifts from the parent's conjunct fails silently at the parent, not at the
child. The children are independent of each other but both depend on
`Lemma_13_2`, so a defect in that shared leaf breaks both at once. The
exhaustiveness of the conjunction is not a separate obligation here: Isabelle
treats `shows "…" and "…"` as two goals, and the two `show` blocks cover both,
so a missing case would leave an unproved goal rather than a silent gap.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Theorem_19_2_box@tst/i/Top1_Ch2.thy:11394, Theorem_19_2_product@tst/i/Top1_Ch2.thy:11398; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, Theorem_19_2_box) -> cites: Theorem_19_2_box occurs at tst/i/Top1_Ch2.thy:11394 | check_claims.py |
| 2 | verified | cites(parent, Theorem_19_2_product) -> cites: Theorem_19_2_product occurs at tst/i/Top1_Ch2.thy:11398 | check_claims.py |
| 3 | verified | cites(tst/i/Top1_Ch2.thy:9286-9450, Lemma_13_2) -> cites: Lemma_13_2 occurs at tst/i/Top1_Ch2.thy:9439 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/JUrban/isa_top_autoform1 at commit `90d108779e83453e9cae2f55b513246e1cc044e0`, under `LicenseRef-unknown`; see the [source note](../../sources/munkres-isabelle/SOURCE.md) for the licence text and attribution.
