# Extract normality and G-delta halves of Munkres Lemma 40.1 into named step lemmas (Nagata-Smirnov)

| | |
|---|---|
| Kind | instance |
| Move | extract-have |
| Language | isabelle |
| Status | draft |
| Source | [munkres-isabelle](../../sources/munkres-isabelle/SOURCE.md) at `90d108779e83` |
| Licence | `LicenseRef-unknown` |

## Intent

Reduce Munkres Lemma 40.1 — *regular with a sigma-locally-finite basis implies
normal and every closed set is G-delta* — to two named step lemmas whose proofs
were lifted out of the conjunction. `Lemma_40_1_step3` proves the normality
half and `Lemma_40_1_step2` the G-delta half, so the parent closes in four
lines by applying both to the shared `hReg`/`hBasis`/`hCLF` context and letting
`argo` assemble the conjunction.

## The decomposition

### parent `Lemma_40_1`: [`tst/Top1_Ch5_8.thy` lines 5064-5072](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L5064-L5072) ([local copy](code/tst/Top1_Ch5_8.thy))

```isabelle
lemma Lemma_40_1:
  assumes hReg: "top1_regular_on X TX"
  assumes hBasis: "basis_for X \<B> TX"
  assumes hCLF: "top1_sigma_locally_finite_family_on X TX \<B>"
  shows "top1_normal_on X TX \<and> (\<forall>A. closedin_on X TX A \<longrightarrow> top1_G_delta_on X TX A)"
  using Lemma_40_1_step3[OF hReg hBasis hCLF]
        Lemma_40_1_step2[OF hReg hBasis hCLF]
  
  by argo
```

### child `Lemma_40_1_step2`: [`tst/Top1_Ch5_8.thy` lines 4626-4704](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L4626-L4704) ([local copy](code/tst/Top1_Ch5_8.thy))

```isabelle
lemma Lemma_40_1_step2:
  assumes hReg: "top1_regular_on X TX"
  assumes hBasis: "basis_for X \<B> TX"
  assumes hCLF: "top1_sigma_locally_finite_family_on X TX \<B>"
  assumes hClosed: "closedin_on X TX A"
  shows "top1_G_delta_on X TX A"
proof -
  have hTop: "is_topology_on X TX"
    using hReg unfolding top1_regular_on_def top1_T1_on_def
    
    by satx
  have hAX: "A \<subseteq> X"
    using hClosed unfolding closedin_on_def
    
    by presburger
  define W where "W = X - A"
  have hWopen: "W \<in> TX"
    using hClosed unfolding closedin_on_def W_def
    
    by presburger
  obtain U :: "nat \<Rightarrow> 'a set" where hUopen: "\<forall>n. U n \<in> TX"
    and hUcl: "\<forall>n. closure_on X TX (U n) \<subseteq> W"
    and hWeq: "W = (\<Union>n. U n)"
    using Lemma_40_1_step1[OF hReg hBasis hCLF hWopen]
    by metis
  text \<open>A = \<Inter>n. (X - cl(U n))\<close>
  define V where "V n = X - closure_on X TX (U n)" for n
  have hVopen: "\<forall>n. V n \<in> TX"
  proof (intro allI)
    fix n
    have hUnX: "U n \<subseteq> X"
      using hUcl hUopen W_def
      
      using subset_closure_on by fastforce
    have hcl: "closedin_on X TX (closure_on X TX (U n))"
      using hTop hUnX closure_on_closed
      
      by blast
    show "V n \<in> TX"
      using hcl unfolding V_def closedin_on_def
      
      by presburger
  qed
  have hAeq: "A = (\<Inter>n. V n)"
  proof -
    have "W = (\<Union>n. closure_on X TX (U n))"
    proof (rule equalityI)
      show "W \<subseteq> (\<Union>n. closure_on X TX (U n))"
        unfolding hWeq using subset_closure_on
        
        by fast
      show "(\<Union>n. closure_on X TX (U n)) \<subseteq> W"
        using hUcl
        
        by blast
    qed
    then have "X - W = (\<Inter>n. X - closure_on X TX (U n))"
      
      by blast
    then show ?thesis
      unfolding V_def W_def using hAX
      
      by blast
  qed
  show ?thesis
    unfolding top1_G_delta_on_def
  proof (intro conjI)
    show "A \<subseteq> X" by (rule hAX)
    have hex: "(\<forall>n. V n \<in> TX) \<and> A = (\<Inter>n. V n)"
      using hVopen hAeq
      
      by presburger
    show "\<exists>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX) \<and> A = (\<Inter>n. U n)"
      apply (rule exI[where x=V])
      using hex
      
      by satx
  qed
qed
```

### child `Lemma_40_1_step3`: [`tst/Top1_Ch5_8.thy` lines 4756-5062](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L4756-L5062) ([local copy](code/tst/Top1_Ch5_8.thy))

```isabelle
lemma Lemma_40_1_step3:
  assumes hReg: "top1_regular_on X TX"
  assumes hBasis: "basis_for X \<B> TX"
  assumes hCLF: "top1_sigma_locally_finite_family_on X TX \<B>"
  shows "top1_normal_on X TX"
proof -
  have hTop: "is_topology_on X TX"
    using hReg unfolding top1_regular_on_def top1_T1_on_def
    
    by linarith
  have hT1: "top1_T1_on X TX"
    using hReg unfolding top1_regular_on_def
    
    by presburger
  show ?thesis
    unfolding top1_normal_on_def
  proof (intro conjI allI impI)
    show "top1_T1_on X TX" by (rule hT1)
  next
    fix C D
    assume hCD: "closedin_on X TX C \<and> closedin_on X TX D \<and> C \<inter> D = {}"
    have hCcl: "closedin_on X TX C" using hCD
      
      by presburger
    have hDcl: "closedin_on X TX D" using hCD
      
      by presburger
    have hdisj: "C \<inter> D = {}" using hCD
      
      by presburger
    have hCX: "C \<subseteq> X" using hCcl unfolding closedin_on_def
      
      by presburger
    have hDX: "D \<subseteq> X" using hDcl unfolding closedin_on_def
      
      by presburger

    text \<open>X-D is open, apply step1 to get {U_n} covering C with cl(U_n) ⊆ X-D.\<close>
    have hXmD_open: "X - D \<in> TX" using hDcl unfolding closedin_on_def
      
      by presburger
    have hex_U: "\<exists>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX) \<and> (\<forall>n. closure_on X TX (U n) \<subseteq> X - D) \<and> X - D = (\<Union>n. U n)"
      by (rule Lemma_40_1_step1[OF hReg hBasis hCLF hXmD_open])
    obtain Ufn :: "nat \<Rightarrow> 'a set" where hUopen: "\<forall>n. Ufn n \<in> TX"
      and hUcl: "\<forall>n. closure_on X TX (Ufn n) \<subseteq> X - D"
      and hXmD_eq: "X - D = (\<Union>n. Ufn n)"
      using hex_U
      
      by blast

    text \<open>Similarly for X-C.\<close>
    have hXmC_open: "X - C \<in> TX" using hCcl unfolding closedin_on_def
      
      by linarith
    have hex_V: "\<exists>V::nat \<Rightarrow> 'a set. (\<forall>n. V n \<in> TX) \<and> (\<forall>n. closure_on X TX (V n) \<subseteq> X - C) \<and> X - C = (\<Union>n. V n)"
      by (rule Lemma_40_1_step1[OF hReg hBasis hCLF hXmC_open])
    obtain Vn :: "nat \<Rightarrow> 'a set" where hVopen: "\<forall>n. Vn n \<in> TX"
      and hVcl: "\<forall>n. closure_on X TX (Vn n) \<subseteq> X - C"
      and hXmC_eq: "X - C = (\<Union>n. Vn n)"
      using hex_V
      
      by blast

    text \<open>U_n covers C (since C ⊆ X-D = ∪U_n). V_n covers D.\<close>
    have hC_sub_Un: "C \<subseteq> (\<Union>n. Ufn n)"
      using hXmD_eq hdisj hCX
      
      by auto
    have hD_sub_Vn: "D \<subseteq> (\<Union>n. Vn n)"
      using hXmC_eq hdisj hDX
      
      by blast

    text \<open>Construct U'_n = U_n - ∪{cl(V_i) | i ≤ n}, V'_n = V_n - ∪{cl(U_i) | i ≤ n}.\<close>
    define U' where "U' (n::nat) = Ufn n - (\<Union> (closure_on X TX ` Vn ` {0..n}))" for n
    define V' where "V' (n::nat) = Vn n - (\<Union> (closure_on X TX ` Ufn ` {0..n}))" for n

    text \<open>U' = ∪U'_n and V' = ∪V'_n.\<close>
    define UU where "UU = (\<Union>n. U' n)"
    define VV where "VV = (\<Union>n. V' n)"

    text \<open>U'_n are open (Ufn n open minus finite union of closed = open).\<close>
    have hU'open: "\<forall>n. U' n \<in> TX"
    proof (intro allI)
      fix n
      have hclVn_closed: "\<forall>i. closedin_on X TX (closure_on X TX (Vn i))"
      proof (intro allI)
        fix i
        have "Vn i \<subseteq> X"
          using hVopen hBasis unfolding basis_for_def topology_generated_by_basis_def
          
          by blast
        then show "closedin_on X TX (closure_on X TX (Vn i))"
          using hTop
          
          by (metis hTop closure_on_closed)
      qed
      have hfinite_union_closed: "closedin_on X TX (\<Union> (closure_on X TX ` Vn ` {0..n}))"
        using closedin_on_finite_Union[OF hTop] hclVn_closed
        
        by simp
      have hcomplement_open: "X - (\<Union> (closure_on X TX ` Vn ` {0..n})) \<in> TX"
        using hfinite_union_closed unfolding closedin_on_def
        
        by presburger
      have hUfnX: "Ufn n \<subseteq> X"
        using hUopen hBasis unfolding basis_for_def topology_generated_by_basis_def
        
        by blast
      have hU'eq: "U' n = Ufn n \<inter> (X - (\<Union> (closure_on X TX ` Vn ` {0..n})))"
        unfolding U'_def using hUfnX
        
        by fast
      show "U' n \<in> TX"
        unfolding hU'eq
        using topology_inter2[OF hTop hUopen[rule_format, of n] hcomplement_open]
        
        by presburger
    qed
    have hV'open: "\<forall>n. V' n \<in> TX"
    proof (intro allI)
      fix n
      have hclUfn_closed: "\<forall>i. closedin_on X TX (closure_on X TX (Ufn i))"
      proof (intro allI)
        fix i
        have "Ufn i \<subseteq> X"
          using hUopen hBasis unfolding basis_for_def topology_generated_by_basis_def
          
          by blast
        then show "closedin_on X TX (closure_on X TX (Ufn i))"
          using hTop
          
          by (metis hTop closure_on_closed)
      qed
      have hfinite_union_closed: "closedin_on X TX (\<Union> (closure_on X TX ` Ufn ` {0..n}))"
        using closedin_on_finite_Union[OF hTop] hclUfn_closed
        
        by auto
      have hcomplement_open: "X - (\<Union> (closure_on X TX ` Ufn ` {0..n})) \<in> TX"
        using hfinite_union_closed unfolding closedin_on_def
        
        by satx
      have hVnX: "Vn n \<subseteq> X"
        using hVopen hBasis unfolding basis_for_def topology_generated_by_basis_def
        
        by blast
      have hV'eq: "V' n = Vn n \<inter> (X - (\<Union> (closure_on X TX ` Ufn ` {0..n})))"
        unfolding V'_def using hVnX
        
        by fast
      show "V' n \<in> TX"
        unfolding hV'eq
        using hVopen hcomplement_open hTop
        
        using topology_inter2 by blast
    qed

    text \<open>UU and VV are open (unions of opens).\<close>
    have hU'range: "range U' \<subseteq> TX"
      using hU'open
      
      by blast
    have hUU_open: "UU \<in> TX"
    proof -
      have "\<Union>(range U') \<in> TX"
        using hTop hU'range unfolding is_topology_on_def
        
        by presburger
      then show ?thesis unfolding UU_def
        
        by presburger
    qed
    have hV'range: "range V' \<subseteq> TX"
      using hV'open
      
      by auto
    have hVV_open: "VV \<in> TX"
    proof -
      have "\<Union>(range V') \<in> TX"
        using hTop hV'range unfolding is_topology_on_def
        
        by presburger
      then show ?thesis unfolding VV_def
        
        by argo
    qed

    text \<open>C ⊆ UU: for c ∈ C, c ∈ Ufn_n for some n; cl(Vn_i) ⊆ X-C for all i, so c ∉ cl(Vn_i).\<close>
    have hC_sub_UU: "C \<subseteq> UU"
    proof (rule subsetI)
      fix c assume hcC: "c \<in> C"
      have hcUn: "c \<in> (\<Union>n. Ufn n)" using hC_sub_Un hcC
        
        by fast
      then obtain n where hcUfn: "c \<in> Ufn n"
        
        by blast
      have hc_not_clV: "\<forall>i. c \<notin> closure_on X TX (Vn i)"
      proof (intro allI)
        fix i
        have "closure_on X TX (Vn i) \<subseteq> X - C" using hVcl
          
          by presburger
        then show "c \<notin> closure_on X TX (Vn i)" using hcC
          
          by blast
      qed
      have "c \<in> U' n"
        unfolding U'_def using hcUfn hc_not_clV
        
        by blast
      then show "c \<in> UU" unfolding UU_def
        
        by blast
    qed
    have hD_sub_VV: "D \<subseteq> VV"
    proof (rule subsetI)
      fix d assume hdD: "d \<in> D"
      have hdVn: "d \<in> (\<Union>n. Vn n)" using hD_sub_Vn hdD
        
        by fast
      then obtain n where hdVnn: "d \<in> Vn n"
        
        by blast
      have hd_not_clU: "\<forall>i. d \<notin> closure_on X TX (Ufn i)"
      proof (intro allI)
        fix i
        have "closure_on X TX (Ufn i) \<subseteq> X - D" using hUcl
          
          by auto
        then show "d \<notin> closure_on X TX (Ufn i)" using hdD
          
          by blast
      qed
      have "d \<in> V' n"
        unfolding V'_def using hdVnn hd_not_clU
        
        by fast
      then show "d \<in> VV" unfolding VV_def
        
        by fast
    qed

    text \<open>UU ∩ VV = {}: if z ∈ U'_m ∩ V'_n, then WLOG m ≤ n.
      z ∈ U'_m ⊆ Ufn_m, so z ∈ closure_on Ufn_m. But z ∈ V'_n excludes ∪{cl(Ufn_i)|i≤n}.\<close>
    have hUV_disj: "UU \<inter> VV = {}"
    proof (rule ccontr)
      assume "\<not> UU \<inter> VV = {}"
      then obtain z where hzUU: "z \<in> UU" and hzVV: "z \<in> VV"
        
        by auto
      obtain m where hzU'm: "z \<in> U' m"
        using hzUU unfolding UU_def
        
        by blast
      obtain n where hzV'n: "z \<in> V' n"
        using hzVV unfolding VV_def
        
        by blast
      text \<open>WLOG m ≤ n (symmetric argument for n ≤ m).\<close>
      have "m \<le> n \<or> n \<le> m"
        
        by presburger
      then show False
      proof
        assume hmn: "m \<le> n"
        text \<open>z ∈ U'_m ⊆ Ufn_m, so z ∈ closure(Ufn_m) (since Ufn_m ⊆ closure(Ufn_m)).\<close>
        have hzUfn: "z \<in> Ufn m" using hzU'm unfolding U'_def
          
          by blast
        have hzclU: "z \<in> closure_on X TX (Ufn m)"
          using hzUfn subset_closure_on
          
          by fast
        text \<open>But z ∈ V'_n = Vn_n - ∪{cl(Ufn_i)|i≤n}, and m ≤ n.\<close>
        have "z \<notin> closure_on X TX (Ufn m)"
          using hzV'n hmn unfolding V'_def
          
          by simp
        then show False using hzclU
          
          by presburger
      next
        assume hnm: "n \<le> m"
        have hzVnn: "z \<in> Vn n" using hzV'n unfolding V'_def
          
          by blast
        have hzclV: "z \<in> closure_on X TX (Vn n)"
          using hzVnn subset_closure_on
          
          by fast
        have "z \<notin> closure_on X TX (Vn n)"
          using hzU'm hnm unfolding U'_def
          
          by auto
        then show False using hzclV
          
          by presburger
      qed
    qed

    show "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> C \<subseteq> U \<and> D \<subseteq> V \<and> U \<inter> V = {}"
      using hUU_open hVV_open hC_sub_UU hD_sub_VV hUV_disj
      
      by blast
  qed
qed
```

### context `Lemma_40_1_step1`: [`tst/Top1_Ch5_8.thy` lines 4376-4623](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L4376-L4623) ([local copy](code/tst/Top1_Ch5_8.thy))

```isabelle
lemma Lemma_40_1_step1:
  assumes hReg: "top1_regular_on X TX"
  assumes hBasis: "basis_for X \<B> TX"
  assumes hCLF: "top1_sigma_locally_finite_family_on X TX \<B>"
  assumes hW: "W \<in> TX"
  shows "\<exists>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX) \<and> (\<forall>n. closure_on X TX (U n) \<subseteq> W) \<and> W = (\<Union>n. U n)"
proof -
  have hTop: "is_topology_on X TX"
    using hReg unfolding top1_regular_on_def top1_T1_on_def
    
    by satx
  have hBsub: "\<B> \<subseteq> TX"
    using hBasis unfolding basis_for_def
    
    using basis_elem_open_in_generated_topology by blast
  text \<open>Decompose the basis into countably many locally finite families.\<close>
  have hCLF_unf: "\<exists>\<B>n::nat \<Rightarrow> 'a set set. (\<forall>n. top1_locally_finite_family_on X TX (\<B>n n)) \<and> \<B> = (\<Union>n. \<B>n n)"
    using hCLF unfolding top1_sigma_locally_finite_family_on_def
    
    by argo
  obtain \<B>n :: "nat \<Rightarrow> 'a set set" where hBn_lf: "\<forall>n. top1_locally_finite_family_on X TX (\<B>n n)"
    and hB_eq: "\<B> = (\<Union>n. \<B>n n)"
    using hCLF_unf
    
    by blast
  text \<open>C_n = \{B \<in> B_n | cl(B) \<subseteq> W\}, U_n = \<Union>C_n.\<close>
  define Cn where "Cn n = {B \<in> \<B>n n. closure_on X TX B \<subseteq> W}" for n
  define U where "U n = \<Union>(Cn n)" for n

  have hUn_open: "\<forall>n. U n \<in> TX"
  proof (intro allI)
    fix n
    have hCn_sub_TX: "Cn n \<subseteq> TX"
    proof (rule subsetI)
      fix B assume "B \<in> Cn n"
      then have "B \<in> \<B>n n" unfolding Cn_def
        
        by fast
      then have "B \<in> \<B>" using hB_eq
        
        by blast
      then show "B \<in> TX" using hBsub
        
        by blast
    qed
    show "U n \<in> TX"
      unfolding U_def using hTop hCn_sub_TX unfolding is_topology_on_def
      
      by presburger
  qed

  have hB_subX: "\<forall>b\<in>\<B>. b \<subseteq> X"
    using hBasis unfolding basis_for_def is_basis_on_def
    by satx

  text \<open>cl(U_n) \<subseteq> W: each Cn is locally finite (subset of Bn), so cl(\<Union>Cn) = \<Union>cl(Cn).\<close>
  have hCn_lf: "\<forall>n. top1_locally_finite_family_on X TX (Cn n)"
  proof (intro allI)
    fix n
    have hCn_sub_Bn: "Cn n \<subseteq> \<B>n n" unfolding Cn_def by fast
    have hBn_subX: "\<forall>A\<in>\<B>n n. A \<subseteq> X"
    proof (intro ballI)
      fix A assume "A \<in> \<B>n n"
      then have "A \<in> \<B>" using hB_eq
        
        by blast
      then show "A \<subseteq> X" using hB_subX
        
        by blast
    qed
    show "top1_locally_finite_family_on X TX (Cn n)"
      using hCn_sub_Bn
        Lemma_39_1(1)[OF hTop hBn_subX hBn_lf[rule_format, of n]]
      
      by presburger
  qed
  have hCn_subX: "\<forall>n. \<forall>B\<in>Cn n. B \<subseteq> X"
  proof (intro allI ballI)
    fix n B assume "B \<in> Cn n"
    then have "B \<in> \<B>n n" unfolding Cn_def by fast
    then have "B \<in> \<B>" using hB_eq by blast
    then show "B \<subseteq> X" using hB_subX
      
      by blast
  qed

  have hUn_cl: "\<forall>n. closure_on X TX (U n) \<subseteq> W"
  proof (intro allI)
    fix n
    have hCn_subX_n: "\<forall>A\<in>Cn n. A \<subseteq> X"
      using hCn_subX
      
      by presburger
    have hcl_eq: "closure_on X TX (U n) = (\<Union>(closure_on X TX ` Cn n))"
      unfolding U_def
      using Lemma_39_1(3)[OF hTop hCn_subX_n hCn_lf[rule_format, of n]]
      
      by presburger
    have "\<forall>B\<in>Cn n. closure_on X TX B \<subseteq> W"
      unfolding Cn_def
      
      by blast
    then show "closure_on X TX (U n) \<subseteq> W"
      unfolding hcl_eq
      
      by blast
  qed

  text \<open>W \<subseteq> \<Union>n. U n: for x \<in> W, regularity gives B with cl(B) \<subseteq> W.\<close>
  have hW_sub: "W \<subseteq> (\<Union>n. U n)"
  proof (rule subsetI)
    fix x assume hxW: "x \<in> W"
    have hWsubX: "W \<subseteq> X"
      using hW hBasis unfolding basis_for_def
      
      by (simp add: topology_generated_by_basis_def)
    have hxX: "x \<in> X"
      using hxW hWsubX
      
      by fast
    have hRegProp: "\<exists>V\<in>TX. x \<in> V \<and> closure_on X TX V \<subseteq> W"
    proof -
      define C where "C = X - W"
      have hCclosed: "closedin_on X TX C"
        unfolding C_def closedin_on_def using hWsubX hW
        
        by (simp add: Diff_Diff_Int Int_absorb1)
      have hxnotC: "x \<notin> C"
        unfolding C_def using hxW
        
        by blast
      obtain U0 V0 where hU0: "neighborhood_of x X TX U0" and hV0: "V0 \<in> TX"
        and hCV0: "C \<subseteq> V0" and hdisjoint: "U0 \<inter> V0 = {}"
        using hReg hxX hCclosed hxnotC unfolding top1_regular_on_def
        
        by blast
      obtain U0' where hU0'open: "U0' \<in> TX" and hxU0': "x \<in> U0'" and hU0'sub: "U0' \<subseteq> U0"
        using hU0 unfolding neighborhood_of_def
        
        by blast
      have hU0'_disj_V0: "U0' \<inter> V0 = {}"
        using hU0'sub hdisjoint
        
        by blast
      have hV0subX: "V0 \<subseteq> X"
        using hV0 hBasis unfolding basis_for_def topology_generated_by_basis_def
        
        by force
      have hXminusV0_closed: "closedin_on X TX (X - V0)"
        unfolding closedin_on_def using hV0 hV0subX
        by (simp add: double_diff)
      have hU0'_sub_XmV0: "U0' \<subseteq> X - V0"
      proof -
        have "U0' \<subseteq> X" using hU0'open hBasis unfolding basis_for_def topology_generated_by_basis_def
          
          by blast
        then show ?thesis using hU0'_disj_V0
          
          by blast
      qed
      have hcl_sub: "closure_on X TX U0' \<subseteq> X - V0"
        using hXminusV0_closed hU0'_sub_XmV0
        
        by (simp add: closure_on_subset_of_closed)
      have hXmV0_sub_W: "X - V0 \<subseteq> W"
        using hCV0 unfolding C_def
        
        by blast
      have hcl_sub_W: "closure_on X TX U0' \<subseteq> W"
        using hcl_sub hXmV0_sub_W
        
        by order
      show ?thesis using hU0'open hxU0' hcl_sub_W
        
        by blast
    qed
    obtain V where hVopen: "V \<in> TX" and hxV: "x \<in> V" and hclV: "closure_on X TX V \<subseteq> W"
      using hRegProp
      
      by blast
    text \<open>Since B is a basis, there is B \<in> B with x \<in> B \<subseteq> V.\<close>
    obtain B where hBB: "B \<in> \<B>" and hxB: "x \<in> B" and hBV: "B \<subseteq> V"
      using hBasis hxX hVopen hxV unfolding basis_for_def
      
      by (metis basis_for_refine hBasis)
    have hclB: "closure_on X TX B \<subseteq> W"
    proof -
      have "B \<subseteq> V"
        
        by (simp add: hBV)
      then have "closure_on X TX B \<subseteq> closure_on X TX V"
        
        by (simp add: closure_on_mono)
      then show ?thesis using hclV
        
        by order
    qed
    obtain n where "B \<in> \<B>n n"
      using hBB hB_eq
      
      by fast
    then have "B \<in> Cn n" unfolding Cn_def using hclB
      
      by blast
    then have "x \<in> U n" unfolding U_def using hxB
      
      by fast
    then show "x \<in> (\<Union>n. U n)"
      
      by blast
  qed

  have hWeq: "W = (\<Union>n. U n)"
  proof (rule equalityI)
    show "W \<subseteq> (\<Union>n. U n)" by (rule hW_sub)
    show "(\<Union>n. U n) \<subseteq> W"
    proof (rule subsetI)
      fix x assume "x \<in> (\<Union>n. U n)"
      then obtain n where "x \<in> U n"
        
        by blast
      then have "x \<in> \<Union>(Cn n)" unfolding U_def
        
        by satx
      then obtain B where "B \<in> Cn n" and "x \<in> B"
        
        by blast
      then have "closure_on X TX B \<subseteq> W" unfolding Cn_def
        
        by blast
      moreover have "x \<in> closure_on X TX B"
        using \<open>x \<in> B\<close> subset_closure_on
        
        by fast
      ultimately show "x \<in> W"
        
        by blast
    qed
  qed

  have hconj: "(\<forall>n. U n \<in> TX) \<and> (\<forall>n. closure_on X TX (U n) \<subseteq> W) \<and> W = (\<Union>n. U n)"
    using hUn_open hUn_cl hWeq
    
    by argo
  show ?thesis using hconj
    
    by blast
qed
```

### context `closedin_on_finite_Union`: [`tst/Top1_Ch5_8.thy` lines 4708-4754](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L4708-L4754) ([local copy](code/tst/Top1_Ch5_8.thy))

```isabelle
lemma closedin_on_finite_Union:
  assumes hTop: "is_topology_on X TX"
  assumes hCl: "\<forall>A\<in>F. closedin_on X TX A"
  assumes hFin: "finite F"
  shows "closedin_on X TX (\<Union>F)"
  using hFin hCl
proof (induct F rule: finite_induct)
  case empty
  show ?case unfolding closedin_on_def using hTop unfolding is_topology_on_def
    
    by auto
next
  case (insert A F)
  have hAcl: "closedin_on X TX A"
    using insert.prems
    
    by blast
  have hFcl: "closedin_on X TX (\<Union>F)"
    using insert.hyps insert.prems
    
    by blast
  have hAX: "A \<subseteq> X" using hAcl unfolding closedin_on_def
    
    by presburger
  have hFX: "\<Union>F \<subseteq> X" using hFcl unfolding closedin_on_def
    
    by presburger
  have hAopen: "X - A \<in> TX" using hAcl unfolding closedin_on_def
    
    by presburger
  have hFopen: "X - \<Union>F \<in> TX" using hFcl unfolding closedin_on_def
    
    by presburger
  have hinter: "(X - A) \<inter> (X - \<Union>F) \<in> TX"
    using hTop hAopen hFopen
    
    by (simp add: topology_inter2)
  have heq: "X - (A \<union> \<Union>F) = (X - A) \<inter> (X - \<Union>F)"
    
    by auto
  have hXsub: "A \<union> \<Union>F \<subseteq> X" using hAX hFX
    
    by simp
  show ?case unfolding closedin_on_def using hXsub hinter heq
    
    by auto
qed
```

### context `top1_G_delta_on_def`: [`tst/Top1_Ch5_8.thy` lines 4369-4370](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L4369-L4370) ([local copy](code/tst/Top1_Ch5_8.thy))

```isabelle
definition top1_G_delta_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_G_delta_on X TX A \<longleftrightarrow> A \<subseteq> X \<and> (\<exists>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX) \<and> A = (\<Inter>n. U n))"
```

How the parts fit. The parent `Lemma_40_1` does no mathematics at all: it is a
conjunction `top1_normal_on X TX ∧ (∀A. closedin_on X TX A ⟶ top1_G_delta_on X
TX A)`, and its proof applies the two children to the same three hypotheses and
lets `argo` assemble the result:

```text
Lemma_40_1 : normal ∧ (closed ⟶ G-delta)              (5064-5072, 4-line glue)
  │ using Lemma_40_1_step3[OF hReg hBasis hCLF]        normal half
  ├─ Lemma_40_1_step3 ── top1_normal_on X TX           (4756-5062)
  │     ├─ Lemma_40_1_step1 (4798, 4811)               open decomposition of X-D, X-C
  │     └─ closedin_on_finite_Union (4854, 4891)       the subtracted unions are closed
  │ using Lemma_40_1_step2[OF hReg hBasis hCLF]        G-delta half
  └─ Lemma_40_1_step2 ── closedin_on X TX A ⟶
                           top1_G_delta_on X TX A      (4626-4704)
        └─ Lemma_40_1_step1 (4649)                     open decomposition of W = X - A
  by argo                                              assemble the conjunction
```

Each child is a good leaf because its statement is self-contained — a single
topological predicate under the three hypotheses — and its proof closes on its
own from `Lemma_40_1_step1` (the shared open-decomposition lemma proved just
above) and library facts, never from its sibling. `Lemma_40_1_step2` applies
`Lemma_40_1_step1` to the open complement `W = X - A`, gets `U n` with
`cl(U n) ⊆ W` and `W = ⋃n. U n`, defines `V n = X - cl(U n)`, shows
`A = ⋂n. V n`, and closes by unfolding `top1_G_delta_on_def` and
`apply (rule exI[where x=V]) by satx`. `Lemma_40_1_step3` is the classical
Theorem 32.1 shrinking argument: apply `Lemma_40_1_step1` to `X - D` and to
`X - C`, define `U'_n = U_n − ⋃_{i≤n}cl(V_i)` and `V'_n = V_n − ⋃_{i≤n}cl(U_i)`,
use `closedin_on_finite_Union` to show the subtracted unions are closed, prove
`C ⊆ UU`, `D ⊆ VV` and `UU ∩ VV = {}` (the last by a WLOG `m ≤ n` split), and
finish with `by blast`.

The two children are independent of each other, so they can be proved (or
handed to separate provers) in parallel; the only thing they share is
`Lemma_40_1_step1`, which is itself the real content and is stated once, not
duplicated.

## Why it is good

1. The parent closes in four lines by `using` the two step lemmas and `argo`,
   with no other proof step (check — [Top1_Ch5_8.thy 5064-5072](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L5064-L5072)).
2. Each child is a self-contained `lemma … qed` that closes on its own, and the
   region 4369-5072 (parent, children and context lemmas) has no `sorry`,
   `oops` or `admit` (check — [step2 4626-4704](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L4626-L4704), [step3 4756-5062](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L4756-L5062)).
3. Below the parent sits a depth-2 chain of project lemmas,
   `Lemma_40_1 → (step2 | step3) → step1`, each applied by an explicit step
   (check — [step2 uses step1 at 4649](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L4649), [step3 uses step1 at 4798 and 4811](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L4798)).
4. The authors name the steps and tie them to the textbook: "Step 1 of Lemma
   40.1: open set decomposition", "Step 2 …: closed sets are G-delta",
   "Step 3 …: normality via the Theorem 32.1 technique", under the section
   "\S40 The Nagata-Smirnov Metrization Theorem" (author-statement —
   [4367-4373, 4625, 4706](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L4367)).
5. The shape is a measurement: a 9-line parent whose 4-line proof body
   delegates 386 lines of proof to the two children (measurement —
   [Top1_Ch5_8.thy](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy)).

In my opinion the detail worth copying is the *shared-context* discipline: the
three hypotheses `hReg`/`hBasis`/`hCLF` are restated verbatim in every step
lemma, which is exactly what lets the parent close with two uniform
`[OF hReg hBasis hCLF]` instantiations and `argo` — no hypothesis is re-derived
in the glue. The one-level-deeper split (a shared `step1` under both children)
is also worth copying: when two children would otherwise repeat the same open
decomposition, it is lifted out once.

## When to use it, and when not

Use it when a goal is a conjunction (or several named claims) over one shared
hypothesis context, each conjunct has a proof long enough to deserve its own
lemma, and the two halves are independent — neither proof needs the other's
conclusion. Then lift each conjunct into a standalone lemma that restates the
same hypotheses verbatim, and leave the parent as a pure `using lemmaP lemmaQ
by argo` assembly. This is the shape a bounded prover can fill: one hole per
conjunct, each hole a self-contained statement.

Avoid it when the two halves share a genuinely intermediate construction — lift
that shared part out first (as `Lemma_40_1_step1` is here) instead of
duplicating it in both children, or the duplication will make the children
bigger than the parent. Avoid it when the conjunction is so short that a single
`intro conjI` proof is clearer than two lemmas. And avoid it when the
hypotheses differ between halves: the whole glue depends on both children
taking exactly the same `assumes` in the same order.

## Consequences

The move turns one conjunction goal into two named obligations (normality, and
closed-implies-G-delta) that each restate the three shared hypotheses
`hReg`/`hBasis`/`hCLF` verbatim. The parent's `using` step relies on the two
children having exactly those three `assumes` in the same order, so a child
that adds or drops a hypothesis breaks the `[OF hReg hBasis hCLF]` template.
The two children are independent of each other — each calls the shared
open-decomposition `Lemma_40_1_step1`, never its sibling — so they can be
proved in parallel. The real difficulty is not removed but pushed one level
down into `Lemma_40_1_step1` (248 lines); if that shared lemma is wrong or too
weak, both children fail together. Downstream, `Theorem_40_3` (the
Nagata-Smirnov metrization theorem) consumes `Lemma_40_1` twice ([lines 6105
and 6107](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/Top1_Ch5_8.thy#L6105)), so the
decomposition's statement must stay exactly the one that theorem needs.

## Rule mapping

This supports survey F §10 rule 4 ("Extract a `have` into a standalone lemma
only with a fidelity check"): the two conjuncts of `Lemma_40_1` are lifted into
the standalone lemmas `Lemma_40_1_step2` and `Lemma_40_1_step3`, and the parent
reassembles them with `using … by argo`, which is exactly the rule's fidelity
check ("replace the hole with `using name by blast`").

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/JUrban/isa_top_autoform1 at commit `90d108779e83453e9cae2f55b513246e1cc044e0`, under `LicenseRef-unknown`; see the [source note](../../sources/munkres-isabelle/SOURCE.md) for the licence text and attribution.
