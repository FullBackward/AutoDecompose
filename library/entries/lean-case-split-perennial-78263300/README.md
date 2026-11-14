# Case split on the node index closes the three-node netfs crash-safety theorem

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | draft |
| Source | [perennial](../../sources/perennial/SOURCE.md) at `ddc0f0acc59a` |
| Licence | `LicenseRef-unknown` |

## Intent

Reduce the end-to-end crash-safety theorem for the three-node netfs to one
instantiation of the generic distributed crash-adequacy theorem
(`goose_dist_crash_adequacy`), then discharge its per-node obligation by a case
split on the node index (`0`, `1`, `2`), each branch applying the shared boot
wrapper `wp_boot` to that node's linked spec (`wp_NodeA` / `wp_NodeB` /
`wp_NodeC`).

## The decomposition

### parent `netfs_crash_safety_bounded`: [`Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean` lines 157-311](https://github.com/mit-pdos/perennial/blob/ddc0f0acc59a5730ad109be9ecfc4a485dcc4ea0/Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean#L157-L311) ([local copy](code/Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean))

```lean
theorem netfs_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions]
    [hPre : GooseGpreS GF] (N T : Nat) (σa σb σc : state) (g : GlobalState) (c0 old : GoString)
    (Ha : NodeStart lctx σa go!"a") (Hb : NodeStart lctx σb go!"b") (Hc : NodeStart lctx σc go!"c")
    (Hin : extLocal fsExt σa.world !! go!"in" = some c0)
    (Hout : extLocal fsExt σb.world !! go!"out" = some old)
    (Hsent : extLocal fsExt σb.world !! go!"sent" = some go!"")
    (Hneta : extGlobal netExt g.globalWorld !! go!"a" = some ∅)
    (Hnetb : extGlobal netExt g.globalWorld !! go!"b" = some ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σa σb σc).map Prod.fst) n
      (distInit (system σa σb σc) g) κs c)
    (Hbound : n < N)
    (Hlive : DistCrashThreadsBelow ((system σa σb σc).map Prod.fst) T n
      (distInit (system σa σb σc) g)) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  refine goose_dist_crash_adequacy (GF := GF) N T (system σa σb σc) g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨trivial, trivial, trivial⟩
    (fun _ _ => ⟨trivial, trivial, trivial⟩) (fun i L => nodePre c0 i L) ?_ ?_
    n κs c Hsteps Hbound ?_ Hlive
  · -- the global setup and the first generation of every node
    intro G _
    iintro Hg
    -- the protocol, from the network's points-to of `"a"` and `"b"`
    icases fsNet_globalStart g.globalWorld $$ Hg with Hnet
    icases (BigSepM.bigSepM_delete Hneta).1 $$ Hnet with ⟨Hna, Hnet⟩
    have Hnetb' : PartialMap.get? (PartialMap.delete (extGlobal netExt g.globalWorld) go!"a")
        go!"b" = some ∅ := by
      rw [LawfulPartialMap.get?_delete_ne (by decide)]; exact Hnetb
    icases (BigSepM.bigSepM_delete Hnetb').1 $$ Hnet with ⟨Hnb, -⟩
    imod inv_alloc netN ⊤ (netInv (extGlobalGS netExt) c0) $$ [Hna Hnb] with #Hinv
    · inext
      iexists ∅, ∅
      iframe Hna Hnb
      ipureintro
      exact ⟨goodMsgs_empty c0, goodMsgs_empty c0⟩
    imodintro
    simp only [system]
    unfold nodeStart
    isplitl []
    · -- `"a"`: the file `"in"` holds `c0` for good
      iintro %L %_ %_ Hstart Hgs
      icases fsNet_localStart (L := L) σa.world $$ Hstart with ⟨Hfiles, %Haddr⟩
      icases (BigSepM.bigSepM_lookup (Φ := fun f c => fsPointsto (extLocalGS fsExt (L := L)) f
        (DFrac.own 1) c) Hin) $$ Hfiles with Hf
      imod fsPointsto_persist (L := L) go!"in" (DFrac.own 1) c0 $$ Hf with #Hf
      rw [Ha.packageState]
      imodintro
      unfold nodePre
      isplitl []
      · iexact Hinv
      isplitl [Hgs]
      · iexact Hgs
      isplitr
      · ipureintro; exact Haddr.trans Ha.addr
      simp only [nodeFiles, ↓reduceIte]
      iexact Hf
    isplitl []
    · -- `"b"`: the invariant of its files, not done yet
      iintro %L %_ %_ Hstart Hgs
      icases fsNet_localStart (L := L) σb.world $$ Hstart with ⟨Hfiles, %Haddr⟩
      icases (BigSepM.bigSepM_delete Hout).1 $$ Hfiles with ⟨Ho, Hfiles⟩
      have Hsent' : PartialMap.get? (PartialMap.delete (extLocal fsExt σb.world) go!"out")
          go!"sent" = some go!"" := by
        rw [LawfulPartialMap.get?_delete_ne (by decide)]; exact Hsent
      icases (BigSepM.bigSepM_delete Hsent').1 $$ Hfiles with ⟨Hs, -⟩
      letI hG : HeapGS .hasLC GF := ⟨G, L⟩
      imod dghostVar_alloc (GF := GF) () with ⟨%γ, Hown⟩
      imod inv_alloc outN ⊤ (bInv (extLocalGS fsExt (L := L)) c0 γ) $$ [Ho Hs Hown] with #Hb
      · inext
        iexists old, go!""
        iframe Ho Hs
        ileft
        iframe Hown
        ipureintro; decide
      rw [Hb.packageState]
      imodintro
      unfold nodePre
      isplitl []
      · iexact Hinv
      isplitl [Hgs]
      · iexact Hgs
      isplitr
      · ipureintro; exact Haddr.trans Hb.addr
      simp only [nodeFiles, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexists γ
      iexact Hb
    isplitl []
    · -- `"c"`
      iintro %L %_ %_ Hstart Hgs
      icases fsNet_localStart (L := L) σc.world $$ Hstart with ⟨-, %Haddr⟩
      rw [Hc.packageState]
      imodintro
      unfold nodePre
      isplitl []
      · iexact Hinv
      isplitl [Hgs]
      · iexact Hgs
      isplitr
      · ipureintro; exact Haddr.trans Hc.addr
      simp only [nodeFiles, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      itrivial
    iempintro
  · -- every generation of every node: its boot program, and its next precondition
    intro hG _ _ i e σ Hes Hlctx
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    have Hnode : (i = 0 ∧ e = boot NodeA ∧ σ = σa) ∨ (i = 1 ∧ e = boot NodeB ∧ σ = σb) ∨
        (i = 2 ∧ e = boot NodeC ∧ σ = σc) := by
      match i, Hes with
      | 0, Hes => cases Hes; exact .inl ⟨rfl, rfl, rfl⟩
      | 1, Hes => cases Hes; exact .inr (.inl ⟨rfl, rfl, rfl⟩)
      | 2, Hes => cases Hes; exact .inr (.inr ⟨rfl, rfl, rfl⟩)
    have Hl : σ.goState.goLctx = lctx := by
      rcases Hnode with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact Ha.goLctx
      · exact Hb.goLctx
      · exact Hc.goLctx
    rw [Hl] at Hlctx
    subst Hlctx
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold nodePre
    iintro ⟨#Hinv, Hgs, %Haddr, #Hf⟩ _
    imodintro
    isplitl [Hgs]
    · rcases Hnode with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · iapply wp_boot NodeA _ (wp_NodeA (GF := GF) c0 Haddr) $$ [] Hgs
        isplitl []
        · iexact Hinv
        · simp only [nodeFiles, ↓reduceIte]; iexact Hf
      · simp only [nodeFiles, Nat.reduceEqDiff, ↓reduceIte]
        icases Hf with ⟨%γ, #Hb⟩
        iapply wp_boot NodeB _ (wp_NodeB (GF := GF) c0 γ Haddr) $$ [] Hgs
        isplitl []
        · iexact Hinv
        · iexact Hb
      · iapply wp_boot NodeC _ (wp_NodeC (GF := GF) c0 Haddr) $$ [] Hgs
        iexact Hinv
    · -- after a crash: the files' and the address's ghost state are kept
      iintro %L' _ Hcs Hgs'
      icases fsNet_crashStart _ L' $$ Hcs with ⟨%Hfs, %Hnet⟩
      imodintro
      iframe Hinv Hgs'
      rw [Hfs, Hnet]
      isplitr
      · ipureintro; exact Haddr
      iexact Hf
  · intro n hn
    simp only [system, List.mem_cons, List.not_mem_nil, _root_.or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact Ha.threads
    · exact Hb.threads
    · exact Hc.threads
```

### child `goose_dist_crash_adequacy`: [`Perennial/GooseLang/DistAdequacy.lean` lines 744-801](https://github.com/mit-pdos/perennial/blob/ddc0f0acc59a5730ad109be9ecfc4a485dcc4ea0/Perennial/GooseLang/DistAdequacy.lean#L744-L801) ([local copy](code/Perennial/GooseLang/DistAdequacy.lean))

```lean
theorem goose_dist_crash_adequacy [hPre : GooseGpreS GF] (N T : Nat)
    (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (Hinitg : extsInitgP g.globalWorld)
    (Hinit : ∀ n, n ∈ es → extsInitP n.2.world g.globalWorld)
    (P : ∀ [GooseGlobalGS .hasLC GF], Nat → GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeStart T n.2 (P i))
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      ∀ (i : Nat) (e : Expr) (σ : state), es[i]? = some (e, σ) →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P i hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ i v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P i L')
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps (es.map Prod.fst) n (distInit es g) κs c)
    (Hbound : n < N) (Hthreads : ∀ n, n ∈ es → n.2.threads = 1)
    (Hlive : DistCrashThreadsBelow (es.map Prod.fst) T n (distInit es g)) :
    ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → φ i v) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  intro i tp σ Hi
  have hlen : i < es.length := by
    have := (List.getElem?_eq_some_iff.mp Hi).1
    rw [Hsteps.length] at this
    simpa [distInit] using this
  have hT : 1 < T := by
    have := Hlive.start (i := i) (tp := [es[i].1]) (σ := es[i].2) (by simp [distInit, hlen])
    rw [Hthreads _ (List.getElem_mem hlen)] at this
    exact this
  obtain ⟨bc, Hb, He⟩ := bdist_crash_nsteps_of_real Hsteps T Hlive (bdistInit N T es g)
    (bdistInit_erase N T es g) (by simp only [bdistInit]; omega) (bdistInit_fuelOk Hthreads)
  subst He
  simp only [BDistCfg.erase, List.getElem?_map] at Hi
  obtain ⟨⟨tp₀, σ₀, t⟩, Hbi, hx⟩ := Option.map_eq_some_iff.mp Hi
  obtain ⟨rfl, rfl⟩ : tp = tp₀ ∧ σ = σ₀ := by
    simp only [Prod.mk.injEq] at hx; exact ⟨hx.1.symm, hx.2.symm⟩
  have Hadeq := fun {m κs' c'} (Hm : BDistCrashNsteps (es.map Prod.fst) T m bc κs' c')
      {i tp σ t} (Hi : c'.nodes[i]? = some (tp, σ, t)) {j} {e} (Hj : tp[j]? = some e) =>
    goose_dist_crash_adequacy_blang N T (by omega) hT es g φ hφ Hinitg Hinit P Hstart Hwp
      (Hb.append Hm) Hi Hj
  refine ⟨?_, ?_, ?_⟩
  · rintro v tp' rfl
    exact ((Hadeq (.refl _) Hbi (j := 0) (e := Val v) rfl).2 v rfl).2 rfl
  · intro e he
    obtain ⟨j, Hj⟩ := List.getElem?_of_mem he
    exact realNotStuck_of_bounded (Hadeq (.refl _) Hbi Hj).1
  · intro e he Hu
    obtain ⟨m, κs', c', tp', j, p, Hm, Hi', Hj, -⟩ := unrecoveredPanic_node Hbi he Hu
    have := (Hadeq Hm.crash Hi' Hj).2 (PanicV p) rfl
    simp at this
```

### child `fsNet_globalStart`: [`Perennial/GooseLang/Ext/Net/Adequacy.lean` lines 101-104](https://github.com/mit-pdos/perennial/blob/ddc0f0acc59a5730ad109be9ecfc4a485dcc4ea0/Perennial/GooseLang/Ext/Net/Adequacy.lean#L101-L104) ([local copy](code/Perennial/GooseLang/Ext/Net/Adequacy.lean))

```lean
theorem fsNet_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState exts) :
    extsGlobalStart (GF := GF) g ⊢
      [∗map] a ↦ ms ∈ extGlobal netExt g, netPointsto (extGlobalGS netExt) a (.own 1) ms :=
  (sep_elim_right (P := iprop(True))).trans sep_elim_left
```

### child `fsNet_localStart`: [`Perennial/GooseLang/Ext/Net/Adequacy.lean` lines 108-112](https://github.com/mit-pdos/perennial/blob/ddc0f0acc59a5730ad109be9ecfc4a485dcc4ea0/Perennial/GooseLang/Ext/Net/Adequacy.lean#L108-L112) ([local copy](code/Perennial/GooseLang/Ext/Net/Adequacy.lean))

```lean
theorem fsNet_localStart [L : GooseLocalGS GF] (σ : ExtsLocalState exts) :
    extsLocalStart (GF := GF) σ ⊢
      ([∗map] f ↦ c ∈ extLocal fsExt σ, fsPointsto (extLocalGS fsExt) f (.own 1) c) ∗
      ⌜(extLocalGS netExt (L := L) : NetNodeGS GF).addr = extLocal netExt σ⌝ :=
  sep_mono_right sep_elim_left
```

### child `fsNet_crashStart`: [`Perennial/GooseLang/Ext/Net/Adequacy.lean` lines 116-120](https://github.com/mit-pdos/perennial/blob/ddc0f0acc59a5730ad109be9ecfc4a485dcc4ea0/Perennial/GooseLang/Ext/Net/Adequacy.lean#L116-L120) ([local copy](code/Perennial/GooseLang/Ext/Net/Adequacy.lean))

```lean
theorem fsNet_crashStart (L L' : GooseLocalGS GF) :
    extsCrashStart (GF := GF) L L' ⊢
      ⌜extLocalGS fsExt (L := L') = extLocalGS fsExt (L := L)⌝ ∗
      ⌜extLocalGS netExt (L := L') = extLocalGS netExt (L := L)⌝ :=
  sep_mono_right sep_elim_left
```

### child `wp_boot`: [`Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean` lines 85-124](https://github.com/mit-pdos/perennial/blob/ddc0f0acc59a5730ad109be9ecfc4a485dcc4ea0/Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean#L85-L124) ([local copy](code/Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean))

```lean
theorem wp_boot [hG : HeapGS .hasLC GF] [sem : go.Semantics] [package_sem : Assumptions] (f : GoString) (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF)
          pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs ∗ P }}
        (App (Val (@! f)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP (boot f) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  have Hne₁ : pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext ≠
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs := by
    unfold pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs
    decide
  have Hne₂ : pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext ≠
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs := by
    unfold pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs
    decide
  have Hne₃ : pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext ≠
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext := by
    unfold pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext
    decide
  have Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs
      (getIsPkgInit (GF := GF)) := by
    refine ⟨by simp [getIsPkgInit], ⟨by simp [getIsPkgInit, Hne₁], trivial⟩,
      ⟨by simp [getIsPkgInit, Hne₂, Hne₃], trivial⟩, trivial⟩
  iintro HP Hgs
  unfold boot
  wp_apply wp_initialize' getIsPkgInit Hinit $$ [Hgs] as ⟨_, #Hpkg⟩
  · -- no package is initialized
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  wp_pures
  wp_apply Hf $$ [HP]
  · iframe
  ipureintro; rfl
```

### child `github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_NodeA`: [`Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Link.lean` lines 32-33](https://github.com/mit-pdos/perennial/blob/ddc0f0acc59a5730ad109be9ecfc4a485dcc4ea0/Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Link.lean#L32-L33) ([local copy](code/Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Link.lean))

```lean
theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_NodeA : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeA.spec (GF := GF) (hG := hG) :=
  github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeA.wp_proof github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.wp_Read github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.wp_Send github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_recvFrom
```

### child `github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_NodeB`: [`Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Link.lean` lines 35-36](https://github.com/mit-pdos/perennial/blob/ddc0f0acc59a5730ad109be9ecfc4a485dcc4ea0/Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Link.lean#L35-L36) ([local copy](code/Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Link.lean))

```lean
theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_NodeB : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeB.spec (GF := GF) (hG := hG) :=
  github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeB.wp_proof github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.wp_Read github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.wp_Write github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.wp_Send github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_recvFrom
```

### child `github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_NodeC`: [`Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Link.lean` lines 38-39](https://github.com/mit-pdos/perennial/blob/ddc0f0acc59a5730ad109be9ecfc4a485dcc4ea0/Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Link.lean#L38-L39) ([local copy](code/Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Link.lean))

```lean
theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_NodeC : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeC.spec (GF := GF) (hG := hG) :=
  github_com.mit_pdos.perennial.goose.testdata.examples.netfs.NodeC.wp_proof github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.wp_Send
```

How the parts fit. The parent's proof is the glue: one `refine
goose_dist_crash_adequacy …` (line 176) turns the system-level conclusion into
three holes, one per hypothesis of the adequacy theorem, plus the adequacy
theorem's own closing arguments. The lemma graph (each arrow is "is applied /
cited by the proof above it"):

```text
netfs_crash_safety_bounded
├── goose_dist_crash_adequacy      the adequacy instantiation (line 176)
│     └─ (reduces to goose_dist_crash_adequacy_blang, DistAdequacy.lean)
├── fsNet_globalStart              global setup: network points-to → netInv (line 184)
├── fsNet_localStart               first generation per node (lines 202, 220, 250)
├── fsNet_crashStart               after a crash: files' and address ghost state kept (line 299)
├── wp_boot                        the boot wrapper, applied per node (lines 285, 291, 295)
│     ├── wp_NodeA                 node "a": read "in", send c0, recvFrom (line 285)
│     ├── wp_NodeB                 node "b": read "sent" / receive+write+mark+send (line 291)
│     └── wp_NodeC                 node "c": sends junk (line 295)
```

The three holes the glue fills are: (1) the global setup and the first
generation of every node; (2) every generation of every node — its boot
program and its next precondition; (3) the single-thread start bound. Hole 2
is where the move lives: `Hnode` (lines 130-135) establishes the three-way
disjunction `(i = 0 ∧ e = boot NodeA ∧ σ = σa) ∨ (i = 1 ∧ …) ∨ (i = 2 ∧ …)`
by `match i, Hes` on the list-membership proof `Hes`, and then `rcases Hnode
with … | … | …` (line 148) splits it, so each branch applies `wp_boot` to that
node's linked spec.

Each child is a good leaf — a self-contained statement whose proof closes on
its own or from named siblings:

- `goose_dist_crash_adequacy` is the project's generic distributed
  crash-adequacy theorem (its statement is the whole contract above). It closes
  on its own: its proof reduces the real-semantics claim to the bounded
  `goose_dist_crash_adequacy_blang` via `bdist_crash_nsteps_of_real`, then
  closes the three conjuncts with `realNotStuck_of_bounded` and
  `unrecoveredPanic_node`.
- `fsNet_globalStart`, `fsNet_localStart`, `fsNet_crashStart` are three
  one-line lemmas about the `[fsExt, netExt]` extension's start and crash ghost
  resources, each closed by a single `sep_elim` / `sep_mono` term.
- `wp_boot` lifts a spec of a function `f` (with the package initialized) into
  the WP of its boot program, closed by `wp_initialize'` and then the given
  `Hf`.
- `wp_NodeA` / `wp_NodeB` / `wp_NodeC` are the linked specs of the three
  nodes, one line each, closed by applying the node's `wp_proof` to its
  callees' specs (e.g. `wp_NodeA` applies `NodeA.wp_proof` to `fsext.wp_Read`,
  `netext.wp_Send` and `wp_recvFrom`).

The glue also reaches for Iris/GooseLang library lemmas that are not shown as
children because they are generic infrastructure, not lemmas written for this
result: `intoVal_ne_PanicV` (line 177), `BigSepM.bigSepM_delete` /
`bigSepM_lookup` (lines 185-225), `inv_alloc` (190, 228), `goodMsgs_empty`
(195), `fsPointsto_persist` (205), `dghostVar_alloc` (227),
`LawfulPartialMap.get?_delete_ne` (188, 224).

Below `wp_NodeA`, the proof is itself a chain of project lemmas: `wp_NodeA`
cites `wp_recvFrom` (Link.lean 33), and `wp_recvFrom` cites
`recvFrom.wp_proof` and `netext.wp_Recv` (Link.lean 29-30) — a chain of depth
3 below the main theorem. The unbounded statement `netfs_crash_safety`
(Results.lean 329-352) is a thin wrapper that instantiates
`netfs_crash_safety_bounded` with `N = n + 1`, `T = n + 2` and the ghost state
`fsNetGF`; the bounded theorem is the reusable core.

## Why it is good

1. The parent proof opens by citing the adequacy theorem
   `goose_dist_crash_adequacy`, so the whole system-level safety conclusion is
   obtained from one generic theorem rather than re-proved here (check; parent
   site lines 157-311).
2. `fsNet_localStart` occurs exactly 3 times in Results.lean — once per node in
   the first-generation setup — which is the three-way split made concrete
   (check; Results.lean lines 202, 220, 250).
3. No `sorry`, `admit` or `axiom` occurs anywhere in Results.lean, so every
   branch and both theorems in the file close (check; Results.lean lines
   1-358).
4. The `netfs_crash_safety_bounded` site (statement and proof) spans 155 lines
   (Results.lean 157-311), assembled from 8 named lemmas cited directly, and
   the longest chain of project lemmas below it that I checked is 3
   (`wp_NodeA` → `wp_recvFrom` → `recvFrom.wp_proof`, Link.lean 29-33)
   (measurement).
5. The authors state the file's goal in the header comment — "the distributed
   crash safety of the three-node system, on the network and the filesystem"
   (Results.lean 2-4) — and the theorem's own doc comment says it is
   "`goose_dist_crash_adequacy` for the system" (Results.lean 154-156)
   (author-statement).

In my opinion the detail worth copying is not the case split itself — a
three-way `rcases` is unremarkable — but the pairing of a *generic* adequacy
theorem with a *per-component* case split: the adequacy theorem supplies the
global soundness argument once, and the split reduces "for every node" to three
parallel applications of a shared boot wrapper, so each branch is one
`iapply wp_boot …`.

## When to use it, and when not

Use it for a safety property over a *finite, enumerable* family of system
components, when a generic adequacy (or simulation) theorem already reduces the
whole-system claim to a per-component obligation, and each component has its
own linked spec (`wp_NodeA`/`B`/`C`) plus a shared wrapper (`wp_boot`) that
folds the branches together. The split on the component index is the natural
way to turn "for every node" into closed per-node goals.

Do not use it when the number of components is large or unbounded — a case
split does not scale, and the exhaustiveness obligation grows with the list.
Avoid it when the components need genuinely different arguments that do not
fit a shared wrapper, or when exhaustiveness of the index is not trivially
decidable from a list-membership proof (`match i, Hes` here relies on `Hes`
being the membership of a three-entry list).

## Consequences

The split creates an exhaustiveness obligation — `i = 0 ∨ i = 1 ∨ i = 2` must
cover every node of the system — discharged here by `match i, Hes` on the
list-membership proof `Hes`, which enumerates the three-entry `system` list.
Each branch must rebuild the node precondition `nodePre` and apply `wp_boot`
to the right node's linked spec; nodes that need different resources (`"b"`
carries a files invariant `bInv`, `"c"` is trivial) are handled inside the
parallel branches, so the branches are not literally identical. The adequacy
instantiation also leaves two further obligations — the global setup and the
thread bound — which are not part of the split and must be discharged
separately (by `fsNet_globalStart` and the single-thread start facts). If a
new node is added to `system`, both the disjunction in `Hnode` and the list it
is proved from must be extended together, or the split silently fails to
cover it.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: goose_dist_crash_adequacy@Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean:176, fsNet_globalStart@Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean:184, fsNet_localStart@Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean:202, fsNet_crashStart@Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean:299, wp_boot@Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean:285, github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_NodeA@Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean:285, github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_NodeB@Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean:291, github_com.mit_pdos.perennial.goose.testdata.examples.netfs.wp_NodeC@Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean:295; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, goose_dist_crash_adequacy) -> cites: goose_dist_crash_adequacy occurs at Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean:176 | check_claims.py |
| 2 | verified | count(fsNet_localStart, 3, Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean) -> count: fsNet_localStart occurs 3 times in 1 file(s) matching Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean | check_claims.py |
| 3 | verified | no_sorry(Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean, 1-358) -> no_sorry: none of sorry, admit, axiom in Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs/Results.lean:1-358 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/mit-pdos/perennial at commit `ddc0f0acc59a5730ad109be9ecfc4a485dcc4ea0`, under `LicenseRef-unknown`; see the [source note](../../sources/perennial/SOURCE.md) for the licence text and attribution.
