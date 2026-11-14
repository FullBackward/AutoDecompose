# Interface lemma source_activation_sound: coverage obligations to source soundness

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | isabelle |
| Status | accepted |
| Source | [voblint-verification-master-thesis](../../sources/voblint-verification-master-thesis/SOURCE.md) at `07ecd3a886ef` |
| Licence | `BSD-3-Clause` |

## Intent

A source-level soundness theorem is reduced to the five local coverage
obligations (entry, edge, call, combine, totality) by routing them through the
`activation_coverage` locale: the proof interprets the locale once, reads the
collecting cap off `activation_collect_sound` and the context witness off
`valid_activation_trace_has_context`, then hands both to
`source_sound_from_collecting_cap`. Nothing concrete — no analysis, domain or
routing policy — appears in the proof, only the two abstraction boundaries.

## The decomposition

### parent `source_activation_sound`: [`src/Analyses/Shared/Result/Source_Activation_Sound.thy` lines 79-117](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/07ecd3a886efa3a5744caabc19fbb301a40384a5/src/Analyses/Shared/Result/Source_Activation_Sound.thy#L79-L117) ([local copy](code/src/Analyses/Shared/Result/Source_Activation_Sound.thy))

```isabelle
theorem source_activation_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::numeric_domain abs_state"
    and adm :: "'c context_policy" and c\<^sub>0 :: 'c
  assumes wf: "wf_compile_input \<G> Pi ps"
    and s0: "s0 \<in> S"
    and run: "\<G>, Pi \<turnstile> (main_body Pi, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
    and ENTRY_G: "\<And>x. x \<in> S \<Longrightarrow> x \<in> \<gamma> (sg (Inl (cfg_entry (compile_prog Pi ps), c\<^sub>0)))"
    and EDGE: "\<And>u a v c x x'. (u, a, v) \<in> intra (compile_prog Pi ps)
        \<Longrightarrow> x \<in> \<gamma> (sg (Inl (u, c))) \<Longrightarrow> x' \<in> edge_step a x
        \<Longrightarrow> x' \<in> \<gamma> (sg (Inl (v, c)))"
    and CALL: "\<And>u dst pars args p cont c c' x.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> x \<in> \<gamma> (sg (Inl (u, c)))
        \<Longrightarrow> c' \<in> adm u c (call_info_of (CallEdge dst pars args) p) x
              (call_enter \<G> (CallEdge dst pars args) x)
        \<Longrightarrow> call_enter \<G> (CallEdge dst pars args) x \<in> \<gamma> (sg (Inl (FunctionEntry p, c')))"
    and COMB: "\<And>cl dst pars args p cont c1 c' p' x t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> x \<in> \<gamma> (sg (Inl (cl, c1)))
        \<Longrightarrow> admits_call_context \<G> (compile_prog Pi ps) adm cl c1 p' x es c'
        \<Longrightarrow> t \<in> \<gamma> (sg (Inl (FunctionResult p, c')))
        \<Longrightarrow> combine_collect \<G> dst x t \<in> \<gamma> (sg (Inl (cont, c1)))"
    and TOTAL: "call_context_total_on (\<lambda>v c. \<gamma> (sg (Inl (v, c)))) adm \<G> (compile_prog Pi ps)"
  shows "\<exists>v stk t c. Pi, compile_prog Pi ps, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                   \<and> activation_context_rel \<G> adm c\<^sub>0 (compile_prog Pi ps) t c
                   \<and> s \<in> \<gamma> (sg (Inl (v, c)))"
proof -
  interpret G: activation_coverage "compile_prog Pi ps" S "\<lambda>v c. \<gamma> (sg (Inl (v, c)))" adm c\<^sub>0 \<G>
    by (standard; blast intro: ENTRY_G EDGE CALL COMB TOTAL)
  have cap: "\<And>v ctx. \<A>\<^bsub>\<G>,adm,c\<^sub>0,compile_prog Pi ps,S\<^esub> v ctx
                     \<subseteq> \<gamma> (sg (Inl (v, ctx)))"
    by (rule activation_collect_sound[OF G.activation_coverage_axioms])
  have has_ctx: "\<And>t. t \<in> \<T>\<^bsub>\<G>,compile_prog Pi ps,S\<^esub>
                   \<Longrightarrow> \<exists>c. activation_context_rel \<G> adm c\<^sub>0 (compile_prog Pi ps) t c"
    using G.valid_activation_trace_has_context by blast
  show ?thesis
    by (rule source_sound_from_collecting_cap[where \<gamma>\<^sub>M=gamma_state,
          OF wf s0 run has_ctx cap])
qed
```

### child `activation_collect_sound`: [`src/Abstract_Interpreter/Framework/Activation/Activation_Backbone.thy` lines 34-50](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/07ecd3a886efa3a5744caabc19fbb301a40384a5/src/Abstract_Interpreter/Framework/Activation/Activation_Backbone.thy#L34-L50) ([local copy](code/src/Abstract_Interpreter/Framework/Activation/Activation_Backbone.thy))

```isabelle
theorem activation_collect_sound:
  assumes "activation_coverage g S cover adm c\<^sub>0 \<G>"
  shows "\<A>\<^bsub>\<G>,adm,c\<^sub>0,g,S\<^esub> v c \<subseteq> cover v c"
proof -
  interpret G: activation_coverage g S cover adm c\<^sub>0 \<G> by (fact assms)
  show ?thesis
  proof (rule subsetI)
    fix st assume "st \<in> \<A>\<^bsub>\<G>,adm,c\<^sub>0,g,S\<^esub> v c"
    then obtain t where t: "t \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
      and sn: "sink_node t = v" and kc: "activation_context_rel \<G> adm c\<^sub>0 g t c"
      and st: "sink_store t = st"
      by (rule activation_collect_E)
    have "sink_store t \<in> cover (sink_node t) c" using G.valid_activation_trace_covered_at[OF t kc]
      .
    then show "st \<in> cover v c" using sn st by simp
  qed
qed
```

### child `valid_activation_trace_has_context`: [`src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy` lines 256-259](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/07ecd3a886efa3a5744caabc19fbb301a40384a5/src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy#L256-L259) ([local copy](code/src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy))

```isabelle
theorem valid_activation_trace_has_context:
  assumes "t \<in> \<T>"
  obtains c where "carries t c"
  using valid_activation_trace_covered[OF assms] by (rule trace_covered_someE)
```

### child `source_sound_from_collecting_cap`: [`src/Analyses/Shared/Result/Source_Activation_Sound.thy` lines 19-46](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/07ecd3a886efa3a5744caabc19fbb301a40384a5/src/Analyses/Shared/Result/Source_Activation_Sound.thy#L19-L46) ([local copy](code/src/Analyses/Shared/Result/Source_Activation_Sound.thy))

```isabelle
theorem source_sound_from_collecting_cap:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'M"
    and \<gamma>\<^sub>M :: "'M \<Rightarrow> store set"
    and adm :: "'c context_policy" and c\<^sub>0 :: 'c
  assumes wf: "wf_compile_input \<G> Pi ps"
    and s0: "s0 \<in> S"
    and run: "\<G>, Pi \<turnstile> (main_body Pi, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
    and has_ctx: "\<And>t. t \<in> \<T>\<^bsub>\<G>,compile_prog Pi ps,S\<^esub>
                   \<Longrightarrow> \<exists>c. activation_context_rel \<G> adm c\<^sub>0 (compile_prog Pi ps) t c"
    and cap: "\<And>v ctx. \<A>\<^bsub>\<G>,adm,c\<^sub>0,compile_prog Pi ps,S\<^esub> v ctx
                       \<subseteq> \<gamma>\<^sub>M (sg (Inl (v, ctx)))"
  shows "\<exists>v stk t c. Pi, compile_prog Pi ps, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                   \<and> activation_context_rel \<G> adm c\<^sub>0 (compile_prog Pi ps) t c
                   \<and> s \<in> \<gamma>\<^sub>M (sg (Inl (v, c)))"
proof -
  let ?g = "compile_prog Pi ps"
  from source_store_in_activation_collect
         [where adm=adm and c\<^sub>0=c\<^sub>0,
          OF wf s0 run has_ctx]
  obtain v stk t c where m:
    "Pi, compile_prog Pi ps, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
    and ck: "activation_context_rel \<G> adm c\<^sub>0 ?g t c"
    and mem: "s \<in> \<A>\<^bsub>\<G>,adm,c\<^sub>0,?g,S\<^esub> v c"
    by blast
  have "s \<in> \<gamma>\<^sub>M (sg (Inl (v, c)))"
    using cap[of v c] mem by blast
  then show ?thesis using m ck by blast
qed
```

How the parts fit. The parent's proof is four steps, all at the abstraction
boundary:

1. `interpret G: activation_coverage "compile_prog Pi ps" S "\<lambda>v c. \<gamma> (sg (Inl (v, c)))" adm c\<^sub>0 \<G>`
   by `(standard; blast intro: ENTRY_G EDGE CALL COMB TOTAL)` (lines 106-107):
   the five coverage assumptions become one locale instance `G`. The cover is
   the lambda over the abstract map, so no concrete domain or policy leaks
   into the step.
2. `have cap: ... by (rule activation_collect_sound[OF G.activation_coverage_axioms])`
   (lines 108-110): the collecting cap, read off the child
   `activation_collect_sound` with the freshly interpreted
   `G.activation_coverage_axioms` as its premise.
3. `have has_ctx: ... using G.valid_activation_trace_has_context by blast`
   (lines 111-113): the context witness, read off the locale theorem
   `valid_activation_trace_has_context`.
4. `show ?thesis by (rule source_sound_from_collecting_cap[where \<gamma>\<^sub>M=gamma_state, OF wf s0 run has_ctx cap])`
   (lines 114-116): both handed to the cap-consuming theorem
   `source_sound_from_collecting_cap`, with the concretization fixed to
   `gamma_state`.

Lemma graph (which lemma uses which, read from the copied files):

- `source_activation_sound` (parent) uses `activation_collect_sound`,
  `valid_activation_trace_has_context`, `source_sound_from_collecting_cap`.
- `source_sound_from_collecting_cap` uses `source_store_in_activation_collect`
  (the source bridge, declared outside these files) plus its own `cap`
  assumption.
- `activation_collect_sound` uses `activation_collect_E` and
  `valid_activation_trace_covered_at`.
- `valid_activation_trace_has_context` uses `valid_activation_trace_covered`
  and `trace_covered_someE`.
- `valid_activation_trace_covered_at` uses `valid_activation_trace_covered`;
  `valid_activation_trace_covered` uses `caller_chain_covered`;
  `caller_chain_covered` uses the four closure lemmas `init_covered`,
  `intra_covered`, `call_covered`, `return_covered`, each of which closes from
  the locale assumptions.

Why each child is a good leaf:

- `activation_collect_sound` is a self-contained statement — a cover satisfying
  the locale bounds the context-indexed buckets — whose proof only interprets
  the locale and reads off `valid_activation_trace_covered_at`; it knows
  nothing about source programs.
- `valid_activation_trace_has_context` is a one-line leaf: every valid trace
  carries a context, closing from `valid_activation_trace_covered` by
  `trace_covered_someE`.
- `source_sound_from_collecting_cap` is the client-facing cap-consumer: given a
  cap and a context witness it yields the source-level inclusion, closing from
  the source bridge `source_store_in_activation_collect`; it is parametrised
  over the concretization `\<gamma>\<^sub>M`, which is what lets the parent instantiate
  it at `gamma_state`.

## Why it is good

1. The name `source_sound_from_collecting_cap` occurs in the parent site (the
   glue's final application, line 115) (`check`, permalink lines 79-117).
2. The name `activation_collect_sound` occurs in the parent site (line 110)
   (`check`, permalink lines 79-117).
3. The name `valid_activation_trace_has_context` occurs in the parent site
   (line 113) (`check`, permalink lines 79-117).
4. The shape is theorem scale: `direct_lemmas = 3`
   (`activation_collect_sound`, `valid_activation_trace_has_context`,
   `source_sound_from_collecting_cap`), `glue_lines = 39` (lines 79-117),
   `child_lines = [17, 4, 28]`, and `depth = 5` along the chain
   `activation_collect_sound -> valid_activation_trace_covered_at ->
   valid_activation_trace_covered -> caller_chain_covered ->
   init_covered/intra_covered/call_covered/return_covered` (`measurement`,
   counted from the site ranges and the copied files).
5. The authors state the move in the file's own comment: "Given entry, edge,
   call, combine and totality obligations on the abstract map,
   activation_coverage builds the cap and the composition above yields
   source-level soundness." (`author-statement`, lines 73-77).

In my opinion the detail worth copying is the two fixed points of contact: the
single `interpret` step that packages the five obligations as a locale
instance, and the `gamma_state` instantiation of the cap-consumer's free
concretization. Between them the proof needs no other idea, so a new analysis
instance replaces only the five assumptions and the map `sg`.

## When to use it, and when not

Use it when the obligations are already packaged as a locale (or a
structure/interface), a separate lemma already turns a satisfying cover into
the collecting cap (`activation_collect_sound`), and a second lemma supplies
the existential context witness (`valid_activation_trace_has_context`); then
the main theorem only interprets the locale and chains the two through a
cap-consuming theorem.

Avoid it when the obligations are not yet packaged, so each must be discharged
inline; when the cap-consuming theorem's statement is too strong or too weak
for the client (it fixes the concretization via `gamma_state`, so a non-numeric
domain needs its own corollary); or when the proof must mention a specific
analysis or routing policy.

## Consequences

The move creates no new obligations beyond those the locale interpretation
discharges in one step (`standard; blast intro: ENTRY_G EDGE CALL COMB TOTAL`).
The cost is two fixed points of contact: the cap lemma's cover parameter must
match the interpreted locale (the lambda `\<lambda>v c. \<gamma> (sg (Inl (v, c)))`), and
the cap-consuming theorem's concretization is instantiated to `gamma_state`.
Failure modes: a domain or policy that does not fit `gamma_state` needs its own
corollary — the file already carries `source_sound_toplevel_from_collecting_cap`
and `source_sound_from_node_collect_cap` for the other shapes — and if the five
obligations are renamed or reordered, the single `interpret` step stops
matching.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/ci.yml job isabelle-build runs 'pixi run isabelle-build' -> scripts/mk/build.sh -> 'isabelle build ... Voblint_Examples'; Voblint_Examples -> Voblint_Examples_CLI -> Voblint_CLI -> Voblint_Analysis_Int -> Voblint_Nonrelational -> Voblint_Result (src/Analyses/Shared/Result/ROOT), whose theories include Source_Activation_Sound.thy; commit 07ecd3a886efa3a5744caabc19fbb301a40384a5 on default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: activation_collect_sound@src/Analyses/Shared/Result/Source_Activation_Sound.thy:110, valid_activation_trace_has_context@src/Analyses/Shared/Result/Source_Activation_Sound.thy:113, source_sound_from_collecting_cap@src/Analyses/Shared/Result/Source_Activation_Sound.thy:115; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at 07ecd3a886efa3a5744caabc19fbb301a40384a5 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, source_sound_from_collecting_cap) -> cites: source_sound_from_collecting_cap occurs at src/Analyses/Shared/Result/Source_Activation_Sound.thy:115 | check_claims.py |
| 2 | verified | cites(parent, activation_collect_sound) -> cites: activation_collect_sound occurs at src/Analyses/Shared/Result/Source_Activation_Sound.thy:110 | check_claims.py |
| 3 | verified | cites(parent, valid_activation_trace_has_context) -> cites: valid_activation_trace_has_context occurs at src/Analyses/Shared/Result/Source_Activation_Sound.thy:113 | check_claims.py |
| 4 | verified | shape numbers re-derived: glue_lines 79-117 = 39 lines; child_lines: Activation_Backbone.thy 34-50 = 17, Activation_Trace_Abstract.thy 256-259 = 4, Source_Activation_Sound.thy 19-46 = 28; direct_lemmas = 3 (all three children cited in glue at Source_Activation_Sound.thy:110,113,115); depth chain verified in code: activation_collect_sound (Activation_Backbone.thy:34-50) calls valid_activation_trace_covered_at (:261), which uses valid_activation_trace_covered (:249), which uses caller_chain_covered (:216), which discharges init_covered/intra_covered/call_covered/return_covered -> depth 5 | verifier |
| 5 | verified | read code/src/Analyses/Shared/Result/Source_Activation_Sound.thy lines 70-76: text block reads 'Given entry, edge, call, combine and totality obligations on the abstract map, activation_coverage builds the cap and the composition above yields source-level soundness. The node-collect variants restate it per CFG node.' — the quoted sentence appears verbatim at lines 73-75 (the cited L73-L77) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent site 79-117 matches code; glue cites exactly the 3 children (activation_collect_sound@110, valid_activation_trace_has_context@113, source_sound_from_collecting_cap@115) and no other named lemma; the interpret step uses the 5 assumptions, not a lemma. Child declarations and closed_by fields match: activation_collect_sound (34-50) closed by subsetI/activation_collect_E/valid_activation_trace_covered_at; valid_activation_trace_has_context (256-259) closed by valid_activation_trace_covered + trace_covered_someE; source_sound_from_collecting_cap (19-46) closed by source_store_in_activation_collect + cap. Proof closes (qed at 117). Shape numbers correct: glue_lines=39 (79..117), child_lines=[17,4,28] (34..50, 256..259, 19..46), direct_lemmas=3, depth=5 along activation_collect_sound->valid_activation_trace_covered_at(261)->valid_activation_trace_covered(249)->caller_chain_covered(216)->init/intra/call/return_covered. Author comment at 73-77 quotes as claimed. | reviewer-correctness |
| generality | accept | Move is stated generically: intent and applicability.use_when frame it as 'obligations packaged as a locale (or structure/interface), a cap lemma, a context-witness lemma, chained through a cap-consuming theorem', with the Voblint names only as parenthetical examples, and goal_shape names the generic shape without concrete domain/policy. When-not-to-use is specific and honest, each branch grounded in the code I read: 'obligations not yet packaged' (discharge inline), 'cap-consumer too strong/weak for the client (fixes concretization via gamma_state)' matches the gamma_state instantiation at Source_Activation_Sound.thy:115 and the header comment (lines 12-15) that corollaries read at gamma_state while the cap-consuming theorem is parametrised over gamma_M, and the sibling corollaries source_sound_toplevel_from_collecting_cap (line 50) and source_sound_from_node_collect_cap (line 152) do exist; 'proof must mention a specific analysis/routing policy' matches the intent claim that nothing concrete appears. Consequences name real costs (two fixed points of contact: the cover lambda and gamma_state) and a real failure mode (renamed/reordered obligations break the single interpret step). Good-leaves question is answered: README 'Why each child is a good leaf' says activation_collect_sound is self-contained and knows nothing about source programs, valid_activation_trace_has_context is a one-line leaf, source_sound_from_collecting_cap is client-facing and parametrised over the concretization. Minor wording nit only: avoid_when's parenthetical 'it fixes the concretization via gamma_state' could be misread as attributing the fixing to the cap-consuming theorem rather than the corollary, but the header comment and the leaves section state the correct relationship, so it does not mislead. | reviewer-generality |
| provenance-licence | accept | Provenance check passes (3 files byte-identical at 07ecd3a886efa3a5744caabc19fbb301a40384a5). Commit, licence (BSD-3-Clause) and every permalink agree across entry.json, source.json, SOURCE.md and README; upstream-LICENSE is BSD 3-Clause text; author-statement locator #L73-L77 verified in the copied Source_Activation_Sound.thy. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis at commit `07ecd3a886efa3a5744caabc19fbb301a40384a5`, under `BSD-3-Clause`; see the [source note](../../sources/voblint-verification-master-thesis/SOURCE.md) for the licence text and attribution.
