# K. Experiments and measurements bearing on rule-based decomposition: what was measured, on what data, with what result (as of 2026-11-15)

Prepared 2026-11-15 for AutoDecompose, which decomposes hard goals into lemmas by rules and measures
tokens per closed leaf (model fixed, harness varied) and decomposition correctness: whether a
generated lemma is true, well-typed in context and sufficient for its parent. The library of 229
harvested decompositions is about to receive a deterministic feature extractor. This survey reports
the experiments already done that bear on both: the question asked, the data, the design, the
number, and what the number does not show. Mechanisms (proof planning, theory exploration, cut
introduction, learned subgoal generation, verification-condition splitting) belong to survey J;
where a paper belongs to both, the numbers are here and the method gets one line. Facts in surveys
A-I are cited as [A §x] to [I §x] and not repeated.

Method. (i) Web search, then a fetch tool that returns extracts of arXiv HTML, ar5iv and repository
pages. A quotation is a string the extract returned; a number is the extract's transcription of the
paper's table or text, and where the extract found a paper inconsistent with itself I repeat the
inconsistency. Pages longer than 100,000 characters were read to that point unless stated. (ii) Ten
PDFs converted with `pdftotext` and read directly; Corneli et al. 2018 was read by keyword only.
(iii) One Isabelle documentation source file and three repository READMEs. (iv) For §1.5, added
afterwards, 25 more sources were downloaded whole and searched as text: ten PDFs converted with
`pdftotext` and fifteen arXiv or ar5iv HTML pages; three figures of one paper were rendered from its
SVG files and read as images. The numbers of §1.5 are my readings of the tables and text, not a
fetch tool's transcription. Tags as in [F]: **[P]** read in the primary source during this survey
("pdf" inside the tag marks my own reading of a converted PDF); **[S]** secondary, or from memory;
**[U]** unverified or not found. "My arithmetic" marks sums and ratios of my own. The source index
lists 85 sources read as [P]: 60 for the first draft and the 25 of §1.5.

Could not be fetched or found: any work dated after 2026-11-11 that adds to [F §7 field 11] (two
searches); any study that reports, per generated subgoal of a decomposition, the rates of false,
ill-typed, insufficient and unused statements (two searches); any corpus of proofs labelled with
proof techniques that reports inter-annotator agreement (two searches); node, depth or fan-out
statistics for the PFR, FLT or sphere-eversion blueprints beyond [H §2.4]; Pease and Martin 2012
itself (known through Corneli et al. 2018); Jeffery et al. 2015; the degree statistics of the
Mathlib network paper, §6 of FormaTheoria and the per-library sizes of MLFMF (truncated pages); how
Paperproof extracts its tree. Staples et al. 2014 and Matichuk et al. 2015 were not re-read; [D
§1.5] has them. Five leads I took from memory were wrong in detail and are corrected in §8. For this
survey's §1.5: the OOPSLA paper on lfind (TLS error at the authors' copy, 403 at the publisher), so
chapter 2 of the first author's thesis was read, its PDF refused to `curl` and obtained through the
fetch tool; any rate of false or unproved proposals for ProD-RL, the BFS-Prover-V2 planner, DSP+,
Lemur or CCLemma; any benchmark for Hipster or for the prover of Ganesalingam and Gowers.

---

## 0. Findings in brief

1. **A human decomposition handed to a fixed model has been tested once at lemma grain, and the sign
   was mixed.** Cobblestone's PerfDecomp oracle moved GPT-4 from 38 % to 52 % on one set of 100 Coq
   theorems and from 48 % to 47 % on another [P] (§1.1).
2. **Human informal proofs are worth little more than machine ones as input to a sketcher.** DSP:
   39.3 % against 38.9 % on miniF2F-test at 100 attempts, reversed beyond 130 attempts; LEGO-Prover:
   50.0 against 45.5; RLMEval: the blueprint's informal proof adds about 1.5 points; FormalMATH:
   adding a written solution to chain-of-thought prompting lowered success [P] (§1.1; DSP+ in §1.5).
3. **A project's own auxiliary lemmas are worth about six points to a 7B prover.** RLMEval,
   pass@128: 8.76 % with blueprint theorems only, 14.70 % with every project lemma available.
   Auxiliary lemmas are 68.3 % of the theorems in those six projects and have 6.6 proof lines
   against 16.6 [P] (§1.1, §2.2).
4. **"Model fixed, harness varied" has more precedents than [E §0.7] lists, but none other with
   matched budgets.** SorryDB (one model: 10.8 % single shot, 27.9 % self-correcting, 30.3 %
   agentic), Cobblestone (GPT-4: 25 % to 48 %), miniCTX (GPT-4o: 11.72 % to 27.08 % with file
   context) [P] (§1.3; see finding 12).
5. **Per-subgoal error rates are still unreported for decomposition.** The nearest numbers are for
   stand-alone statements: MathlibLemma's funnel (9,148 proposed, 4,317 compile, 1,506 proved; 54 %
   of a sample of rejected ones false) and IsarStep (58 % of generated intermediate propositions
   well-formed, 27.6 to 29.4 % correct) [P] (§1.4; see finding 12).
6. **Statement size does not predict proof size outside verification developments.** Across the AFP
   about half the articles fit the seL4 quadratic relation with R² below 0.5, and the coefficients
   span 0.07 to 21.29; on Mizar there are "no clear relationships" [P, pdf] (§2.1). [D §1.5] should
   carry this caveat.
7. **Human corpora are shallow inside a proof and deep across the library.** AFP 2015: 48,755 of
   64,497 lemmas have proof depth 1 and almost 99 % depth 4 or less. Mathlib: declaration DAG depth
   84. An AI-built development of 30,298 declarations: median depth 2, root depth 458 [P] (§2.2,
   §2.3).
8. **The nearest precedent for "predict the move from the goal" is PaMpeR, and it needs the
   prover.** From 108 hand-written assertions on the proof state it puts `induct` among its top five
   recommendations 27 % of the time and `cases` among its top four 16 %, against 58 to 60 % top-1
   for `simp` and `auto`. sem_ind ranks the human's induction arguments first 38.2 % of the time on
   1,095 problems [P] (§4). No study predicts a lemma-level move, none uses text alone, and no
   labelled corpus of moves reports inter-annotator agreement.
9. **Structure adds to names, and names carry most of the signal.** Symbols alone against structural
   term features: 998 against 1,130 of 2,078 Mizar problems. Node names alone against the formula
   graph: 81.5 against 90.3 % on HolStep. Hiding variable names: 49.95 down to 37.36 % on HOList.
   TF-IDF on text against node2vec on the reference graph: 0.51 against 0.95 to 0.98 link-prediction
   accuracy [P] (§3).
10. **Retrieving similar proofs is the largest feature effect measured with a language model.**
    Rango: BM25 over the proof states of proofs in the same project, 20.4 % to 30.0 % of 500 Coq
    theorems; lemma retrieval adds one point [P] (§3).
11. **The one learned lemma proposer with a no-lemma arm gains little, and loses under supervised
    training.** ProD-RL on AFP theorems: with supervised fine-tuning, proposing lemmas lowers
    pass@16 from 43.4 to 40.8 %; with RL it reaches 45.5 %, which is 2.1 points above the no-lemma
    model, and 0.1 points above it out of distribution. A general LLM that plans subgoals for a
    fixed step prover adds more, at budgets that are not matched: 86.1 to 95.1 % on miniF2F-test in
    BFS-Prover-V2, 49.6 to 74.2 % in DSP+ [P] (§1.5).
12. **Outside the LLM provers the step has been ablated with the base tool fixed, and the share of
    proposals rejected is reported.** CVC4 solves 10 and then 30 of the 66 benchmarks said to need
    lemmas, in one encoding, once it generates subgoals; a lemma from lfind raises a fixed prover
    from 22.1 to 49.1 % of 222 points; Houdini pruning adds 90 of 469 programs to Loopy at equal LLM
    calls; AutoVerus's table from error class to agent repairs 37 tasks, of which a generic agent
    repairs 17. A third of lfind's candidates are refuted before proof effort, 23.6 % of Lemmanaid's
    conjectures are false, and 12.4 % of AutoVerus's candidates are filtered as unsafe. Three of the
    four sets were selected as needing the step [P] (§1.5).

## 1. Measured effect of decomposition (block A)

[F §7 field 11] lists the ablations of 20 harnesses. This section adds oracle experiments, ablations
F lacks, fixed-model comparisons and error rates. I found nothing dated after 2026-11-11.
LeanHammer's ground-truth-premise oracle is in [B §B1].

### 1.1 Oracle experiments: a human decomposition, sketch or lemma set is supplied

**Cobblestone** (Kasibatla, Agarwal, Brun, Lerner, Ringer, First; ICSE 2026)
[P, https://arxiv.org/html/2410.19940v4]. Question: does outside partial progress help a
divide-and-conquer LLM prover (method: J). Data: four sets of 100 Coq theorems, two of which carry
the oracle runs; GPT-4. Design: model fixed; the PerfPrems oracle supplies the lemmas the human
proof uses, PerfDecomp a decomposing prefix of the human proof. Result (Fig. 13; Wigderson100 and
CoqGym100): no oracle 38 and 48 %; PerfPrems 43 and 50 %; PerfDecomp 52 and 47 %; union of the three
variants 55 and 58 % (the RQ4 text swaps the last pair). Cost: $1.25 and 14.7 minutes per run on
average; 59.3K tokens per theorem on CoqGym100. The same paper is the nearest thing to a
decomposition ablation in Coq (Figs. 7, 9, 10): whole-proof chain of thought with 20 samples 19 and
25 %; tactic-by-tactic with CoqHammer 33 and 40 %; Cobblestone 38 and 48 %, and 16 and 25 % without
the hammer. One invocation proves 31 of the 38 and 44 of the 48; recursion on failed subgoals adds
the rest. Not shown: two sets of 100; GPT-4 "has potentially seen CoqGym"; the authors say the
oracle results "do not indicate how an interactive, semi-automated approach may perform"; no arm
matches tokens.

**DSP, human against machine drafts** (Jiang et al., ICLR 2023)
[P, https://ar5iv.labs.arxiv.org/html/2210.12283]. Data: miniF2F in Isabelle, Codex as sketcher, 100
sketches per problem. Result (Table 1, valid/test): human informal proof 42.6/39.3; Codex and
Minerva 8B 40.6/35.3; Minerva 62B 43.9/37.7; 540B 42.6/38.9. At 200 attempts human drafts solve 203
problems and 540B drafts 209; the latter "solve more problems than human proof drafts when more than
130 attempts are made per problem". With human drafts, removing in-line comments gives 37.7/36.5 and
removing the informal proof 38.9/34.0. Of 50 Minerva drafts checked by hand, 29 were correct, 16 had
one faulty step and 5 were nonsense. Not shown: there is one human draft per problem, sketched 100
times, against 100 different machine drafts, so authorship is confounded with diversity.

**LEGO-Prover** (Wang et al., ICLR 2024) [P, https://arxiv.org/html/2310.00656]. miniF2F valid/test,
ChatGPT, 100 attempts (Table 1): model-written informal proofs 52.4/45.5, human-written 55.3/50.0.
Ablation at 50 attempts, validation set only: 50.4 % with the growing lemma library, 47.1 % without.
Of 22,532 lemmas generated, 10.8 % came from the prover's own decompositions; "24%" of the 135
solved validation problems used a retrieved lemma. Not shown: any rate of false or unprovable
requested lemmas; one run per arm, about $300 each.

**RLMEval** (Poiroux, Bosselut, Kunčak; EMNLP Findings 2025)
[P, https://arxiv.org/html/2510.25427v1]. Data: 613 blueprint theorems from six Lean projects.
Design: "easy" mode exposes every project lemma, "normal" mode "only blueprint theorems"; the
proof-autoformalisation task adds the blueprint's informal proof. Result (Tables 5 and 6, pass@128,
normal/easy): DeepSeek-Prover-V2-7B 8.76/14.70 without the informal proof and 10.33/16.74 with it;
all five models gain from easy mode without the informal proof, and four of the five with it. Easy
mode is an oracle for the lower half of the human decomposition: the auxiliary lemmas exist and are
proved. Not shown: 7B provers only, no agent; no arm supplies auxiliary statements without their
proofs; some informal proofs "can be cryptic without broader project context".

**miniCTX** (Hu et al., ICLR 2025) [P, https://arxiv.org/html/2408.03350]. 762 theorems from six
projects. GPT-4o whole-proof 11.72 % on average, 27.08 % with the preceding file as context; a 1.3B
model tuned on file context 35.94 % against 19.53 % for state-tactic tuning (Table 3). Success is
"relatively low (19%)" where the human proof is longer than five lines. [B §B1] cites miniCTX-v2
only.

**IMO-Steps** (Yousefzadeh, Cao, Ospanov 2024) [P, https://arxiv.org/html/2411.18872]. The authors
proved 17 IMO problems in Lean by hand and cut 13 of the proofs, by judgement, into 1,329 lemmas
(40,170 lines). Per-lemma results: DeepSeek-Prover-V1.5-RL 522 (39.3 %) and Goedel-Prover 504
(37.9 %) at 32 samples; o3-mini 316 (23.8 %) after ten feedback rounds. Not shown: no arm attempts
the undecomposed problems at the same budget, so the gain from the decomposition is not measured;
lemmas that existing automation proved were left out, by the extract's account.

**FormalMATH** (Yu et al. 2025) [P, https://arxiv.org/html/2505.02735]. On the 425-problem Lite set
at 3,200 samples, DeepSeek-Prover-V1.5-SFT reaches 47.0 % plain, 50.6 % with chain of thought and
49.2 % with a natural-language solution added to it; the RL model 49.8, 51.7 and 51.2 (§4.3). The
solution lowers success against chain of thought, not against plain prompting.

### 1.2 Ablations of decomposition and of lemma extraction that F lacks

- **Subgoal-based demonstrations** (Zhao, Li, Kong 2023) [P, https://arxiv.org/html/2305.16366].
  Isabelle, miniF2F, 100 LLM calls. Table 2, valid/test: full method 48.0/45.5; without
  subgoal-structured demonstrations 44.3/40.6; without learned ordering of demonstrations 47.5/44.3;
  without both 41.8/38.5. The subgoal proofs were refined by ChatGPT against the prover; no rate of
  rejected subgoals is given.
- **ProofFlow** (Cabral et al., ICLR 2026) [P, https://arxiv.org/html/2510.15981v1]. 184
  undergraduate proofs, each step formalised as a Lean lemma. ProofScore with the dependency DAG
  enforced 0.545, without 0.417, whole-proof 0.123, step-by-step 0.072 (Table 1, stronger models,
  pass@5); with weaker models 0.355 against 0.347. The DAG pipeline uses 94.2K output tokens and
  31.8 minutes per problem, whole-proof 76.7K and 10.7. Sources of step-level failure with the DAG,
  over 1,737 steps (Table 2): none 53.3 %, formaliser 38.9 %, tactic completion 5.6 %, the NL
  statement 2.2 %.
- **Lemma mining before LLMs** (Kaliszyk and Urban 2014)
  [P, https://ar5iv.labs.arxiv.org/html/1402.3578]. Intermediate lemmas from kernel traces (about
  1.7 billion inference nodes for Flyspeck) are ranked by dependency-graph measures (§6, row 16) and
  the best are offered as premises. Core HOL Light, 1,954 theorems, 30 s: 63.1 % to 66.2 % for the
  14 best methods; in the fully chronological setting 61.7 % to 64.8 %. Flyspeck, 1,796 theorems:
  36.4 % to 44.2 % in union with the older methods; the authors call 5 % a "very conservative
  estimate".
- **REFACTOR** (Zhou, Wu, Li, Grosse; ICLR 2024) [P, https://arxiv.org/html/2402.17032]. A GNN marks
  the nodes of a Metamath proof tree that form an extractable lemma. It recovers the human lemma in
  19.6 % of unseen proofs (node accuracy 85.6 %); 1,907 new lemmas refactor 14,092 of 27,220
  theorems; a prover trained on the refactored corpus proves 632 of 2,720 test theorems against 557,
  and 31.0 % of its proofs use a new lemma.
- **TacMiner** (Xin et al., OOPSLA 2025) [P, https://arxiv.org/html/2503.24036]. 918 Coq proofs;
  mined tactics shrink the corpus by 26 %; Copra proves 30 of 50 selected theorems with them and 11
  without, "a relative increase of 172%".
- **LLM2Ltac** (Fang, Yao, Xiong 2026) [P, https://arxiv.org/html/2605.08694]. An LLM names the
  strategy behind each tactic of 11,725 Rocq library proofs and writes it as Ltac. Of 49,909 tactics
  mined by GPT-5.2, 16,902 compile and 5,766 generalise; CoqHammer proves 1,950 of 6,199 theorems
  with them (1,972 with a DeepSeek-mined set) against 1,592. No list of strategy kinds and no human
  check of the labels is given; one parameter was tuned on the evaluation sets.

### 1.3 Model fixed, harness varied

[E §0.7] names AutoformBot as the one precedent and [F §6.3] reads h1; [A §4.7] and [B §C1] carry
the Minimal Agent ablation. Three more exist. (i) **SorryDB** (Letson, Sarra et al. 2026)
[P, https://arxiv.org/html/2603.02668v1]: 1,000 `sorry` tasks sampled from 5,663 in 78 repositories.
Gemini Flash 3 fills 10.8 % with one sample, 20.5 % with 32, 27.9 % when self-correcting for up to
16 iterations and 30.3 % as an agent; Claude Opus 4.5 goes 7.8, 15.4, 27.1 %; a fixed tactic list
fills 8.4 %; the union of all approaches 35.7 % (Table 1). "with just 16 model calls, iterative
approaches strongly outperform any single-shot approach". The authors "do not know how many tasks
are actually unsolvable because they are unprovable" and give no breakdown by goal feature or proof
length. (ii) Cobblestone (§1.1): several harnesses on GPT-4; it also beats chain of thought on
GPT-3.5 and Claude 3 Opus (Fig. 8). (iii) miniCTX (§1.1). None of the three matches token budgets
across arms; AutoformBot does [E §1.4].

### 1.4 Rates of false, ill-typed or insufficient generated statements; cost

[F §9, "Missing", item 2] found no per-lemma error rates. I found none for decomposition by an LLM
prover either; lfind, Lemmanaid, kSubS and AutoVerus report rejection rates for their own proposals
(§1.5). The nearest measurements for LLM provers are these.

- **MathlibLemma** (Liu et al. 2026) [P, https://arxiv.org/html/2602.02561v3]. An LLM proposes
  "folklore" lemmas near Mathlib files. Funnel (Table 1; totals are my arithmetic): 9,148 proposed;
  6,150 pass an LLM judge; 4,317 of those compile (70 %); 289 fall to `aesop`; 4,028 remain; 1,506
  are proved by the union of seven provers (37.39 %), the best single one reaching 19.39 %. Audits:
  of 53 judge-rejected statements "54% were indeed mathematically false"; experts proved 107 of 138
  sampled unproved statements, the usual defect of the rest being a missing hypothesis. These are
  stand-alone lemmas, so sufficiency does not arise.
- **IsarStep** (Li, Yu, Wu, Paulson; ICLR 2021) [P, https://ar5iv.labs.arxiv.org/html/2006.09265].
  820K training examples mined from 204K AFP and library lemmas; the task is to fill one missing
  intermediate proposition of an Isar proof. Best model: top-1 exact match 22.8 %, or 24.3 % when
  the lemmas used are given; top-10 35.2/37.2; well-formed 58.2 to 58.9 %; correct (exact, or shown
  equivalent by ATPs) 27.6/29.4 % (Tables 1, 2, 4). "incorrect propositions are well-formed and
  plausible propositions". It is the only large measurement of generated `have` statements against
  human ones; it predates LLM provers and I found no re-run.
- DSP's draft audit (§1.1) and ProofFlow's failure table (§1.2). FormalMATH's pipeline: a
  negation-proving filter removed about 1.6 % of autoformalised statements and an LLM semantic check
  60.7 % of the syntactically valid ones [P].
- Cost per subgoal is reported nowhere. Per problem: Cobblestone $1.25; ProofFlow 94.2K output
  tokens; LEGO-Prover about $300 per 100-attempt run. Project-scale unit costs are in [E §3].

### 1.5 Evaluations of the mechanisms described in survey J

Added after both surveys were drafted: J leaves the numbers of 25 works to K, and K had none. Each
record gives what the evaluation shows about the lemma-proposal or splitting step (an arm without it
where one exists) and ends with what is not shown. All are [P], searched as downloaded text ("pdf":
a converted PDF); URLs are in the source index, methods in J at the bracketed sections. §1.4 found
no error rates for decomposition: that holds for the LLM provers, and lfind, Lemmanaid, kSubS and
AutoVerus report rejection rates.

**Proof planning and rippling [J §1].**
- **IsaPlanner case analysis** (ITP 2010) [P, pdf]. 87 theorems with `if` or `case` functions, "none
  of which IsaPlanner could prove previously": 47 proved with the technique, 37 by a
  simplifier-based prover (§4, text). The authors built the corpus to need case analysis.

**Lemma discovery and theory exploration [J §2].**
- **QuickSpec** (JFP 2017) [P, pdf]. No test of whether the laws help a prover; §4.5 measures cost
  (1,800 s to 30 s against version 1, Table 2) on case studies of 13 to 398 tested laws.
- **HipSpec** (CADE 2013) [P, pdf]. 85 IsaPlanner conjectures, 67 of which need no lemma: HipSpec
  80, Zeno 82, ACL2s 74, IsaPlanner 47, Dafny 45. 50 CLAM theorems that mostly need one: HipSpec 44
  (47 with settings changed), CLAM 41, Zeno 21 (§4.1). Against Isabelle's library, precision 80 %
  and recall 73 % on naturals, 90 % and 100 % on lists (Table 1). No arm without the conjectures.
- **Hipster** (CICM 2014) [P]. Worked examples only; no benchmark.
- **IsaCoSy** (JAR 2011, draft) [P, pdf]. Against Isabelle's library (§10.2): naturals, recall 83 %
  (10 of 12) and precision 63 %; lists, 100 % (9 of 9) and 38 %. Of 46 conjectures that passed the
  counterexample checker unproved in one theory, 20 were proved by hand and "no non-theorems were
  found" (§10.3). 1 h 22 min to 18 h 43 min per theory (Table 2). No lemma is used in a later proof.
- **TheSy** (CAV 2021) [P, pdf]. 311 CVC4 induction benchmarks, 5 minutes (Table 1): TheSy 187, CVC4
  with conjecture generation 260 and without 70, Z3 75. Against Hipster on 85 theories, by mutual
  subsumption of lemma sets, ahead in 65 and level in 6 (Fig. 5), a measure with no ground truth.
- **CCLemma** (ICFP 2024) [P, pdf]. 60 s per property (Table 1); CCLemma, HipSpec, CVC4, TheSy: 87
  IsaPlanner properties 75, 77, 67, 44; 50 CLAM properties needing lemmas 38, 38, 22, 34; 96
  optimisation equations 28, 11, 18, 6. No arm without lemmas.
- **lfind** (OOPSLA 2022; thesis ch. 2 read) [P, pdf]. 222 points in human Coq proofs where a human
  helper lemma is applied; Proverbot9001 fixed. It closes 22.1 % of the points with no lemma and
  49.1 % with lfind's; counting a top-ten match of the human lemma, 64.9 % (Table 2.1, §2.5.4).
  Generalisation alone: 19.4 %. Median candidates per point 168, then 112 after the invalidity
  filter and 17 after the redundancy filter (Fig. 2.7). Points needing no lemma are not sampled.
- **CVC4 induction** (Reynolds and Kuncak 2015) [P, pdf]. 311 benchmarks in each of three encodings,
  300 s (Fig. 2): induction alone and with subgoal generation 207 and 237, 186 and 192, 243 and 260;
  on the 66 said to need subgoals, 10 and 30 in the first encoding (my arithmetic). Without the
  candidate filters 2 of the 17 gains in the third encoding remain. No candidate counts.
- **Lemmanaid** (arXiv 2504.04942v6) [P]. Task: recover a human lemma from its symbols; HOL-test
  4,740 lemmas, AFP-test 18,975; a 6.7B model. Templates 50.2 and 28.6 % at best, direct generation
  38.5 and 25.2 %, ensembles 55.1 and 34.8 against 44.1 and 31.6 % (Table 1); 41.7 against 38.1 % on
  139 lemmas of 2026 (Table 2). Of 7,628 conjectures for HOL-test 22.6 % are the human lemma, 17.8 %
  otherwise true, 23.6 % false, 36.0 % unresolved (Table 3). No proof uses the output.

**Cut introduction [J §3].**
- **Cut introduction** (Hetzl et al., arXiv 1401.4330) [P]. Five hand-built proofs: one introduced
  cut leaves 0.45 to 0.69 of the inferences (Table 1), which is not "a systematic empirical
  investigation". J's exponential compression is a theorem about one proof sequence (§7).

**Learned subgoal generation [J §4].**
- **kSubS** (NeurIPS 2021) [P]. INT inequalities, proof length 15, budgets of 50 to 400 graph nodes
  (Table 2): best-first search 0.09, 0.24, 0.35, 0.47; with the subgoal generator 0.38, 0.91, 0.91,
  0.91; 69 h 15 min against 9 h 22 min for 1,000 proofs (Table 5). On small Sokoban boards 17 % of
  subgoals increase the distance to the solution (Fig. 3). Generated problems.
- **AdaSubS** (ICLR 2023) [P]. Same task, ±3 points (Table 1). At 1,000 nodes: best-first 36.7 %,
  kSubS 89.6 %, mixed subgoal distances 95.7 %. A learned verifier of reachability changes these by
  at most 1.1 points; at 50 nodes it lifts the mixed scheme from 51.5 to 59.0 %.
- **HyperTree Proof Search** (2022) [P]. No lemma-proposal step and no arm without goal splitting;
  its tables compare training regimes (miniF2F-test, pass@64: 35.3 % supervised, 41.0 % after online
  training; Table 2).
- **ProD-RL** (arXiv 2411.01829) [P]. AFP test (4.3k theorems) and AFP 2023 (2k, later than the
  model's cutoff); 7B model. Pass@16 (Table 2): fine-tuned without lemma proposal 43.4 and 39.4; RL
  without it 42.4 and 37.7; fine-tuned with it 40.8 and 36.5; ProD-RL 45.5 and 39.5. Fine-tuned
  only, lemma proposal lowers the pass rate; over the no-lemma fine-tuned arm ProD-RL gains 2.1 and
  0.1 points, against the headline's 4.7 and 3.0 over its own (my arithmetic). No lemma error rate.
- **BFS-Prover-V2's planner** (arXiv 2509.06493) [P]. Budget "accumulative" (Table 1): the 32B step
  prover alone 86.1 % on miniF2F-test, 85.5 % on validation; with a general LLM planning `have`
  subgoals 95.1 and 95.5 %. No budget per row; no count of unprovable or replanned subgoals.
- **DSP+** (arXiv 2506.11487) [P; Figs. 3, 5, 10 read as rendered images]. miniF2F-test, 244
  problems, pass@128. Full pipeline 74.2 %; no draft 71.7 %; no step prover 22.5 %; step prover with
  Aesop and no sketch 49.6 %, at a "limited budget" (Fig. 3). Without error-line masking 71.3 %;
  without stated subgoal hypotheses 71.3 % (Fig. 5). Given the human informal proof, 70.9 against
  74.2 % (Fig. 10). Eight wrongly formalised statements found. No rate of false sketched subgoals.

**Program verification [J §5].**
- **Boogie VC splitting** (2008) [P, pdf]. Time against number of splits for single functions, no
  aggregate (Figs. 2 to 5). A 600-line function "would not finish in one day" with three splits or
  fewer and takes about 20 s with ten or more; for another, splitting "is useless".
- **Lemur** (arXiv 2310.04870v5) [P]. ESBMC alone is the arm without proposals. Code2Inv, 133
  programs, 10 minutes (Table 1a): ESBMC 68, Lemur with GPT-4 107 at 4.7 proposals per solved
  program. 47 SV-COMP programs chosen because two verifiers fail on them (Tables 1b, 3): they solve
  1 each, Lemur 24 to 25, or 19 to 20 without its repair rule. No rate of rejected proposals.
- **Loopy** (arXiv 2311.07948) [P]. 469 single-loop C programs with a sufficient invariant; GPT-4;
  Frama-C (§4, Fig. 1). With 15 completions, 293 verify with one completion taken whole and 383 with
  Houdini pruning over their union; 8 completions and 7 repair rounds give 398; the symbolic tool
  Ultimate solves 430. Pruning is worth 90 programs at equal LLM calls.
- **Laurel** (OOPSLA 2025) [P]. DafnyGym, assertions removed from lemmas of three code bases: 143
  tasks in §5 and §6.1, 145 in the introduction; GPT-4o, 10 attempts (§6.2 to §6.4). Code only
  6.2 %; placeholder at the computed location 34.4 %; with six examples chosen by proof similarity
  as well 56.6 % (82/145); examples without placeholder 46.8 %. Same-codebase examples.
- **AutoVerus** (OOPSLA 2025) [P]. Verus-Bench, 150 tasks, GPT-4o: 137 proved, 37 of them only after
  repair by error class; plain repeated prompting proves 67 at 59 LLM calls per task, a count
  AutoVerus reaches at 2 (Table 2, Fig. 8). On the 37, a generic agent given the whole error report
  proves 17 at the same budget (§7.4.2): the nearest test I found of gap 9 in §5, on repair and on
  tasks the rule table had solved. 326 of 2,637 candidates (12.4 %) were filtered as unsafe.

**SAT/SMT divide and conquer [J §6].**
- **Cube-and-conquer** (HVC 2011) [P, pdf]. One van der Waerden instance: about 20 h whole, 4 h as
  32,331 cubes (§4). Of 15 SAT 2009 instances unsolved in competition, a time is listed for 10,
  against 7 and 6 for two portfolio solvers and 13 for a grid solver (Table 1, my count).
- **Partitioning for SMT** (FMCAD 2023) [P]. 214 hard benchmarks, 20 minutes, PAR-2 curves. Atoms
  from the solver's priority queue "consistently perform worse than the random strategy" (Fig. 2).
  Unpartitioned scrambled copies beat the recommended partitioning portfolio below 32 cores and lose
  above (Fig. 5).

**Rule catalogues [J §7].**
- **Ganesalingam and Gowers** (arXiv 1309.4501) [P]. No measure of proving power; §3 tests five
  write-ups against human ones: asked to pick the program's, "roughly half the voters" did.

**Table A. Experiments of block A.** "pts" are percentage points.

| Work | Prover; data | Held fixed | Varied | Result | Main limit |
|---|---|---|---|---|---|
| Cobblestone | Coq; 2 x 100 theorems | GPT-4, harness | oracle: none, lemmas, decomposition | 38/43/52 % and 48/50/47 % | n = 100; sign differs by set |
| DSP | Isabelle; miniF2F | Codex, 100 sketches | author of informal proof | human 39.3, Minerva-540B 38.9 (test) | one human draft against 100 machine drafts |
| LEGO-Prover | Isabelle; miniF2F | ChatGPT, attempts | informal proof author; lemma library | 50.0 vs 45.5; 50.4 vs 47.1 | one run per arm |
| RLMEval | Lean; 613 blueprint theorems | 7B provers, pass@128 | project lemmas visible; informal proof | 8.76 to 14.70; +1.5 pts | no agent, no frontier model |
| miniCTX | Lean; 762 theorems | GPT-4o | file context | 11.72 to 27.08 % | context is more than decomposition |
| IMO-Steps | Lean; 1,329 hand-cut lemmas | 32 samples | prover | 39.3 % of lemmas at best | no undecomposed arm |
| Subgoal demonstrations | Isabelle; miniF2F | ChatGPT, 100 calls | demonstration format | 45.5 vs 40.6 (test) | few-shot effect, not a harness stage |
| ProofFlow | Lean; 184 NL proofs | models | step DAG enforced or not | 0.545 vs 0.417 ProofScore | metric includes an LLM judge |
| Lemma mining 2014 | HOL Light; 1,954 and 1,796 theorems | ATPs, 30 s | mined lemmas as premises | +3.1 pts; +7.8 pts in union | one setting ranks lemmas on the full graph |
| REFACTOR | Metamath; 2,720 test theorems | prover | corpus refactored with new lemmas | 557 to 632 | extraction accuracy 19.6 % |
| SorryDB | Lean; 1,000 sorries | Gemini Flash 3 | one shot, self-correct, agent | 10.8/27.9/30.3 % | budgets differ by arm |
| MathlibLemma | Lean; 9,148 proposals | pipeline | (funnel) | 47 % compile, 16 % proved (my arithmetic) | stand-alone lemmas |
| IsarStep | Isabelle; 5,000 test steps | data | model; used lemmas given | 27.6 to 29.4 % correct | 2021 seq2seq models |

**Table A2. Evaluations of §1.5.** Columns as in Table A; "—" means none.

| Work | Prover; data | Held fixed | Varied | Result | Main limit |
|---|---|---|---|---|---|
| IsaPlanner case analysis | IsaPlanner; 87 theorems | prover, definitions only | case-analysis technique | 0 to 47; simplifier arm 37 | corpus built to need the technique |
| QuickSpec | Haskell; case studies | — | version 1 against 2 | 1,800 s to 30 s; 13 to 398 laws | no proving task |
| HipSpec | Haskell, Z3; 85 and 50 conjectures | 1 s per obligation | prover | 80 of 85; 44 of 50 against CLAM 41 | no arm without conjectures |
| Hipster | Isabelle; worked examples | — | — | none | no benchmark |
| IsaCoSy | Isabelle; two library theories | — | (recall, precision) | recall 83 and 100 %; precision 63 and 38 % | reference is one library |
| TheSy | own prover; 311 goals; 85 theories | 5 min | tool | 187 of 311 against CVC4 260 | subsumption measure is relative |
| CCLemma | own prover; 87, 50, 96 properties | 60 s | tool | 75, 38, 28 against HipSpec 77, 38, 11 | no ablation |
| lfind | Coq; 222 lemma points | Proverbot9001 | lemma supplied or not | 22.1 to 49.1 % | points where a human used a lemma |
| CVC4 induction | CVC4; 311 in 3 encodings | solver, 300 s | subgoal generation | 207 to 237; 186 to 192; 243 to 260 | candidate counts not given |
| Lemmanaid | Isabelle; 4,740 and 18,975 lemmas | 6.7B model, 5 predictions | template or direct generation | 50.2 vs 38.5 %; 28.6 vs 25.2 % | target's symbols are given |
| Cut introduction | GAPT; 5 proofs | — | (compression) | 0.45 to 0.69 of the inferences | not a systematic study |
| kSubS | INT, length 15 | node budget | subgoal generator | 0.47 to 0.91 at 400 nodes | generated problems |
| AdaSubS | INT, length 15; 1,000 problems | node budget | subgoal distances; verifier | 95.7 vs 89.6 %; verifier 51.5 to 59.0 % at 50 nodes | generated problems |
| HTPS | Lean, Metamath | search | training regime | 35.3 to 41.0 % (miniF2F-test) | no decomposition arm |
| ProD-RL | Isabelle; AFP, 4.3k and 2k theorems | 7B model, pass@16 | lemma proposal; SFT or RL | 43.4, 40.8, 45.5; 39.4, 36.5, 39.5 | lemma error rates not given |
| BFS-Prover-V2 | Lean; miniF2F | 32B step prover | planner | 86.1 to 95.1 % (test) | budgets not matched |
| DSP+ | Lean; miniF2F-test, 244 | models, pass@128 | pipeline components | full 74.2; prover only 49.6; no prover 22.5 | prover-only arm at a small budget |
| Boogie VC splitting | Boogie; single functions | function | number of splits | over a day to about 20 s (one function) | no aggregate; some functions gain nothing |
| Lemur | ESBMC; 133 and 47 programs | verifier, time limit | LLM proposals | 68 to 107; 1 to 25 | second set chosen on baseline failure |
| Loopy | Frama-C; 469 loops | GPT-4, 15 calls | Houdini pruning; repair | 293, 383, 398; Ultimate 430 | below the symbolic baseline |
| Laurel | Dafny; 143 or 145 assertions | GPT-4o, 10 attempts | placeholder; examples | 6.2, 34.4, 56.6 % | examples from the same code base |
| AutoVerus | Verus; 150 tasks | GPT-4o | workflow; rule table or generic agent | 137 vs 67; 37 vs 17 | the 37 were selected by the rule table |
| Cube-and-conquer | SAT; vdW; 15 hard instances | solver | split or whole | 20 h to 4 h; times for 10 of 15 | instances chosen as hard |
| SMT partitioning | cvc5; 214 benchmarks | 20 min, core count | partitioning; scrambling | partitioning wins from 32 cores up | curves only |
| Ganesalingam-Gowers | own prover; 5 problems | — | author of write-up | about half pick the program | proving power not measured |

## 2. Proof structure in human-written corpora (block B)

### 2.1 Size relations, beyond [D §1.5]

- **Specification size against code size** (Staples, Kolanski, Klein, Lewis, Andronick, Murray,
  Jeffery, Bass; ICSE 2013)
  [P, pdf, https://trustworthy.systems/publications/nicta_full_text/6416.pdf]. Unit: the 31 seL4 API
  functions; size is the normalised line count of the slice reachable from each function in the
  abstract specification, the executable specification and the C code. Result (Figs. 1, 2): the
  three pairwise correlations of slice size are 0.89, 0.95 and 0.92; COSMIC function points
  correlate with the three at 0.31, 0.15 and 0.19, none significant at 0.05. Not shown: one system;
  shared sub-functions are counted in every slice that reaches them.
- **The seL4 statement-size relation replicated on the AFP** (Blanchette, Haslbeck, Matichuk,
  Nipkow; CICM 2015, §4.2) [P, pdf, https://www21.in.tum.de/~nipkow/pubs/cicm15.pdf]. Same measures
  as Matichuk et al. [D §1.5]. Quadratic fits, raw and idealised R² (Table 1): JinjaThreads 0.346
  and 0.712; Group-Ring-Module 0.487 and 0.622; Psi_Calculi 0.349 and 0.431. Over the whole AFP with
  the idealised measure, "approximately half of the articles have an R2 of less than 0.5 (or have
  too few data points to build a model)", 50 lie between 0.5 and 0.7 and 50 above 0.7; the best fits
  are software-verification articles, and the quadratic coefficients run "from 0.07 to 21.29". Their
  conclusion: "proof size cannot be estimated based solely on this coarse measure of lemma statement
  size".
- **Statement size against number of dependencies in Mizar** (Aspinall and Kaliszyk, FASE 2016,
  §5.5) [P, pdf, https://ckaliszyk.github.io/d/16/dack-fase16.pdf]. On MPTP2078 the number of proof
  dependencies is plotted against three measures of statement size: "there are no clear
  relationships, and plenty of outliers". The authors add that "Effort prediction in general cannot
  be feasible" for mathematics.
- **Remaining proof length from the proof state** (LeanProgress; George, Huang, Song, Anandkumar
  2025) [P, https://arxiv.org/html/2502.17925]. On about 80k Lean proof trajectories a language
  model predicts the number of steps left with 62.5 % accuracy from the state alone and 75.8 % with
  the proof history (Table 1); as a search signal it lifts ReProver from 41.4 to 45.2 % (Table 2).
  Its input is a proof state, not a statement.
- Success falls with human proof length wherever it is reported: miniCTX (§1.1); RLMEval, where
  successful model proofs average 2.5 to 6.0 lines and the human proofs 16.6 (Table 3) [P]; VeruSAGE
  and the seL4 OSDI study [D §1.9, §3].

### 2.2 Lemma size, proof depth, statement shape

- **AFP, snapshot of 16 April 2015** (Blanchette et al. 2015) [P, pdf]: 215 articles, 64,497 lemmas,
  1,018,800 lines; proofs 58 % of the text, lemma statements 19 %, definitions 8 %; 3.6 lemmas per
  definition. Proof depth, the nesting of Isar blocks (Fig. 5, labels as extracted): 48,755 lemmas
  at depth 1 (an unstructured script), 10,399 at depth 2, 3,187 at 3, 1,244 at 4, 533 at 5, one at
  15; "Almost 99% of all proofs have a depth of 4 or less". Statement shape after Isabelle's
  clausifier (§5): 49,901 lemmas give one clause; 11,444 are unit equations, 22,475 conditional
  equations, 46,186 Horn clauses; 20,235 statements have one literal and 30,502 two to four. "One
  third of all lemma statements are equations, two thirds are Horn clauses."
- **Proof style in the AFP** (Megdiche, Huch, Stevens 2022)
  [P, https://ar5iv.labs.arxiv.org/html/2207.10424]. A linter over outer-syntax tokens (it "does not
  process inner syntax such as terms") finds 59,573 lints in AFP 2021-1 (Table 1): `tactic_proofs`
  23,215; `complex_method` 13,526; `unrestricted_auto` 8,886; `complex_isar_initial_method` 4,747;
  `low_level_apply_chain` 2,801; `apply_isar_switch` 1,166.
- **Coq and Lean.** CoqGym (Yang and Deng, ICML 2019)
  [P, https://ar5iv.labs.arxiv.org/html/1905.09381]: 70,856 proofs from 123 projects; "each proof
  has 8.7 intermediate goals and 9.1 steps"; 5.6 premises in the local context; 53 % of tactics take
  an argument. LeanDojo (Yang et al., NeurIPS 2023)
  [P, https://ar5iv.labs.arxiv.org/html/2306.15626]: 98,734 theorems and 217,776 tactics, 2.2 per
  theorem (my arithmetic); 129,243 tactics cite a premise, 2.13 on average.
- **Blueprint projects** (RLMEval Table 2) [P]: blueprint theorems average 16.6 proof lines and
  auxiliary lemmas 6.6; the auxiliary share of all theorems is 68.3 % on average and runs from
  15.9 % (FLT3) to 85.9 % (Carleson). A blueprint node therefore stands on about two unlisted helper
  lemmas (my arithmetic from the mean share). IMO-Steps (§1.1): about one hand-cut lemma per 3.5
  proof lines.
- **How often structural methods occur** (PaMpeR's corpus, §4) [P]: of 425,334 method invocations in
  the Isabelle library and AFP, `simp` is 26.8 %, `auto` 22.2 %, `rule` 10.2 %, `cases` 1.5 %,
  `induct` 1.3 %, `case_tac` 0.9 %, `induction` 0.5 %.

### 2.3 Dependency graphs: depth, fan-out, reuse

- **Mathlib** (Li, Peng, Severini, Shafto 2026) [P, https://arxiv.org/html/2604.24797v2]. Commit of
  2 February 2026; 308,129 declarations, 8,436,366 edges, 7,563 modules (§5 of the paper says
  317,655 nodes). Extracted with importGraph, jixia and lean-training-data. "43.9% of dependencies
  arise exclusively from proofs versus only 8.1% from statements"; 48.0 % arise from both. DAG depth
  153 for modules and 84 for declarations; definitional height median 7; "The median import
  utilization is only 1.6%"; in-degree is heavy-tailed and the most-cited nodes are language
  infrastructure (`Eq.refl`, 69,580 citations). Data:
  https://huggingface.co/datasets/MathNetwork/MathlibGraph .
- **An AI-built development** (FormaTheoria; Nie et al., arXiv 2608.10894, August 2026)
  [P, https://arxiv.org/html/2608.10894, characters 0 to 200,000]. Odd Order, Glauberman Z*,
  Brauer-Suzuki and Bender-Suzuki in Lean: "30,298 declarations reachable from Bender–Suzuki" in
  more than 994,000 lines. Project-only graph: 186,187 edges (6.1 per node, my arithmetic); "8,916
  (29.4%) have depth zero, and the median depth is only two"; percentiles 90, 95 and 99 are 38, 169
  and 378; the root has depth 458; the most-used declaration has 6,016 dependants and the largest
  fan-out is 536 (§5.1.3). The authors grant that fast construction "does not by itself produce a
  concise and reusable library". Not in [E].
- **AFP imports graph** (Blanchette et al. 2015, §3) [P, pdf]: 215 nodes, 97 edges, 106 isolated
  articles, depth 6; "the top 3 articles are reused 9, 6, and 4 times".
- **Module-level metrics** (Aspinall and Kaliszyk 2016, Fig. 4) [P, pdf]. Six module metrics recast
  from object-oriented design, among them DIT (depth in the import DAG), TDM (theorems depended on)
  and LCOM (one minus the mean pairwise Jaccard index of the statements' symbol sets). Means:
  Flyspeck DIT 27.6, TDM 1,582, LCOM 62.0 %; Isabelle Main 17.6, 357, 72.2 %. Nothing validates them
  against effort or defects.
- **Fine-grained dependencies in Coq and Mizar** (Alama, Mamane, Urban 2011)
  [P, https://ar5iv.labs.arxiv.org/html/1109.3687]: item-level dependencies cut re-checking after a
  change "about seven times for CoRN, and about five times for Mizar"; learned premise pruning lifts
  Vampire from 567 to 717 of 2,078 problems.

### 2.4 The de Bruijn factor

Wiedijk (2000) [P, pdf, https://www.cs.ru.nl/~freek/factor/factor.pdf] takes the ratio of formal to
informal file size, raw (apparent) and after gzip (intrinsic): Landau's Grundlagen in Automath 3.9
and 3.7; a finite-topology paper in Mizar 4.6 and 3.1; four pages of the Compendium of Continuous
Lattices in Mizar 6.7 and 4.1. Three texts, no variance; I found no figure for Lean blueprints or
LLM-written developments.

### 2.5 User studies

- **REPLica** (Ringer, Sanchez-Stern, Grossman, Lerner; CPP 2020)
  [P, pdf, https://dependenttyp.es/pdf/analytics.pdf]. A month of instrumented Coq use by 8
  intermediate-to-expert users, 362 interactive sessions. "Of the 279 interactive proof subsessions,
  209 (over 75%) began a proof, only to step above the entire proof attempt and return to make
  changes to earlier definitions or commands". In the 70 successful ones (1,085 tactic invocations)
  seven tactics make up over half the invocations; of 96 cancelled tactics, 31 were re-run with
  changed arguments. One user's changes "most often corresponded to generalizing the inductive
  hypothesis after a partial proof attempt" (Benchmark 10).
- **QED in Context** (Shi, Torczon, Goldstein, Pierce, Head; OOPSLA 2025)
  [P, pdf, https://jwshii.github.io/OOPSLA25.pdf]. Contextual inquiry, 30 Rocq and Lean users, one
  hour each on their own work. Counts of participants: 15 realised in mid-proof "that a new lemma
  would be useful"; 14 revised the specification in mid-proof; 12 used `admit` or `sorry` to defer a
  goal; 16 reused proofs by copy and paste; 5 worked from a paper proof. "Participants almost always
  did lemma extraction manually, with one notable exception".
- **What's in a Proof?** (Jain et al. 2025) [P, https://arxiv.org/html/2508.02733v1]: 8 experts in
  F* and Verus on four small tasks; F* sessions that put 74 % of early time into the specification
  all succeeded, rapid verifiers in 67 %; clusters of one to five sessions.

**Table B. Corpus studies.**

| Study | Corpus | Unit | Measure | Result | Does not show |
|---|---|---|---|---|---|
| Staples 2013 | seL4, 31 API functions | API slice | lines of spec and code | R 0.89 to 0.95 | proof size; a second system |
| Blanchette 2015 §4 | AFP 2015 | lemma | statement size vs proof size | half of articles R² < 0.5 | a predictive model |
| Blanchette 2015 §2, §5 | 64,497 lemmas | lemma | Isar depth; clauses, literals | 76 % depth 1 (my arithmetic); 2/3 Horn | the move used in each proof |
| RLMEval Table 2 | six blueprints | theorem | proof lines; helper share | 16.6 vs 6.6; 68.3 % | graph depth, fan-out |
| Li et al. 2026 | Mathlib, 308,129 declarations | declaration | depth, edge kind | depth 84; 43.9 % proof-only edges | proof-internal structure |
| FormaTheoria 2026 | 30,298 AI-written declarations | declaration | depth, degree | median 2, root 458 | comparison at equal content |
| Aspinall and Kaliszyk 2016 | Flyspeck, Isabelle, Mizar | module | six metrics | mean module depth 3.9 to 27.6 | validity of the metrics |
| Wiedijk 2000 | three texts | text | formal/informal size | 3.1 to 4.1 after gzip | variance; modern provers |
| REPLica 2020 | 8 Coq users, one month | subsession | outcome, edits | 209 of 279 step back | large projects, teams |
| Shi et al. 2025 | 30 Rocq and Lean users | participant | behaviours seen | 15 extract a lemma mid-proof | frequency per proof |

## 3. Features and graph representations (block C)

Table C gives, for each work, the unit, the schema, what the computation needs, the tool and the
measured effect. Three points the table cannot carry. First, **MaSh's scheme is the most complete
recipe for statement features in Isabelle** (Blanchette, Greenaway, Kaliszyk, Kühlwein, Urban 2016)
[P, pdf]: "For each term in the formula (excluding the outer quantifiers, connectives, and
equality), the nontrivial first-order patterns up to a given depth are generated as features";
"Variables are replaced by their types, since variable names have no fixed meaning"; type
constructors, type classes with their superclasses, the theory name and a local-fact flag are added;
the features of chained facts enter at half weight and those of up to ten preceding facts at weight
0.1; weights are inverse document frequency; "Proofs involving over 20 facts are considered
unsuitable and simply ignored". Second, **two papers treat variable names in opposite ways.**
FormulaNet renames every variable and still gains ("By construction, our graph is invariant to
variable renaming"); Paliwal et al. hide the names and lose 12.6 points ("human-chosen variable
names are important"). I think the difference is that FormulaNet keeps the binding edges, while
hiding names also erases which free variable is which. Third, **conditioning on the conjecture did
not help the HolStep baselines** ("None of our conditioned models appear to be able to improve upon
the unconditioned models"); FormulaNet's authors note that only 0.8 % of statements occur with both
labels, so usefulness can be read off the statement alone. A label that is nearly a function of the
item is a hazard for any benchmark built from the library's positive examples.

**Table C. Feature and graph schemas.** "Needs" says what the published implementation requires;
"parser" means a term parser without a prover.

| Work | Unit | Schema | Needs | Tool, URL | Task and number |
|---|---|---|---|---|---|
| MePo (Meng and Paulson 2009) [P, pdf, https://www.cl.cam.ac.uk/~lp15/papers/Automation/filtering-jal.pdf] | fact against goal | constant symbols per clause; score m/n, relevant over all symbols; rare symbols weighted 1 + 2/log(n+1); pass mark p rises by (1 - p)/c each round, p = 0.6, c = 2.4 | Isabelle constants | Sledgehammer | 285 problems: Vampire's success "peaks sharply at 0.6", mean problem 909 to 142 clauses |
| MaSh (2016) [P, pdf, https://www21.in.tum.de/~blanchet/mash2.pdf] | fact and goal | see text; labels are proof-term dependencies | Isabelle terms, types, proof terms | Sledgehammer; `mash_export` | mean rank of a needed fact 735 to 132 (IsaFoR); goals solved 48.5 % with MePo alone, 66.1 % with MaSh and MeSh added |
| Kaliszyk, Urban, Vyskočil (IJCAI 2015) [P, pdf, https://www.ijcai.org/Proceedings/15/Papers/435.pdf] | formula | SYM symbols; TRM0 subterms with variables unified; TRMα subterms de Bruijn-normalised; MAT matching terms with generalisations; PAT walks in the term graph; ABS substitution-tree nodes; UNI unifying terms | parser | not linked in the paper [U] | MPTP2078, k-NN then E: SYM 998 theorems, TRM0 1,050, best matching feature 1,130, union of four 1,153 (Table 5); extraction 0.25 s for SYM, 25 s for UNI |
| ENIGMA (Jakubův and Urban 2017) [P, https://ar5iv.labs.arxiv.org/html/1701.06532] | clause | counts of symbol triples along walks of length 3; variables and Skolem symbols each mapped to one token; sign of the literal at the root | parser | E prover | AIM, 200 problems, 180 s: 22 solved by the base strategy, 41 with the classifier, 57 after boosting |
| TacticToe (Gauthier et al., JAR 2021) [P, https://ar5iv.labs.arxiv.org/html/1804.00596] | goal | constant names including logical operators; type constructors; "subterms with all variables replaced by a single placeholder V"; variable names; hypotheses and conclusion tagged apart; TF-IDF to the sixth power, k-NN | HOL4 terms | HOL4 | 7,164 theorems, 60 s: 66.4 % against E 34.5 %; predicting theorem-list arguments 156 to 199 on 273 tuning theorems |
| Tactician features (Zhang et al., CICM 2021) [P, https://ar5iv.labs.arxiv.org/html/2104.05207] | proof state | AST walks up to length 3; root-to-atom walks with inner nodes abstracted; top-level shape with arities; counts; hypotheses and goal apart | Coq terms | Tactician | Coq library, 40 s: k-NN 33.7 to 34.7 %, random forest 35.3 to 36.2 % of lemmas with the new features |
| Passport (Sanchez-Stern et al., TOPLAS 2023) [P, https://ar5iv.labs.arxiv.org/html/2204.10370] | identifier in a proof state | category (global definition, local variable, type constructor); index if common; BPE subwords; qualified path | Coq via SerAPI | on TacTok, ASTactic | 10,782 theorems: globals alone 16 % more proofs, constructors 8 %, locals 0.5 %, all three 33 %; 20 retrainings span 11.6 to 12.0 % |
| ILP rules (Zhang, Cerna, Kaliszyk 2024) [P, https://arxiv.org/html/2411.01188v1] | proof state | one fact per AST node of goal and hypotheses; relations above, left, equal-term; identifiers optionally replaced by their kind | Coq terms | Popper | 151,678 states: "the combination of ILP and k-NN increases the accuracies of k-NN" in every test theory; numbers only in a figure; F1 0.164 to 0.564 |
| ML4PG (Komendantskaya, Heras, Grov 2012) [P, https://ar5iv.labs.arxiv.org/html/1212.3618] | lemma proof | first five steps by six columns: tactic names, number of tactics, argument type, argument is a hypothesis, top symbol of the goal, number of subgoals; 30 features | Coq through Proof General | ML4PG | clusters only; no precision or recall |
| ACL2(ml) (Heras et al., LPAR 2013) [P, https://ar5iv.labs.arxiv.org/html/1308.1780] | lemma statement | 7 by 7 matrix of the term tree: row by arity (row 0 for variables), column by depth, cell a code for the symbol class; 49 features | parser and definitions | ACL2(ml) | "37%" of clusters usable for lemma analogy; no count of lemmas that finished a proof |
| FormulaNet (Wang et al., NIPS 2017) [P, https://ar5iv.labs.arxiv.org/html/1709.09994] | formula | node per function, constant, quantifier and variable occurrence; edges function to argument and quantifier to bound occurrence; equal leaves merged; variables renamed | parser | none named | HolStep usefulness: 83 % (token CNN) to 90.3 %; 81.5 % from node names alone |
| Paliwal et al. (AAAI 2020) [P, https://ar5iv.labs.arxiv.org/html/1905.10006] | goal, theorem | S-expression tree with equal subexpressions merged, edges both ways, 12 rounds | prover export | HOList | 3,225 theorems: 32.65 to 49.95 % closed; plain tree 45.67; names hidden 37.36; bag of tokens 37.98 |
| Graph2Tac (Blaauwbroek et al., ICML 2024) [P, https://arxiv.org/html/2401.02949] | proof state and definitions | one graph for the library; definition nodes shared; equal subterms merged by hash | Coq via Tactician | 120 packages, 520k definitions | 2,000 theorems, 10 min: 26.1 %, or 17.5 % without learned definition embeddings; k-NN on hand-made features 25.8 %; both 33.2 % |
| MLFMF (Bauer, Petković, Todorovski; NeurIPS 2023) [P, https://arxiv.org/html/2310.16005] | library entry | nodes library, module, entry; edges CONTAINS, DEFINES, REFERENCE from declaration or from body; each entry also an s-expression | Agda or Lean at compile time | https://github.com/ul-fmf/mlfmf-data | link prediction accuracy: node2vec 0.95 to 0.98, TF-IDF 0.51 to 0.52, bag of words 0.50 (Table 3) |
| LeanDojo [P] | tactic, theorem | file DAG; ASTs; state before and after each tactic; premises with definition and use sites | modified Lean build | LeanDojo | ReProver 47.6 to 51.2 % with retrieval; 23.2 to 26.3 % on unseen premises |
| jixia [P, https://github.com/frenzymath/jixia] | declaration, line, tactic | JSON per file: declarations, symbols with types and a reference graph, elaboration with tactic info, proof state per line, AST | built Lean project; "No change need to be made on the target file" | Apache-2.0 | none; used for the Mathlib network (§2.3) |
| TheoremGraph (Kurgan et al. 2026) [P, https://arxiv.org/html/2606.25363] | declaration | six edge kinds: extends, field, sig, proof, def, docref; 388,105 declarations, 11,335,708 edges, 25 projects | Lean kernel environment | huggingface.co/datasets/uw-math-ai/theorem-matching | retrieval Recall@10 0.775 against 0.780 for LeanSearch v2 |
| coq-dpdgraph [P, https://github.com/coq-community/coq-dpdgraph] | object | nodes with kind, prop, body, opaque, path; "edge n1 --> n2 : n1 uses n2" | Rocq plugin | LGPL-2.1 | none; `dpdusage` lists unused definitions |
| Isabelle `thm_deps`, `unused_thms` [P, https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/master/src/Doc/Isar_Ref/Outer_Syntax.thy] | fact | "immediate theorem dependencies ... without going deeper into the dependency graph"; theorems of a theory range "that are never used" | Isabelle session | distribution | none |
| Proof-step graphs: ProofFlow (§1.2); TacMiner (§1.2); CoqGym; Paperproof [P, https://github.com/Paper-Proof/paperproof] | step | ProofFlow: condition, definition, lemma and solution nodes, edge from prerequisite; TacMiner: "nodes represent tactic applications, while edges represent proof state dependencies"; CoqGym: goal nodes, tactic edges; Paperproof: hypothesis, goal and tactic nodes in nested scopes | LLM on NL text; Coq-SerAPI; Coq; Lean in VS Code | MIT (Paperproof) | ProofFlow and TacMiner as in §1.2; Paperproof none, and no offline export in the README [U] |
| Rango (Thompson et al., ICSE 2025) [P, https://arxiv.org/html/2412.14063] | stored proof | BM25 between the current proof state and each state of a stored proof, maximum taken; same project only | Coq states; text similarity | CoqStoq, 196,929 theorems | 500 theorems: no retrieval 18.6 %, lemmas only 20.4 %, proofs only 29.0 %, both 30.0 % |
| Goal clones (Ghanbari, ECOOP 2025) [P, https://arxiv.org/html/2504.19129v1] | goal | alpha-equivalence of goals generalised over their context | Rocq via Coq-LSP | clone-finder | 40 projects: "27.73 (with median being 0.5)" clones per project; half the projects have none |
| HolStep baselines (Kaliszyk, Chollet, Szegedy 2017) [P, https://ar5iv.labs.arxiv.org/html/1703.00426] | step and conjecture | characters or tokens of the printed statements | text | dataset | usefulness of a step: logistic regression 0.71, CNN 0.82 to 0.83 |

## 4. Annotated taxonomies of moves (block D)

- **PaMpeR** (Nagashima and He, ASE 2018) [P, https://ar5iv.labs.arxiv.org/html/1806.07239].
  Question: which proof method did the human apply to this proof state. Features: "108 assertions
  manually written in Isabelle's implementation language, Standard ML", about the goal and about the
  goal against its context, for example "check if the outermost constant of the first goal is the
  meta-logic universal quantifier", whether the goal has a schematic variable, a constant defined
  with `inductive`, a term of a type defined with `datatype`, a constant from theory `Nat`. Data:
  425,334 invocations of 239 methods from the Isabelle library and the AFP. Model: one regression
  tree per method; 10 % held out. Result (Tables II to IV), share of held-out invocations where the
  human's method is in the top n: `simp` 58 at n = 1 and 98 at n = 2; `auto` 60 and 94; `rule` 3 at
  n = 1 and 86 at n = 3; `cases` (689 held-out uses) 16 at n = 4 and 80 at n = 10; `induct` (568) 27
  at n = 5 and 79 at n = 15; `induction` (185) 37 at n = 4; `case_tac` (362) 10 at n = 5. Not shown:
  the labels are single-step methods, not lemma-level moves; arguments are not predicted;
  alternatives count as errors, so the rates are "conservative estimates"; classes are imbalanced
  (§2.2). The data set (Nagashima, CICM 2020) [P, https://ar5iv.labs.arxiv.org/html/2004.10667], 113
  assertions as 0/1 vectors, is public at https://doi.org/10.5281/zenodo.3819026 and comes with no
  baseline.
- **Induction arguments** (Nagashima) [P, https://ar5iv.labs.arxiv.org/html/2001.10834 ,
  https://ar5iv.labs.arxiv.org/html/2009.09215]. smart_induct: 20 heuristics on the syntax of the
  goal; on 50 induction proofs from three AFP files the human's arguments rank first in 33, in the
  top three in 37 and in the top ten in 45; it "struggles to predict the choice of experts for
  structural induction" because it cannot tell which variables to generalise. sem_ind: 44 heuristics
  that also read the definitions of the constants; "22 Isabelle theory files with 1,095 applications
  of the induct tactic"; top-1, 3, 5, 10 coincidence 38.2, 59.3, 64.5, 72.7 % against 20.1, 42.8,
  48.5, 55.3 % for smart_induct. The weights are set by hand; the heuristics themselves are for J.
- **Strategy selection from static problem features** (Bridge, Holden, Paulson; JAR 2014)
  [P, pdf, https://www.cl.cam.ac.uk/~lcp/papers/Reports/Bridge-ml.pdf]. 6,118 TPTP problems; 14
  static features (among them the fractions of unit, Horn, ground, positive, negative and mixed
  clauses; maximum and mean clause length, depth and weight) and dynamic ones taken after 100 given
  clauses; labels are which of five E heuristics is fastest. Test set of 1,530: the best fixed
  heuristic proves 774, an oracle 906, and "The SVM trained using static features is the
  best-performing combination here, proving 833 theorems"; dynamic features alone give 810. It shows
  that a handful of static counts on the problem recover a little under half the gap to the oracle
  (my arithmetic: 59 of 132 theorems).
- **Informal mathematics.** Pease and Martin's typology of Mini-Polymath 3, as reported by Corneli
  et al. 2018 [P, pdf by keyword, https://arxiv.org/pdf/1803.06500]: five comment types (examples,
  conjectures, concepts, proofs, other) over "147 comments over 27 threads", ten comments in two
  types, coded by the two authors together. ProofFlowBench [P]: 184 proofs with step graphs
  "initially generated by LLMs, followed by human verification", 8.4 nodes each. Neither gives an
  agreement figure.
- **Taxonomies with counts but no classifier.** REPLica's classes of edits (§2.5); FormalMATH's
  error classes on 100 failed proofs per prover, LLM-assisted and human-reviewed (incomplete proof
  44 to 93 %, misuse of automation tactics 43 to 78 %) [P]; misformalisation classes in [E §1.9].
  HolStep proposes, and does not evaluate, "Predicting whether a statement is an important one
  (human named)". LLM2Ltac (§1.2) and Strat2Rocq [S] have an LLM name strategies and never list or
  validate the names.

**Table D. Labelled data on moves.**

| Work | Unit labelled | Labels | Who labelled; agreement | Predictor, result |
|---|---|---|---|---|
| PaMpeR | proof state | 239 proof methods | the proof script; none | regression trees on 108 assertions; `induct` top-5 27 %, `cases` top-4 16 % |
| smart_induct, sem_ind | induction goal | arguments of `induct` | the proof script; none | hand-weighted heuristics; top-1 38.2 % on 1,095 |
| Bridge et al. | first-order problem | fastest of five heuristics | by running all five | SVM on 14 static features; 833 against 774 of 1,530 |
| ILP rules (Table C) | proof state | tactic | the proof script | rules plus k-NN; improvement shown only in a figure |
| Mini-Polymath 3 | blog comment | five content types | two authors jointly; none | none |
| ProofFlowBench | NL proof step | dependency edges | LLM, then people; none | ProofScore structural term |
| REPLica | edit | change classes | authors; none | none |
| This library | decomposition | 17 moves | harvest agents, three review lenses; none measured | none yet |

## 5. What has not been measured

Each gap is stated as a question the library could put.

1. **Can the decomposition move be predicted from the parent statement alone?** PaMpeR predicts the
   next proof method from the proof state with prover-computed features; sem_ind predicts induction
   arguments. No study predicts a lemma-level move (strengthen, generalise, interface lemma, key
   invariant), and none restricts itself to the statement text.
2. **Does a human decomposition help a fixed model, and at what token cost?** Cobblestone's oracle
   is the one direct test: two sets of 100 Coq theorems, opposite signs, no token accounting by arm.
   RLMEval's easy mode and IMO-Steps give the lemmas but lack the matching arm.
3. **How much of the gain comes from the move's name, how much from the child statements, how much
   from the glue?** No experiment separates the three. DSP's "no in-line comments" and "no informal
   proof" rows are the nearest.
4. **What share of generated children are ill-typed, false, insufficient or unused, by move?** Not
   reported for any LLM prover ([F §9], §1.4); the symbolic and verification tools of §1.5 report
   rejection rates, none by move. MathlibLemma and IsarStep give the rates for stand-alone
   statements only.
5. **Do features of the statement predict the shape of the human decomposition** (number of
   children, glue lines, depth)? Matichuk et al. and the AFP replication relate statement size to
   proof size only, and the relation fails in half the AFP.
6. **Do annotators agree on the move?** No corpus reports agreement (§4). The library's labels come
   from harvest agents and have not been re-labelled blind.
7. **How often does each lemma-level move occur in ordinary developments?** Method and tactic
   frequencies exist (§2.2); the frequency of strengthening, generalising or introducing an
   interface lemma does not. The library is a set of exemplars and cannot supply base rates.
8. **How much do text-only features lose against elaborated ones on one task?** The evidence is
   indirect: symbols against structure in Mizar, names against graph on HolStep, TF-IDF against
   node2vec in MLFMF (§3). No paper runs a text tier and a prover tier of the same features on the
   same labels.
9. **Is a rule-bound decomposition better than a free one with the model held fixed?** [F §8] found
   none; the oracle and demonstration experiments of §1.1 to §1.3 do not test it either. The nearest
   test is AutoVerus's rule table against a generic agent at equal budget, 37 against 17 tasks, on
   proof repair and on tasks the rule table had already solved (§1.5).

## 6. Features with precedent

One row per feature. "Text" means computable from source text with a tokeniser; "parser" needs the
term structure of inner syntax; "prover" needs elaboration or a loaded session. The last column
gives the task the feature was shown to help and by how much; "descriptive" means no downstream test
exists.

| # | Feature | Source | How computed | Needs | Shown to help |
|---|---|---|---|---|---|
| 1 | Symbol set of the statement, weighted by rarity | MePo, MaSh, KUV SYM, TacticToe | constants (and logical operators) occurring; weight log of inverse frequency, or 1 + 2/log(n+1) | prover in the originals; text if identifiers stand in for constants | premise selection baseline: 998 of 2,078 (KUV); MePo peak 38.9 % |
| 2 | Subterm patterns with variables abstracted | MaSh (depth 2, variables to types), TacticToe (variables to V), KUV TRM0 | every subterm, variables replaced | parser; types need the prover | KUV 998 to 1,050; with matching generalisations 1,130 |
| 3 | Walks in the term tree, length up to 3 | ENIGMA, Tactician, KUV PAT | symbol sequences along paths; counts | parser | ENIGMA 22 to 41 problems; KUV PAT 1,127 |
| 4 | Types, type classes, theory name, local flag | MaSh | from the elaborated statement and its theory | prover; theory name is text | not ablated |
| 5 | Neighbouring statements (chained facts, ten preceding facts, preceding file) | MaSh; miniCTX | features of neighbours at reduced weight; or the file prefix as context | text | miniCTX 11.72 to 27.08 %; in MaSh not ablated |
| 6 | Identifier category and qualified path | Passport | global definition, local variable or constructor; module path | prover in the original; binder scan in text | more proofs: globals +16 %, constructors +8 %, locals +0.5 % |
| 7 | Outermost connective or quantifier; top symbol of the goal | PaMpeR, ML4PG, TacticToe | head of the term after stripping binders | parser | PaMpeR as a whole (§4); not ablated per assertion |
| 8 | Kind of definition behind the statement's constants (inductive, datatype, recursive function) and their theories | PaMpeR; sem_ind; ACL2(ml) | look up each constant's defining command | prover; text when the definition is in a file the entry copies | `induct` top-5 27 %; sem_ind top-1 38.2 % |
| 9 | Clause shape: number of clauses and literals; Horn, unit equation, conditional equation; mean and maximum clause length and depth | Blanchette et al. §5; Bridge et al. | clausify, then count | prover or clausifier; premise and conclusion counts are text | strategy selection 774 to 833 of 1,530; otherwise descriptive |
| 10 | Statement size by recursive unfolding of definitions | Matichuk et al. [D §1.5]; Blanchette et al. §4 | distinct constants reached from the statement | prover | proof size: R² 0.15 to 0.85 raw in seL4; below 0.5 in half the AFP |
| 11 | Text size; size after compression | Staples 2013; Wiedijk | normalised lines; gzip bytes | text | code size from spec size R 0.89 to 0.95 (31 points) |
| 12 | Nesting depth of the proof | Blanchette et al. Fig. 5 | depth of Isar blocks; how they computed it is not stated [U] | text for Isar | descriptive |
| 13 | Proof-style counts (apply chains, apply-to-Isar switches, bare `auto`, compound methods) | Isabelle linter | patterns over outer-syntax tokens | text after tokenising | descriptive |
| 14 | Per-step table: tactic name, argument kind, argument is a hypothesis, subgoal count | ML4PG | first five steps | tactic names text; subgoal counts prover | clustering only |
| 15 | Depth-by-arity matrix of the statement's term tree | ACL2(ml) | 7 by 7 cells, symbol class codes | parser | clustering only |
| 16 | Position in the dependency graph: recursive uses U and dependencies D, U·D/S with S the statement size, PageRank, longest chain; depth; fan-in, fan-out | Kaliszyk and Urban 2014; Li et al. 2026; Aspinall and Kaliszyk | from the dependency DAG | prover in general; text inside an entry where the glue cites its children | lemma ranking +3 points; in Mathlib centrality tracks infrastructure |
| 17 | Statement-level against proof-level references | MLFMF; Li et al. 2026; TheoremGraph; `\uses` in blueprints [H §2.4] | names cited in the statement, names cited in the proof | prover for exact edges; text for names | node2vec link prediction 0.95 to 0.98; 43.9 % of Mathlib edges proof-only |
| 18 | Pairwise statement similarity by Jaccard index of symbol sets | Aspinall and Kaliszyk (LCOM) | set overlap | text | descriptive: module means 57 to 76 % dissimilar |
| 19 | Formula graph with shared subexpressions and named variables | FormulaNet; Paliwal et al. | merge equal subterms; keep binding edges | parser | 83 to 90.3 %; 45.67 to 49.95 %; names hidden, 12.6 points lower |
| 20 | Proof-state text similarity to stored proofs (BM25) | Rango | token overlap, best state per proof | states need the prover; statements are text | 20.4 to 30.0 % |
| 21 | Step-dependency DAG of a proof | ProofFlow; TacMiner; Paperproof | which step uses which earlier result | LLM or prover; Isar labels in text (my reading) | ProofScore 0.417 to 0.545 |
| 22 | Proof history, remaining length | LeanProgress | language model on state and history | prover | 62.5 to 75.8 % accuracy |
| 23 | Duplicate goals up to renaming | Ghanbari 2025 | alpha-equivalence after generalising over the context | prover | descriptive: half of 40 projects have clones |

Reading the table (opinion, fairly sure): rows 1, 5, 11, 12, 13 and 18 are within reach of a
tokeniser; rows 2, 3, 7, 9 and 15 need a term parser for inner syntax but no prover; rows 4, 8, 10
and the exact forms of 16 and 17 need the prover. The measured effects are largest for rows 2, 3, 19
and 20, and every one of those was measured on premise selection or tactic prediction, not on
choosing a decomposition.

## 7. Experiment designs the library could support

The five designs are my proposals. Each names the prior baseline, the data and the threat I think
most serious. The library has 229 entries in 17 moves (all statuses), 12 to 23 for each of the
eleven mathematical and verification moves, in Lean, Isabelle and Rocq.

1. **Move from statement (gap 1).** Predict the move label from features of the parent statement
   only, by leave-one-source-out cross-validation, once per feature tier. Baselines: the majority
   class; PaMpeR's top-n coincidence for `induct` and `cases` (§4); for the tier comparison, KUV's
   998 against 1,130. Data: parent statements and labels as they stand. Threat: the entries were
   chosen as clear exemplars, so their goals may show the move more plainly than goals met in
   practice; with about 15 entries per class, a difference of three entries is within noise. I think
   a negative result here would be informative and a positive one would not yet be.
2. **Blind re-labelling (gap 6).** Have two annotators who do not see the label assign a move to a
   stratified sample of 60 entries, from the parent, children and glue; report Cohen's kappa and the
   confusion matrix. Baseline: none exists, which is the point. Threat: the classes overlap by
   design (strengthening against generalising, key invariant against induction), so a low kappa may
   reflect the taxonomy and not the annotators; model annotators that share training data with the
   harvest agents would agree for the wrong reason.
3. **Oracle ladder with the model fixed (gaps 2 and 3).** For entries that build under the pool
   server, give one student model the parent with (a) nothing, (b) the move name, (c) the child
   statements as `sorry` lemmas, (d) children and glue; measure tokens per closed leaf and parents
   closed. Baselines: Cobblestone's 38/43/52 and 48/50/47; RLMEval's 8.76 against 14.70; DSP's 39.3
   against 38.9. Data: the Isabelle entries first. Threat: the sources are public and the model has
   probably seen them, so arm (a) is inflated; perturbing names does not remove this. A second
   threat is that only buildable entries enter, and those lean towards small self-contained sources.
4. **Error rates of generated children (gap 4).** For each parent, have the fixed model propose
   children under a named rule and with no rule; classify each child as ill-typed (build), refuted
   (nitpick, quickcheck), insufficient (parent fails with children as `sorry`) or unused. Baselines:
   MathlibLemma's 70 % compile rate and 54 % false among judge-rejected; IsarStep's 58 % well-formed
   and 28 % correct; [F §9]. Threat: "false" is observed only when a counterexample finder succeeds,
   so the false rate is a lower bound and differs by move for reasons unrelated to the model.
5. **Retrieval of a decomposition (gap 8).** Leave one entry out, retrieve its nearest neighbours by
   statement features, and score whether a neighbour has the same move and whether its child shapes
   match. Baselines: TF-IDF against structure in MLFMF and KUV; Rango's gain from retrieving proofs
   over lemmas. Threat: entries from one source resemble each other in vocabulary, so retrieval must
   be scored across sources, which leaves few neighbours for moves that one project dominates.

My guess is that designs 2 and 3 are worth most: 2 because every other use of the labels rests on
it, and 3 because it is the experiment the field has run once.

## 8. Unverified items, and discrepancies with surveys A, D, E, F, H

- **[E §0.7]** says "model fixed, harness varied" has one precedent. With matched token budgets that
  still holds as far as I found; without that condition SorryDB, Cobblestone and miniCTX are
  precedents (§1.3).
- **[D §1.5]** is headed "Statement size predicts proof size, quadratically". The AFP-wide
  replication by an overlapping author group (§2.1) limits this to verification-style developments;
  D cites neither that replication nor Aspinall and Kaliszyk's null result.
- **[H §4.3, §7]** leaves the release of the Mathlib network data as [U]. The paper gives a Hugging
  Face data set, a GitHub repository and a Zenodo archive (§2.3). Its node count is inconsistent
  between abstract and §5.
- **[F Table 2]** gives DSP's automation ablation in the column for decomposition ablations; the
  nearer control is the row without the informal proof, 3.7 and 5.3 points lower (§1.1). [F §0.7]'s
  list omits the ablations of §1.2, none of which contradicts it.
- **[A §4.8]** on SorryDB agrees with what I read; [B §B1]'s miniCTX-v2 figure was not checked.
- **Leads from my own memory that were wrong.** MacKenzie, Fleuriot and Vaughan, "An Evaluation of
  the Archive of Formal Proofs" [P, https://ar5iv.labs.arxiv.org/html/2104.01052], is a usability
  survey of 30 respondents, not a corpus study. smart_induct was evaluated on 50 proofs, not 109.
  LeanProgress reports 75.8 % and a 41.4 % baseline. TacticToe's 34.5 % is E prover, not HOLyHammer.
  REFACTOR's 733.5 is not the overall usage.
- **Inconsistencies inside sources**, repeated as found: Cobblestone's combined-oracle pair;
  RLMEval's "over 75%" against a table mean of 68.3 %; smart_induct's 65 % for 33 of 50; IMO-Steps'
  1,329 and 1,330 lemmas.
- **[U]** Fig. 5 of Blanchette et al. and the ordering of the matching-term variants in KUV's Table
  5 were read from converted text that lost its layout. DSP's figure of 154 problems "without
  sketching", returned by the extract, could not be placed and is not used. IMO-Steps' exclusion of
  automation-provable lemmas rests on the extract.

## Source index

URLs are given inline at each entry and in Table C, and for §1.5 in the next paragraph; all were
fetched on 2026-11-15. The 60 sources read as [P] for the first draft are the 16 of §1.1 to §1.4,
the 14 of §2 (Staples et al. 2013, Blanchette et al. 2015, Aspinall and Kaliszyk 2016, LeanProgress,
Megdiche et al. 2022, CoqGym, LeanDojo, Li et al. 2026, FormaTheoria, Alama et al. 2011, Wiedijk
2000, REPLica, Shi et al. 2025, Jain et al. 2025), the 22 first cited in Table C, MacKenzie et al.
2021 (§8), the 6 of §4 (PaMpeR, its data set, smart_induct, sem_ind, Bridge et al. 2014, Corneli et
al. 2018), and one left to J: Sonoda, Akiyama and Uezato, arXiv 2602.10512, read in v1 of 11
February 2026, "Don't Eliminate Cut: Exponential Separations in LLM-Based Theorem Proving" [P,
https://arxiv.org/html/2602.10512v1, first 100,000 characters], theory only in the part read ("a
flat (cut-free) learner provably requires exponentially more data than a cut-aware hierarchical
learner"). The current version, v2 of 7 May 2026, is titled "Exponential Sample Complexity
Separation between Flat and Hierarchical Agentic Theorem Provers" [P abstract]; J §4.7 quotes the
abstract of v2.

The 25 sources of §1.5 [P], fetched 2026-11-15. PDFs: IsaPlanner case analysis,
https://www.cse.chalmers.se/~jomoa/papers/CaseAnalysis_ITP_2010.pdf ; QuickSpec, HipSpec and
IsaCoSy, in the same directory, quickspec-JFP.pdf , hipspec-cade.pdf and ConjSynthesisJAR2011.pdf ;
TheSy, https://arxiv.org/pdf/2009.04826 ; CCLemma, https://par.nsf.gov/servlets/purl/10555783 ;
lfind, in Sivaraman's thesis, https://escholarship.org/uc/item/9cd41151 ; Reynolds and Kuncak,
https://infoscience.epfl.ch/record/201755 ; Boogie VC splitting,
https://mmoskal.github.io/pdf/splitting.pdf ; cube-and-conquer,
https://www.cs.utexas.edu/~marijn/publications/cube.pdf . HTML at https://ar5iv.labs.arxiv.org/html/
followed by the identifier: 1405.3426 (Hipster), 1401.4330 (cut introduction), 2108.11204 (kSubS),
2206.00702 (AdaSubS), 2205.11491 (HTPS), 2306.05854 (SMT partitioning), 1309.4501 (Ganesalingam and
Gowers). HTML at https://arxiv.org/html/ followed by the identifier: 2504.04942 (Lemmanaid, v6),
2411.01829 (ProD-RL, v1), 2509.06493 (BFS-Prover-V2), 2506.11487 (DSP+, v1, with its figure files
x3.svg, x5.svg and x8.svg), 2310.04870 (Lemur, v5), 2311.07948 (Loopy, v1), 2405.16792 (Laurel, v2),
2409.13082 (AutoVerus, v3).

Links seen and not fetched: AFP mining data http://www21.in.tum.de/~blanchet/afp_mining_data.tgz ;
MaSh data http://www21.in.tum.de/~blanchet/mash2_data.tgz ; Mathlib network code
https://github.com/MathNetwork/mathlib-network ; PaMpeR data https://doi.org/10.5281/zenodo.3819026
; proof-metrics tools http://homepages.inf.ed.ac.uk/da/proofmetrics/ (Aspinall and Kaliszyk).

Secondary only [S]: Strat2Rocq, arXiv 2510.10131 (search summary: CoqHammer success raised by
13.41 %); Heras and Komendantskaya, "Recycling proof patterns in Coq"; Pease and Martin 2012;
Isabelle clone detection by Ghanouchi and by Vinan and Hupel, as cited by Ghanbari; the ICLR
abstract of ProofFlow, which a search summary reports with different baseline figures. Local files:
`README.md`, `library/README.md`, `library/INDEX.md` (entries per move counted with `awk`), and
surveys A, B, D, E, F, H as cited.
