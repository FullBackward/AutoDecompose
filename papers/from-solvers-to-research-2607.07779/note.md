# From Solvers to Research: LLM-Driven Formal Mathematics at the Research Frontier

| Field | Value |
|---|---|
| Authors, organisation | Eric Jiang, Xiao Liang, Junyi Zhang and 38 others (41 names, reader's count), among them Terence Tao, Andrea Bertozzi, Nanyun Peng, Amit Sahai and Wei Wang. University of California, Los Angeles; one author at Lawrence Livermore National Laboratory |
| Date and version read | Version 4, 4 November 2026. Version 1 is dated 8 July 2026 (arXiv submission history) |
| Source | arXiv 2607.07779, https://arxiv.org/abs/2607.07779 |
| Licence of the source | CC BY 4.0 (arXiv page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Sections 1, 3, 5.1, 5.2, 5.3.2, 5.3.3, 5.4, 6, 7 and 8 in full from the arXiv HTML. Figure 2 read from the PDF text (page 9), because the HTML does not render it. Section 2, Section 4 and Section 5.3.1 searched only. Other figures not viewed |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given. **[S]** the statement comes from a secondary source, which is named. **[U]** the
statement is not verified. A number without a tag is not permitted.

## 1. What the work is

The work is a survey. It reviews how language models produce formal proofs, and it asks what
evidence a research claim needs. It covers public records up to 20 October 2026 [P, Section 5].
Its main claim is that the unit of analysis must be the "versioned workflow" [P, Section 1]. A
versioned workflow is the full dated record of a result. The record holds the statement, the
models, the tools, the proof environment, the cost, the human actions and the review history. It gives no new experiment. It has 327 reference entries (reader's count from the
PDF) and 50 pages [P, PDF].

## 2. How it works

The survey sorts methods on three axes that can overlap [P, Section 3; Figure 2].

1. *Training strategies*: how a model is fitted (supervised training, reinforcement learning,
   training with search in the loop).
2. *Inference-time mechanisms*: how candidates are made and chosen. The four leaves are planning
   and decomposition, retrieval, ranking and search, and verifier-guided repair.
3. *Stateful or agentic workflows*: how state, tools and feedback pass between calls. The four
   leaves are persistent state and libraries, tool use, multi-agent coordination, and knowledge
   promotion and reuse.

The survey then defines four *evaluation objects*: a benchmark theorem, a repository task, a
formalisation project, and an open research claim [P, Section 7.1, Table 7]. It states that these
are not levels of one scale. It adds six *evidence dimensions* [P, Section 7.2]. They are:
fidelity of the target, scope of the verification, disclosure of workflow and resources,
availability of artefacts, human contribution, and originality with external review. A checklist
of seven fields turns the dimensions into reporting duties [P, Section 7.4].

## 3. How it splits a proof

The survey does not split proofs. It classifies the systems that do, and the classification is
coarse.

- **One leaf, no sub-classes.** "Planning & Decomposition" is one leaf below inference-time
  mechanisms. It lists DSP, DeepSeek-Prover-V2, SubgoalXL, Seed-Prover 1.5, LEAP and
  Goedel-Architect [P, Figure 2]. The text has one paragraph of six sentences on it
  [P, Section 3.2, "Planning and theorem decomposition"].
- **The criterion.** "Decomposition is useful only when the intermediate obligations are faithful
  and checkable" [P, Section 3.2]. A plan must be judged "by the checked obligations it induces,
  not by fluency alone" [P, Section 3.2].
- **A second axis that matters more.** The survey sorts stateful systems by how long a retained
  object lives [P, Section 3.2]. FormalEvolve keeps candidates for one problem. LEAP and
  Goedel-Architect keep a blueprint for one problem. DreamProver and ProofEvolve keep lemmas or
  schemas across problems. The stated distinction is "what persists after a call and what evidence
  licenses its reuse" [P, Section 3.2].
- **What is absent.** The survey does not class a split by its unit, by who chooses it, by a
  check before work on the children, or by its record. It names no move such as induction or
  case split.

## 4. What it says about scale

The survey has no section on build cost. The words "recompile" and "merge queue" do not occur
(searched). It gives these scale facts, all from other sources:

- Anthropic: an eleven-day multi-agent formalisation of Fermat's Last Theorem on Prove2Me
  [P, Section 5.2].
- OpenAI, Navier-Stokes: about 10,000 concurrent agents, about 2.7 million messages, about 130
  billion output tokens over 88 hours, and 17 more hours for Lean [P, Section 5.3.2].
- OpenAI collection at commit 1581d4cb: 719 manuscripts in 372 families [P, Section 5.3.3,
  Table 5].
- Large projects are named without figures [P, Section 7.3]. The survey asks that a scale claim
  "name a dated release or immutable commit" [P, Section 7.3].

It warns that orchestration raises "specialization, parallel sampling, and total inference cost"
together, so a gain needs "budget-matched ablations" [P, Section 3.3].

## 5. Evidence

The work is a survey, so there is no result table and no ablation. Its content in numbers:

| Item | Value | Place |
|---|---|---|
| Method axes and leaves | 3 axes, 11 leaves | Figure 2 |
| Evaluation objects | 4 | Table 7 |
| Evidence dimensions | 6 | Section 7.2 |
| Checklist fields | 7 | Section 7.4 |
| Platforms compared | 7 (Lea, Theo, AI co-mathematician, Prove2Me, TheoremDB, Formal Conjectures, Palomar) | Table 6 |
| OpenAI families examined | 4 (numbers 102, 087, 003, 032) | Table 5 |

**What the survey lists that `docs/research/` does not.** A name search over surveys A to L on
21 November 2026 found no mention of these (reader's check):

- Systems: DreamProver, FormalEvolve, LeanAgent, ImProver, ProofOptimizer, ReForm, MPS-Prover,
  3D-Prover, Bourbaki, LemmaHead, LTRAG, PALM, MASA, TheoremLlama, Alchemy, Abel, process-verified
  reinforcement learning, PhysProver, Nazrin, LongCat-Flash-Prover, Pythagoras-Prover, NanoProof,
  Maestro, DeepTheorem.
- Platforms: Lea, Theo, the AI co-mathematician, TheoremDB, Palomar.
- Benchmarks: TCS-Bench, TaoBench, First Proof, TheoremBench, MathlibPR, FaithformBench,
  ProofJudge, AdvancedMathBench, OEIS Open, MathAtlas, MechGeo, MA-ProofBench, CAM-Bench.

Three of these bear on decomposition. DreamProver consolidates lemmas across problems. TheoremDB
records each attempted tactic with its outcome and cost, so a later agent does not repeat it
[P, Section 6.2]. Palomar registers a fixed repository snapshot and checks it with Comparator
[P, Section 6.3].

**What the survey does not list.** It has no section on industrial systems. Companies appear
inside other sections. A search finds no mention of Math Inc's Gauss, of Axiom Math, or of Meta's
RepoProver and AutoformBot (reader's check). Harmonic's Aristotle appears in one sentence of the
main text and in the multi-agent leaf of Figure 2 [P, Section 3.3; Figure 2].

## 6. Limits

Stated by the authors: the survey is "narrative, non-exhaustive" [P, Section 1]. The dated cases
are no "validated ranking of systems" [P, Section 1]. The authors did not rebuild the OpenAI Lean
developments [P, Table 5 caption].

Found by the reader: one author (Tao) is also the author of two cited records, Palomar and an
essay [P, Sections 6.3 and 8.5.1]. The decomposition class is too coarse to compare two splitting
methods. The survey's
cut-off is before Axiom's release of 26 October 2026 and before both anchors.

## 7. Relation to the two anchors

Both anchors are later than version 4, and neither cites the survey (checked in the two reference
files). The survey cites no anchor.

**Turing Agent (arXiv 2611.21299).** The survey's criterion for a split is "faithful and
checkable". Turing Agent enforces the second property with its Lean check of the children against
the parent. The survey names the benchmarks that Turing Agent uses: RLMEval and Formal TCS
[P, Section 7.3]. Its demand for budget-matched ablations names the gap in Turing Agent: no
ablation isolates the split, and no cost is given.

**MathEye (arXiv 2611.22103).** The survey proposes a three-layer "versioned relational
representation" of concepts, declarations and proof fragments [P, Section 8.2]. It cites a
"structural-hypergraph" proposal as a research agenda only. MathEye's proof dependence graph is a
working hypergraph of this kind for one proof. A search of the survey for "angelic" and
"sketching" finds nothing, so it does not cover MathEye's precursors.

## 8. What this repository can use

- **Class each library entry by the survey's missing fields.** Unit, chooser, check before the
  children, record, and action on failure are the fields that the survey lacks. The library
  already has them, so the 229 entries can give the finer taxonomy.
- **Adopt the seven-field checklist for experiments.** The field "outcome accounting" asks for
  failed and excluded branches and the denominator. Survey K's experiment plans can use it.
- **Use the retention axis for the proposed algorithm.** A split method must say what it keeps
  (a lemma, a blueprint, a schema) and what check permits reuse.
- **Use the test protocol of Section 8.2.** It holds out whole problem families and tests on a
  later library version. This fits a test of the feature graphs.

## 9. Open points and things not read

- Section 2 (foundations), Section 4 (benchmark tables) and Section 5.3.1 (Erdős problems) were
  not read. Figures 1 and 3 to 8 were not viewed.
- The name search uses spelling patterns. A system that the earlier surveys describe under another
  name is counted as absent.
- Versions 1 to 3 were not compared with version 4.
