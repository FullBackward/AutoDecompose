# L. Cross-prover decomposition: prior work above one proof assistant (as of 2026-11-16)

Prepared 2026-11-16 for AutoDecompose, whose owner wants to decide how to split a goal into lemmas
at a level independent of the proof assistant and to render the split into Lean, Rocq and Isabelle.
This is a novelty check, not a survey. It tries to refute three claims: (a) no prior work defines
decomposition moves or proof strategies above the prover and runs or renders them in more than one
assistant; (b) no prior corpus holds lemma-level decompositions of real proofs from several
assistants under one taxonomy of moves, or one schema of parent, children and how they fit; (c) no
prior work measures whether a decomposition made for one assistant transfers to another, or compares
the decomposition of one theorem across assistants. Earlier surveys: [F §x], [J §x], [K §x].

Method. Seventeen web searches (one extended); then 25 pages and 6 PDFs downloaded whole with `curl`
and searched as plain text (PDFs through `pdftotext`). A quotation is a string I saw in the
downloaded text; a number is my reading of the text or table. Tags as in [F]: **[P]** read in the
primary source during this search; **[S]** secondary, or from memory; **[U]** unverified or not
found; "[P abstract]" means abstract only. URLs were fetched on 2026-11-16.

Could not be fetched or found: the CLAM-HOL papers (Cloudflare challenge; the Edinburgh abstract
record was read); the body of Babel-formal (workshop abstract page only); the Tinker paper after its
§2.3 (ar5iv breaks off); Ωmega and λClam (not re-tried after [J]); the Logipedia site; Leanstral
(known through ITPEval's appendix). Not looked up: POPLmark; the regularity lemma in Isabelle and in
Lean; the Flyspeck blueprint; hol2dk. Not found: an LLM harness whose decomposition step is shared
by two assistants (three searches; ITPEval's related-work table); a corpus across assistants
labelled with moves (two searches; the two of [K]); an experiment that fixes one assistant's lemma
skeleton and measures proving in another (one search); a blueprint tool for Isabelle (one search).

## 0. Findings in brief

1. **Strategies above the prover ran in more than one prover before the LLM provers.** CLAM's plans
   became HOL tactics; Tinker's strategy graphs have interfaces to Isabelle and ProofPower; Why3
   splits a goal by fixed transformations and hands the pieces to Coq, Isabelle/HOL or PVS. Their
   moves are in-proof steps (split, case, induct, ripple), not lemma-level moves (§1) [P].
2. **Agents on two assistants share the search loop, not a decomposition.** COPRA: one loop, a
   prompt per assistant. ProofWala: one tactic-step record for Lean and Rocq (§2) [P].
3. **Benchmarks align statements, not proofs.** PutnamBench: "We do not include any of the formal
   proofs in our benchmark." The Seventeen Provers: "I did not ask for a formalization of any
   specific proof" (§3) [P].
4. **One benchmark of July 2026 aligns whole files with their helper lemmas across four assistants
   and measures translation.** ITPEval, best model, real-library files: 15.2 % of translated lemma
   skeletons type-check and 5.2 % of translated proofs compile. Its authors write that "no large
   aligned corpus of proofs exists across systems" (§4) [P].
5. **Transfer below the lemma structure has been measured twice.** Dependencies of matched HOL4
   theorems raise HOL(y)Hammer on HOL Light from 30 to 40 %; Lean training data raises a Rocq step
   model from 45.54 to 53.47 % pass@5 after fine-tuning (§2, §4) [P].
6. **One theorem's decomposition has been compared across assistants by hand, a few times:**
   Tarjan's algorithm in Why3, Coq and Isabelle (49 and 46 lemmas); 101 Isabelle lemmas re-proved in
   Coq (544 against 1,190 tactics); Odd Order in Rocq and in an agent-built Lean development (§5)
   [P]. None uses a common schema or labels moves.

## 1. Proof structure and strategy languages above one prover

- **Declarative proof text** (Wiedijk; Wenzel and Wiedijk) [P pdf,
  https://www.cs.ru.nl/~freek/pubs/sketches2.pdf , https://www.cs.ru.nl/~freek/notes/mv.pdf ,
  https://www.cs.ru.nl/~freek/pubs/romantic.pdf]. A formal proof sketch is a Mizar proof with steps
  left out, and "the notion of formal proof sketch makes sense for any declarative language".
  "Several systems (Hyperproof, Mizar, Isabelle/Isar) all basically have the same proof language".
  Euclid's proof "is shown in both systems", Mizar and Isar, written twice by hand. Not measured.
- **TLA+ proofs** [P, https://ar5iv.labs.arxiv.org/html/1208.5933]. "The TLA+ proof language and
  TLAPS have been designed to be independent of any particular theorem prover." The split is written
  once; its leaves go to Isabelle/TLA+, Zenon and SMT solvers as back ends. See also [J §7.2].
- **Why3** [P, https://www.why3.org/doc/itp.html; J §5.1]. Fixed transformations split a goal stated
  in Why3's logic, and a piece can go to an assistant: "Why3 offers the possibility to call an
  interactive theorem prover instead" (Coq, Isabelle/HOL, PVS). I think this is the nearest working
  system to the owner's design. The pieces are separate obligations; Lean is not a target.
- **Proof planners** [P abstract, https://www.dai.ed.ac.uk/daidb/papers/documents/rp885.html]. CLAM
  plans by methods and critics [J §1.1, §1.3]; "the interface sends HOL goals to CLAM for planning
  and translates plans back into HOL tactics". CLAM's own prover was Oyster [S, memory].
- **Tinker** [P to §2.3, https://ar5iv.labs.arxiv.org/html/1410.8217; J §1.5]. PSGraphs "should be
  seen as a generic, theorem prover-independent tool"; Tinker "currently has interfaces implemented
  for both Isabelle and ProofPower". A node is run "by calling the underlying tactic function" of
  the prover; the part I read shows a different graph in each prover, not one graph in both.
- **Hiproofs** [P pdf, https://www-live.dfki.de/fileadmin/user_upload/import/4972_pgtactic-mcs.pdf]:
  labelled parents and children on a proof tree, "independent of both the underlying logic and the
  prover being used"; captured for HOL Light [P, https://ar5iv.labs.arxiv.org/html/1307.2713].
- **Minilang** [P, https://arxiv.org/html/2507.18885; F §2.5]: "it is possible to port at least the
  core of Minilang to other proof assistants like Lean"; no port is reported. Visored's "accepted
  proof can be re-emitted as a checked Lean file" [P abstract, https://arxiv.org/abs/2606.17581].

## 2. Agents and learned provers on more than one assistant

- **COPRA** [P, https://arxiv.org/html/2310.04353v5]. A GPT-4 agent that proposes one tactic at a
  time in a backtracking search. "Our current implementation of Copra allows for proof generation
  in both Lean and Coq." It has a system prompt per assistant and no decomposition step.
- **ProofWala** [P, https://arxiv.org/html/2502.04671 (v3)]. One interface and one proof-step record
  for Lean 4 and Rocq; step models trained on one language or both. Table 3, pass@5, one language
  against both: Lean 28.25 to 30.58 % (p = 0.018); three Rocq sets gain 0.4 to 1.4 points (my
  arithmetic; not significant); CategoryTheory after fine-tuning 45.54 to 53.47 (p = 0.008), where
  "we found structurally analogous Lean theorems". The shared level is the tactic step.
- **DSP, DSP+ and others.** Draft-sketch-prove was built for Isabelle [F §2.1] and rebuilt for Lean
  [J §4.7]; no sketch moves between them. Leanstral is said to show "Rocq to Lean translation" [S,
  ITPEval appendix D.2]. Three searches for an agent or sketch language on all three found none.

## 3. Benchmarks and corpora aligned across assistants

- **miniF2F** [P, https://ar5iv.labs.arxiv.org/html/2109.00110]: "488 problem statements" for
  "Metamath, Lean, Isabelle (partially) and HOL Light (partially)"; proofs "optionally attached".
  **In Rocq** [P, https://arxiv.org/html/2503.04763v2]: "478 out of 488 theorems (98%)" translated
  by LLMs, "ignoring proofs"; pass@1 from informal text 43 %, from the Lean version 40 % (Table 2).
- **PutnamBench** [P, https://arxiv.org/html/2407.11214]: "640 formalizations in Lean 4 and
  Isabelle, and 412 formalizations in Coq", "aligned in their structure, including hypothesis naming
  and framing"; no proofs. Baselines: DSP 4/640 in Isabelle, COPRA 1/640 in Lean, 1/412 in Coq.
- **MMA** [P, https://arxiv.org/html/2311.03755]: 244 K Isabelle and 88 K Lean 4 statements with
  machine-written informal versions, not aligned with each other; training on both helps each.
  **KELPS** [P abstract, https://arxiv.org/abs/2507.08665]: natural language into "Knowledge
  Equations", then by rules into "Lean, Coq, and Isabelle": one intermediate language, statements.
- **Catalogues.** Wiedijk's list: "Lean 100 HOL Light 99 Isabelle 95 Rocq 80" on the day of this
  search [P, https://www.cs.ru.nl/~freek/100/]. **The Seventeen Provers of the World**: √2 in 17
  systems with their lemmas [P pdf, https://www.cs.ru.nl/~freek/comparison/comparison.pdf].

## 4. Proof translation and library alignment

- **Logical frameworks.** Thiré [P, https://ar5iv.labs.arxiv.org/html/1807.01873] exports "an
  arithmetic library containing Fermat's little theorem to OpenTheory and to two other proof
  systems" (Coq and Matita); "about 300 lemmas". My reading: the lemma structure arrives intact
  because whole proof terms are translated. OpenTheory: [P, https://www.gilith.com/opentheory/].
- **OAF** [P, https://ar5iv.labs.arxiv.org/html/2005.03089]: the libraries "of Coq, HOL Light, IMPS,
  Isabelle, Mizar, and PVS into a universal format: OMDoc/MMT". One schema for six assistants'
  declarations; a proof may be "dependency-only". It holds "low-level data structures that are
  suitable for the kernel and not the high-level structure that is seen by the user". MLFMF: [K §3].
- **Gauthier and Kaliszyk** [P, https://ar5iv.labs.arxiv.org/html/1509.03527]. "Certain conjectures
  can be proved directly from the dependencies induced by similar proofs in the other library."
  HOL(y)Hammer "could automatically find proofs for 30% of the HOL Light problems, can prove 40%
  with the knowledge from HOL4". What transfers is the set of lemmas a proof uses.
- **Babel-formal** [P abstract, https://neurips.cc/virtual/2025/131109]: proof terms as "a pivot
  language for translating proof scripts between proof assistants"; "aligned sources (14 files, 117
  lemmas) across Lean and Rocq".
- **ITPEval** [P, https://arxiv.org/html/2607.19407]. "A four-way aligned cross-ITP benchmark with
  1,560 source files and 6,848 theorems and lemmas across Lean 4, Rocq, Isabelle, and HOL Light."
  Parts: Babel-formal extended (16 items, 660 lemmas, "we authored all four versions ourselves");
  58 of Wiedijk's theorems from real libraries (232 files, 4,924 lemmas; a unit is "the entire
  source file, including the headline theorem plus supporting lemmas"); 316 miniF2F statements.
  Statement translation starts from "a source file with all proof bodies replaced by placeholders",
  and "all statements in the file must type-check together": best model 47.4 % and 15.2 % on the
  first two parts. Proof translation: 29.7 % and 5.2 %. The statement task is in effect the
  transfer of a lemma skeleton; no parent or child is recorded, and no prover is given a skeleton.

## 5. The same theorem in several assistants; blueprints outside Lean

- **Tarjan's algorithm in Why3, Coq and Isabelle** (Chen, Cohen, Lévy, Merz, Théry)
  [P, https://ar5iv.labs.arxiv.org/html/1810.11979]. "the proof relies on the same arguments in the
  three formal systems". Why3: "The proof uses 49 lemmas". Isabelle: 46 lemmas, "starting from an
  initial version of the Why3 proof"; "Similar as in the Coq proof, the overall induction proof was
  explicitly decomposed into individual lemmas". The invariants moved across by hand.
- **Concrete Semantics in Coq** [P, https://ar5iv.labs.arxiv.org/html/1808.06413]. "We have
  reproven 101 lemmas from the Isabelle/HOL theories" with CoqHammer: Isabelle 2,806 lines and 544
  tactics; Coq 3,493 lines, 1,190 tactics, 468 hammer calls. The lemma list was kept, by hand.
- **FormaTheoria against the Rocq Odd Order proof** [P, §5.6 of https://arxiv.org/html/2608.10894;
  K §2.3]. Both follow the same two books: 40,549 Rocq lines, 626,021 Lean lines. The Lean side
  "has fewer declarations than the Rocq development in five sections, but eighty times as many in
  PF Part I Section 6", which the authors ascribe to "the decomposition found by RefineAgent".
- **Blueprints.** Lumsdaine [P pdf, https://coq-workshop.gitlab.io/2024/files/EA9.pdf] had "begun a
  port" of leanblueprint "adapted for Coq"; no release found [U]; no two-assistant blueprint found.

## 6. Comparison

| Work | Assistants | Assistant-independent level | What transfers | Measured |
|---|---|---|---|---|
| Wiedijk; Wenzel and Wiedijk §1 | Mizar, Isabelle/Isar | proof text | one proof, written twice | no |
| TLA+ proofs §1 | Isabelle/TLA+, Zenon, SMT | proof text | leaf obligations | no |
| Why3 §1 | Coq, Isabelle/HOL, PVS | strategy (fixed transformations) | subgoals as obligations | no |
| CLAM-HOL §1 | HOL; Oyster [S] | strategy (proof plans) | plans, as tactics | not in the abstract |
| Tinker §1 | Isabelle, ProofPower | strategy (graph language) | the tool; nodes are per prover | no |
| Hiproofs §1 | generic; HOL Light capture | proof-structure schema | nothing | no |
| Minilang; Visored §1 | Isabelle; own prover, Lean export | proof text | Visored: accepted proof to Lean | no |
| COPRA §2 | Lean, Coq | none | the search loop | per assistant only |
| ProofWala §2 | Lean 4, Rocq | none (tactic-step record) | training data | yes: 28.25 to 30.58; 45.54 to 53.47 |
| DSP, DSP+ §2 | Isabelle; Lean | none (rebuilt) | the design | no |
| miniF2F; in Rocq §3 | Metamath, Lean, Isabelle, HOL Light; Rocq | statement | statements | 478/488 translated |
| PutnamBench §3 | Lean 4, Isabelle, Coq | statement | nothing | per assistant only |
| MMA; KELPS §3 | Isabelle, Lean; plus Coq | statement | training data; statements | MMA: joint training helps |
| Wiedijk's list; Seventeen Provers §3 | many | none (theorem name) | nothing | no |
| Thiré; OpenTheory §4 | Matita to Coq, OpenTheory; HOL family | proof term | whole library, lemma for lemma | checked, not scored |
| OAF §4 | six | declaration and dependency | nothing (export only) | no |
| Gauthier and Kaliszyk §4 | HOL4, HOL Light | dependency sets | lemmas used by matched theorems | yes: 30 to 40 % |
| Babel-formal §4 | Lean, Rocq | proof term | proof scripts | yes; figures not read |
| ITPEval §4 | Lean 4, Rocq, Isabelle, HOL Light | none (file to file) | lemma skeletons; proofs | yes: 15.2 %, 5.2 % on real files |
| Tarjan §5 | Why3, Coq, Isabelle | informal argument | invariants, by hand | counts: 49 and 46 lemmas |
| Concrete Semantics §5 | Isabelle to Coq | lemma list | 101 statements, by hand | yes: 544 against 1,190 tactics |
| FormaTheoria §5 | Rocq, Lean | source sections | nothing (compared afterwards) | yes: lines; declaration counts |
| Lumsdaine §5 | Coq (begun) | dependency graph of a text | nothing | no |

## The three claims

**(a) Refuted as worded; partly anticipated once narrowed.** Why3 decides a split above the
assistant and renders the pieces for Coq, Isabelle/HOL and PVS; Tinker is a strategy language with
two prover interfaces; CLAM's plans became HOL tactics. Each defeats "proof strategies ... in more
than one proof assistant". They lack lemma-level moves (strengthen, generalise, state an interface
lemma), a choice among competing moves [J §0, finding 10], the targets Lean, Rocq and Isabelle
together, and output as a lemma-structured proof. Nearest prior work: Why3, then Tinker. Opinion:
the claim can be kept as "no prior work chooses lemma-level moves from a statement representation
common to Lean, Rocq and Isabelle and renders one split in all three"; I think that form stands. I
am moderately sure: proof planning was read in abstracts only, and Ωmega not at all.

**(b) Partly anticipated.** The taxonomy clause stands: I found no corpus across assistants labelled
with lemma-level moves, and [K §4] found none inside one assistant. The schema clause is anticipated
at a coarser grain: OAF and MLFMF hold declarations and their dependencies from several assistants
in one format; hiproofs give a prover-independent schema of parent, children and labels, captured
for one prover; ITPEval aligns 58 real theorems with their helper lemmas across four assistants
(4,924 lemmas) without recording which lemma serves which. Nearest prior work: ITPEval's
real-library part. I am fairly sure of the taxonomy clause and less sure of "any common schema":
dependency exports are many and I read two. Opinion: what is new in the library's 229 entries is
the record of parent, children and move, not the alignment.

**(c) Refuted as worded for comparison; partly anticipated for transfer.** Comparison by hand
exists: Tarjan in three systems, 101 Concrete Semantics lemmas in two, Odd Order in two, Euclid in
Mizar and Isar, √2 in seventeen. Transfer has been measured for whole files (ITPEval), dependency
sets (Gauthier and Kaliszyk), tactic-step data (ProofWala) and statements (miniF2F in Rocq). Not
found: an experiment that fixes the lemma skeleton of assistant A, gives it to a prover in B, and
compares with a native skeleton or none; a comparison under one schema over more than a handful of
theorems. Nearest prior work: ITPEval for transfer, Chen et al. for comparison. Opinion: narrowed to
those two experiments the claim stands today. I am moderately sure; ITPEval is four months old, and
my guess is that follow-up work is in progress.

## Source index

URLs are given inline at each entry (all fetched 2026-11-16). Repository: [F §2.1, §2.5]; [J §0,
§1.1 to §1.5, §4.7, §5.1, §7.2]; [K §2.3, §3, §4]. Not reached: the CLAM-HOL papers at
https://core.ac.uk/download/28971047.pdf ; https://logipedia.inria.fr ; Tinker beyond its §2.3.
Downloaded and not used: arXiv 1808.09701 (Isabelle/HOL and Coq compared), arXiv 2601.15294
(KnowTeX), https://1000-plus.github.io/ , and the Springer chapter on Isabelle/Naproche.
