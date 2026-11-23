# J. Automating decomposition outside the LLM harnesses: mechanisms, triggers and checks (as of 2026-11-15)

Prepared 2026-11-15 for AutoDecompose, which will decompose hard goals into lemmas by rules and is
about to extract features from the 229 entries of `library/` to learn when each move applies.
Survey F reports how LLM harnesses decompose. This survey reports how the splitting of a goal into
subgoals or lemmas has been automated elsewhere. The sibling survey K covers experiments and
measurements; where a work belongs to both, the method is given here and the numbers are left to K
with one line. K §1.5 was added after both surveys were drafted, to hold the numbers of the 25
works whose field (6) points to it. Sections 1-7 take seven families in turn; §8 compares them on
six fields; §9 lists the goal features that prior automation keys on; §10 proposes what could be
tried on the library. Earlier surveys are cited as [A §x], [B §x], [D §x], [F §x], [I §x] and not
repeated.

Method. (i) arXiv abstract pages and HTML (arxiv.org/html, ar5iv), documentation and repositories,
read through a fetch tool that returns extracts written by a small model and caps quotations at
about 125 characters; quotations are limited to text the extract returned. (ii) Eighteen PDFs read
as text after `pdftotext`: Bundy 1988; Ireland and Bundy, CADE-13; Johansson's thesis; the
IsaPlanner case-analysis paper; HipSpec; QuickSpec; IsaCoSy; TheSy; CCLemma; Sivaraman's thesis
(for lfind); the CVC4 induction report; the Sledgehammer Isar paper; Boogie VC splitting; Cobleigh
et al.; bi-abduction; cube-and-conquer; slides on AVATAR; AutoCorres (PLDI 2014; text converted
for [D]). (iii) The local library, for §10. Tags as in [F]: **[P]** read in the primary source
during this survey; **[S]** secondary, or from memory; **[U]** unverified or not found. A tag in a
heading covers the entry unless a sentence carries its own; "[P abstract]" means abstract only.

Could not be fetched or found: Ireland and Bundy, "Productive Use of Failure in Inductive Proof"
(JAR 1996; 403), so the critics rest on the authors' CADE-13 paper and on Johansson's thesis; the
current ACL2 manual (403; the v6-1 page was read); Walsh's divergence critic and the TheSy page
on ar5iv (conversion failures; TheSy was read from the arXiv PDF); the Ωmega/MULTI paper (403);
the AVATAR paper; the lfind OOPSLA PDF (certificate error; the first author's thesis was read);
the bodies of the Diaframe, AdaSubS, Tinker, Peano and ProofCompass papers; chapters 5-7 of "QED
at Large"; IsaScheme; Vampire's induction paper; the Lean blog post on functional induction. Two
searches found no decomposition method dated after 2026-11-11; I do not claim there is none.

Field key, used in every entry and in Table 1: **(1)** what is decomposed (goal kind, prover);
**(2)** how the split is proposed: fixed rule, search, learned model, or extraction from an
existing proof; **(3)** which features of the goal trigger or select the split; **(4)** how the
split is checked before effort is spent on it; **(5)** code; **(6)** reported effect in one line.

---

## 0. Findings in brief

1. **Lemmas are proposed from two directions.** Top-down methods read a stuck goal (critics, lemma
   calculation, lfind, CCLemma, the sorrifiers of [F §3]); bottom-up methods enumerate over the
   signature and never look at a goal (QuickSpec, HipSpec, IsaCoSy, TheSy) (§2) [P].
2. **The features that trigger a split in symbolic automation are few and syntactic:** the head
   connective of the goal or of a hypothesis; the recursive functions in the goal and their
   recursion arguments; an `if` or `case`; the difference between hypothesis and conclusion;
   repeated subterms; and, in verification, the program's syntax (§9) [P].
3. **The oldest rule catalogue with applicability conditions is keyed on failure, not on the
   goal.** Proof critics attach a patch to each pattern of "precondition failure" of rippling
   (§1.3); AutoVerus's table from error class to repair agent and Laurel's placement rule repeat
   the design, with a verifier's message as the pattern (§5.8, §5.9) [P].
4. **Lemma speculation by critic did not transfer.** Re-implemented in IsaPlanner, it met "few
   proofs for which this critic was applicable and successful"; the same thesis then built
   bottom-up synthesis instead (§1.3, §2.3) [P].
5. **A counterexample filter before proof effort is routine outside the LLM harnesses:** CLAM's
   conjecture disprover (1996), IsaCoSy's quickcheck, QuickSpec's testing, CCLemma's
   characteristic vectors, lfind's QuickChick filter, CVC4's ground-fact filter. [F §9] found two
   such gates among its harnesses (§2, §8) [P].
6. **Program verification has the most mechanical decomposition and leaves one creative step.**
   Verification conditions are split by connective, path or assertion, and proofs by callee and
   statement; the invariant or intermediate assertion is left to a person or a model and is
   checked by the verifier, with Houdini pruning in Loopy and AutoVerus (§5) [P].
7. **Learned subgoal generators condition on goal text alone.** kSubS, HTPS, ProD-RL and the
   subgoal-demonstration line name no features; their checks are reachability by a low-level
   policy or a proof of the lemma (§4) [P].
8. **Lemmas are extracted from finished proofs in three ways:** a grammar over the term instances
   of a cut-free proof (Hetzl et al.); graph statistics over intermediate facts (Kaliszyk and
   Urban); and a classifier trained on proofs in which a used theorem has been inlined, so that
   recovering it is the label (REFACTOR) (§3) [P].
9. **Two works learn method selection from a corpus with explicit features:** PaMpeR (108 boolean
   assertions, regression trees) and TacticToe (constants, types, abstracted subterms, k-NN).
   PaMpeR recommends special-purpose methods well and general-purpose ones poorly, and induction
   arguments needed hand-written heuristics over the constants' definitions (§7.5-7.7) [P].
10. **Fixed-rule decomposers that print a proof skeleton exist in three provers:** the TLA+
    Toolbox, Isabelle (`sketch`), and Ganesalingam and Gowers's prover. None chooses among
    competing moves: the user picks, or a fixed priority list decides (§7.1-7.3) [P].
11. **Stopping rules for splitting are numeric proxies of child difficulty:** decisions times
    assigned variables in cube-and-conquer, a squared cost estimate in Boogie, a 50 % slowdown
    bound when Sledgehammer merges steps (§3.4, §5.2, §6.1) [P]. This adds to [F §0, finding 4].
12. **Harnesses missing from [A] and [F] add no new check.** BFS-Prover-V2's planner, DSP+,
    ProofCompass, Cobblestone and ProD-RL validate subgoals by syntax or by proof only (§4) [P].

---

## 1. Proof planning, rippling and strategy graphs

### 1.1 Explicit proof plans (Bundy, CADE-9, 1988) [P, https://era.ed.ac.uk/handle/1842/4561]
(1) Inductive conjectures; the plan specifies LCF-style tactics. (2) Fixed rules: "A method is a
frame containing information about the preconditions and effects of a tactic"; a planner chains
methods. (3) Syntactic properties of the goal, stated in a meta-logic: an input "pattern which
must match the before formula", plus preconditions. For induction: "use the occurrence of
recursive functions in the conjecture to suggest what induction scheme to use", and induct on the
variable in the recursion argument. (4) None; the tactic may still fail. (5) None given. (6)
Worked examples from a subset of the Boyer-Moore strategy.

### 1.2 Rippling with case analysis in IsaPlanner (Johansson, Dixon, Bundy, ITP 2010) [P, https://www.cse.chalmers.se/~jomoa/papers/CaseAnalysis_ITP_2010.pdf]
(1) Step cases of inductions in Isabelle/HOL; rippling is due to Bundy et al. (1993) [S]. (2) A
fixed heuristic: rewrite only while a measure decreases. (3) Three features. (a) The *embedding*
of the induction hypothesis in the goal, and the *wave-fronts*, the parts of the goal that differ
from it. (b) An `if` or `case` in the goal: "After each ripple-step, the case splitting
techniques for case- and if-statements are tried". (c) A common subterm of a blocked goal: lemma
calculation "applies common subterm generalisation to the goal and attempts to prove the
resulting lemma by induction". The induction variable is not chosen by a feature; the default is
"structural induction on a single variable". (4) Before a split, try to prove that one branch is
taken. (5) http://dream.inf.ed.ac.uk/projects/isaplanner (not checked live). (6) 47 of 87; see
K §1.5.

### 1.3 Critics: patches keyed on how rippling fails
Sources: Ireland and Bundy, JAR 1996 [U, not fetched]; their "Extensions to a Generalization
Critic for Inductive Proof", CADE-13 [P, https://homepages.inf.ed.ac.uk/rbf/MY_DAI_OLD_FTP/rp786.pdf];
Johansson's thesis, Edinburgh 2009, §2.5.1 and ch. 6
[P, https://www.cse.chalmers.se/~jomoa/papers/moajohansson-thesis.pdf].
(1) Failed step cases in CLAM 3. (2) A fixed table: "proof patches ... associated with different
patterns of precondition failure" [P, CADE-13]. (3) The way the ripple method failed, in the
thesis's summary of the four critics [P]:
- no wave-rule applies, but one matches except for a missing wave-front: revise the induction;
- the condition of a conditional wave-rule cannot be proved: split on that condition;
- no wave-rule applies and one side is fully rippled: *lemma calculation* (§1.2);
- weak fertilisation is not applicable: *lemma speculation*, a schematic lemma whose second-order
  meta-variables are instantiated by later ripple steps;
- a sideways ripple is blocked by a missing sink: generalise by introducing an accumulator.

(4) "A conjecture disprover, therefore, is used to filter candidate instantiations of the
schematic conjecture" [P, CADE-13]. (5) None found. (6) The negative result of finding 4:
Johansson re-implemented lemma speculation in IsaPlanner; "there are few proofs failing in this
way", and in Isabelle's list library she "found only one inductive theorem to which lemma
speculation was even applicable" [P, ch. 6].

### 1.4 ACL2's induction heuristic [P, https://www.cs.utexas.edu/~moore/acl2/v6-1/INDUCTION.html]
(1) Any conjecture that reaches induction. (2) Fixed rule. (3) Each application of a recursive
function suggests the induction that unwinds it, provided "the controlling actuals are distinct
variables": `(append x y)` suggests one, `(append (foo x) y)` does not. Candidates are combined
for cliques of functions and some are vetoed because they "flaw" others; `:induction` rules add
pairs of pattern and scheme. (4) None. (5) In ACL2. (6) Boyer and Moore 1979, ch. XIV, has the
heuristics in full [S].

### 1.5 PSGraph and Tinker (Grov, Kissinger, Lin, 2013-14) [P, https://ar5iv.labs.arxiv.org/html/1302.6890, §1-4; P abstract, https://arxiv.org/abs/1410.8217]
(1) Proof strategies for Isabelle (Tinker also for ProofPower): a graph whose nodes are tactics
and whose wires carry goals. (2) A hand-drawn graph. (3) *Goal types*, "predicates describing the
features of a goal": each output wire has one, and a new subgoal goes down the wire whose type it
satisfies. Examples: `top_symbol(...)`, `inductable`, `hyp_embeds`, `measure_reducible`. (4) The
type is the check: "If no output type matches a goal, then evaluation fails". (5)
https://github.com/ggrov/tinker (the README targets Isabelle 2013). (6) None in the part read.
Grov and Maclean [P abstract, https://arxiv.org/abs/1303.2975] propose to generalise example
proofs into such graphs through a lattice of goal types. I think this is the nearest precedent for
the project's plan: a rule is a tactic node, and its applicability condition is a conjunction of
named goal predicates. Ωmega/MULTI (Melis, Meier, Siekmann, AIJ 2008) was not read [S].

---

## 2. Lemma discovery and theory exploration

These systems produce lemma statements; the prover decides afterwards which of them a parent
needs. HipSpec's authors state the two directions: "Instead of waiting for the proof to somehow
get stuck, we use bottom-up lemma discovery" [P].

### 2.1 QuickSpec (Smallbone, Johansson, Claessen, Algehed, JFP 2017) [P, https://www.cse.chalmers.se/~jomoa/papers/quickspec-JFP.pdf]
(1) No goal: a signature of Haskell functions yields equations. (2) Enumeration in order of size.
(3) The signature only. The enumeration is over *schemas* ("a term in which all variables have
been replaced by a hole"); conditional laws arise only from predicates the user names. (4) Random
testing groups terms into classes; pruning by normal forms under the laws found so far is
interleaved with testing. (5) https://github.com/nick8325/quickspec. (6) See K §1.5.

### 2.2 HipSpec (CADE 2013) [P, https://www.cse.chalmers.se/~jomoa/papers/hipspec-cade.pdf] and Hipster (CICM 2014) [P, https://ar5iv.labs.arxiv.org/html/1405.3426]
HipSpec. (1) Properties of Haskell programs. (2) QuickSpec's conjectures, unpruned, go to a prover
that works "by enumerating all possible ways of doing structural induction over the free
variables". (3) The signature and an order: "prove simpler equations before more complicated
ones". (4) Testing; each proved equation becomes a lemma for later attempts. (5)
http://www.github.com/danr/hipspec. (6) It finds the accumulator lemma for `rev xs = qrev xs`,
which the authors say lemma calculation cannot reach; see K §1.5. Hipster does the same for
Isabelle/HOL on functions the user names, and adds a filter worth copying: a conjecture proved by
the *routine* tactic (simplifier, then Metis) is discarded as trivial, and one that needs the
*difficult* tactic (structural induction first) is kept. A lemma is thus defined as interesting
by which tactic closes it. Code: https://github.com/moajohansson/IsaHipster.

### 2.3 IsaCoSy (Johansson, Dixon, Bundy, JAR 2011; draft read) [P, https://www.cse.chalmers.se/~jomoa/papers/ConjSynthesisJAR2011.pdf]
(1) Isabelle/HOL theories of recursive datatypes. (2) Bottom-up synthesis of terms by size. (3)
The signature and the current rewrite rules: "only irreducible terms, those not matched by the
left hand side of any rewrite rule, are synthesised"; each proved theorem adds constraints. (4)
"counter-example checking is used to prune out the obviously false ones" (quickcheck); survivors
go to IsaPlanner. (5) In IsaPlanner. (6) See K §1.5. IsaScheme instantiates user-given schemes
with a theory's constants [S].

### 2.4 TheSy (Singher and Itzhaky, CAV 2021) [P, https://arxiv.org/pdf/2009.04826]
(1) A signature of inductive datatypes and recursive definitions. (2) Term generation by depth,
conjecture inference, screening. (3) *Symbolic observational equivalence*: terms are evaluated on
symbolic examples built from constructors to a bounded depth, inside an e-graph. (4) Screening
drops conjectures that known lemmas imply; the method "eliminates the need for random testing as
a filtering phase and for SMT solvers". (5) None in the text read. (6) See K §1.5.

### 2.5 CCLemma (Kurashige et al., ICFP 2024) [P, https://par.nsf.gov/servlets/purl/10555783]
(1) Equations over recursive functions, in its own prover. (2) Goal-directed: saturate an e-graph
for the stuck goal, propose *connector lemmas* ("those that can merge two distinct e-classes"),
and generalise each by replacing common subterms with fresh variables. (3) Pairs of e-classes with
the same *characteristic vector* (the values of the class under many assignments). (4) "if two
e-classes have different c-vecs, this serves as a counterexample to any lemma that equates terms
from those e-classes"; subsumed lemmas are dropped. (5) https://github.com/cole-k/cc-lemma [S].
(6) See K §1.5.

### 2.6 lfind (Sivaraman et al., OOPSLA 2022; read in Sivaraman's UCLA thesis, ch. 2) [P, https://escholarship.org/uc/item/9cd41151]
(1) A stuck Coq goal. (2) Generalise the goal in every way by replacing terms with variables;
from each generalisation make *sketches* with one term replaced by a hole; fill the hole by
data-driven synthesis from examples of the proof state. (3) The subterms of the goal and their
values on examples. (4) "Filtering removes lemmas that are determined to be either trivial,
redundant, or invalid", the last by QuickChick; the rest are ranked by whether a proof-search
tool proves them and the goal. (5) None in the text read. (6) 144 of 222 locations; see K §1.5.

### 2.7 Subgoals inside an SMT solver (Reynolds and Kuncak, VMCAI 2015; report read) [P, https://infoscience.epfl.ch/record/201755]
(1) Quantified conjectures in CVC4. (2) Candidate equalities enumerated by size, each introduced
as a splitting lemma that the solver proves by induction or refutes. (3) "active terms that refer
to variables in the conjecture being proven". (4) Candidates equivalent to others are removed, as
are "subgoals that are contradicted by ground facts in the current context". (5) In CVC4. (6) See
K §1.5. Vampire's induction with generalisation (CICM 2020) is the superposition counterpart [S].

### 2.8 Lemma analogy in ACL2(ml) (Heras et al., arXiv 1308.1780) [P, https://ar5iv.labs.arxiv.org/html/1308.1780]
(1) An ACL2 theorem in progress. (2) Mutate a source lemma by replacing each symbol with its
analogue from the cluster of its definition. (3) A term-tree matrix indexed by depth and arity
(K's subject). (4) "we test the validity of the set of generated equations using a
counter-example checker". (5) http://staff.computing.dundee.ac.uk/jheras/acl2ml (from the
paper). How the source lemma is chosen was not in the extract [U].

### 2.9 Lemmanaid (Alhessi et al., arXiv 2504.04942, v6 of June 2026) [P, https://arxiv.org/html/2504.04942]
(1) The symbols of an Isabelle theory yield lemma statements. (2) A fine-tuned LLM emits a
*template*, a statement whose operators are "replaced by schematic variables called holes", such
as `?H1 x1 (?H1 x2 x3) = ?H1 (?H1 x1 x2) x3`; a constraint solver fills the holes. (3) "the list
of symbols appearing in the body of the original lemma, as well as contextual information", that
is, types and definitions. (4) Well typed by construction; falsity is left to the user's
counterexample checker. (5) https://anonymous.4open.science/r/lemmanaid-emnlp. (6) 50 % (HOL) and
29 % (AFP) of held-out human lemmas recovered, the two figures coming from different prompt
variants, and the model being given the target lemma's symbols; see K §1.5.

---

## 3. Cut introduction and lemma extraction from existing proofs

### 3.1 Algorithmic cut introduction (Hetzl, Leitsch, Reis, Weller, arXiv 1401.4330) [P, https://ar5iv.labs.arxiv.org/html/1401.4330]
(1) A cut-free first-order proof, such as an automatic prover's output; the result is a shorter
proof with universally quantified cut formulas, that is, lemmas. (2) Extraction: take the set T
of terms that instantiate the quantifiers, find a grammar G with L(G) = T, and build the proof
with cuts from it. (3) Regularity among the instances, not the goal: the Δ-vector is "the biggest
common term of all t_i parametrized with some variable α". (4) Correct by construction. (5) GAPT,
http://www.logic.at/gapt/. (6) Exponential compression is a
theorem about one sequence of proofs; the five measured proofs keep 0.45 to 0.69 of their
inferences; see K §1.5.

### 3.2 Lemma mining over inference graphs (Kaliszyk and Urban, arXiv 1402.3578) [P, https://ar5iv.labs.arxiv.org/html/1402.3578]
(1) The intermediate facts of HOL Light and Flyspeck proofs: "around 1.7 billion" at kernel
level, about 1.07 million at tactic level. (2) Extraction, scoring, greedy selection. (3)
Statistics of each fact in the dependency graph: recursive uses U, recursive dependencies D and
size S (U·D/S and variants); longest inference chain over size; forward and reverse PageRank; the
number of edges the lemma would remove. (4) Every candidate is already a theorem. (5) Traces at
http://cl-informatik.uibk.ac.at/~cek/lemma_mining/. (6) A 21.4 % improvement on Flyspeck; see
K §1.2.

### 3.3 REFACTOR (Zhou, Wu, Li, Grosse, ICLR 2024) [P, https://arxiv.org/html/2402.17032]
(1) A Metamath proof tree; the output is a subtree to be made a theorem. (2) Learned: a graph
neural network labels each node as inside or outside the target. Training pairs come from
inlining: "Our idea is to reverse the process of theorem extraction, by expanding the proof of" a
used theorem inside its caller. (3) Character-level text of each node's name and statement, and
the tree's edges. (4) The predicted nodes must "form a connected component"; a Metamath verifier
checks the extracted theorem; duplicates are dropped. (5) https://github.com/jinpz/refactor. (6)
19.6 % of human-chosen theorems recovered on unseen proofs; see K §1.2.

### 3.4 ATP proofs turned into Isar (Blanchette, Böhme, Fleury, Smolka, Steckermeier, JAR 2016) [P, https://wwwbroy.in.tum.de/~blanchet/isar2.pdf]
[B §A4] gives the motivation. (1) A resolution proof by contradiction of an Isabelle goal; the
output is a direct Isar proof of `have`, `obtain` and case analyses. (2) Extraction by a
*redirection* algorithm. (3) Which atoms are *tainted* by the negated conjecture, and the shape
of the last derived clause: for a disjunction, "An m-way case analysis is called for". (4) Preplay
tests "the generated proofs for a few seconds before displaying them"; compression "performs the
merger if the resulting inference is fast enough--no more than 50% slower than the two original
inferences taken together". (5) In Isabelle (`isar_proofs`). (6) One example goes from 54 to 29
steps. Its intermediate facts are whatever the prover derived: sufficient by construction, and
not chosen for meaning.

Related: Peano (Poesia and Goodman, arXiv 2211.15864) [P abstract] lets an agent induce reusable
tactics from its own solutions; LEGO-Prover is in [A §1.6] and [B §C7]; ProofEvolve in [F §5.9].

---

## 4. Learned subgoal generation not covered by F

### 4.1 kSubS (Czechowski et al., NeurIPS 2021) [P, https://ar5iv.labs.arxiv.org/html/2108.11204] and AdaSubS (ICLR 2023) [P abstract, https://arxiv.org/abs/2206.00702]
(1) The INT inequality benchmark; a state is a token string. (2) A transformer generates a
subgoal, trained on the state k steps ahead on a solved trajectory (k = 3 for INT). (3) The
current state only. (4) A low-level policy must reach the subgoal within a step budget: "Only
these reachable by the low-level policy are used"; a value function orders the rest. AdaSubS
proposes subgoals at several distances and uses "A verification mechanism ... to filter out
unreachable subgoals". (5) https://github.com/subgoal-search/subgoal-search. (6) See K §1.5.

### 4.2 HyperTree Proof Search (Lample et al., 2022) [P, https://ar5iv.labs.arxiv.org/html/2205.11491]
(1) Metamath and Lean goals. (2) A learned tactic policy; a tactic is a hyperedge to the set of
subgoals it creates. There is no lemma generator. (3) The tokenised goal. (4) Tactic validity;
"the value of a parent is the product of values of its children". (5) None in the text read. (6)
See K §1.5. The decomposition is AND-branching, not the choice of a cut.

### 4.3 Subgoal-based demonstration learning (Zhao, Li, Kong, 2023) [P, https://ar5iv.labs.arxiv.org/html/2305.16366]
(1) miniF2F in Isabelle. (2) An LLM rewrites informal proofs into subgoal sequences over 15
rounds; a diffusion model orders the demonstrations. (3) Statement and informal proof, as text.
(4) "each subgoal in this sequence should be reachable from both the initial state" and the final
one; unreachable subgoals are split finer. (5) https://github.com/HKUNLP/subgoal-theorem-prover.
(6) See K §1.2. SubgoalXL, its successor, is in [A §1.8].

### 4.4 ProD-RL (Dong, Mahankali, Ma, arXiv 2411.01829) [P, https://arxiv.org/html/2411.01829]
(1) AFP theorems, Isabelle. (2) The model writes lemma statements inside its proof, enclosed "by
<invoke> and </invoke> tokens"; each becomes a child node, to a fixed depth. (3) Theorem and
context, as text. (4) Isabelle checks each proof with its lemmas as premises; a proved lemma
earns reward 1 even when its parent fails. (5) Test sets only,
https://huggingface.co/kfdong/ProD/tree/main. (6) 40.8 % to 45.5 % on its AFP test set,
against 43.4 % for the fine-tuned model that proposes no lemma; see K §1.5.

### 4.5 Cobblestone (Kasibatla et al., ICSE 2026) [P, https://arxiv.org/html/2410.19940]
(1) Coq theorems. (2) A mechanical cut inside LLM whole-proof samples: the failing tactic and what
follows become `admit`, and Cobblestone "makes one recursive call per subgoal in progress". (3)
The position of the first error and the bullet structure. (4) Coq executes each candidate;
CoqHammer is tried on each `admit`. (5) https://doi.org/10.5281/zenodo.17603489. (6) See K §1.1.
This is the sorrify-at-failure family of [F §3] in Coq. Prasad and Amin (ICLR 2025 workshop) [P
abstract, https://iclr.cc/virtual/2025/36230] likewise extract "lemmas at failure points".

### 4.6 BFS-Prover-V2's planner (Xin et al., arXiv 2509.06493) [P, https://arxiv.org/html/2509.06493]
(1) Lean 4. (2) A general LLM emits subgoals "formatted as Lean have statements", at the start
and again when the step prover exhausts its budget on one. (3) The theorem text; on replanning,
also the subgoals already proved. (4) No check of the statements is described; a proved subgoal
becomes a hypothesis. (5) None found. (6) 86.1 % to 95.1 % on miniF2F-test with the
planner, at budgets that are not matched; see K §1.5.

### 4.7 DSP+ (Cao et al., arXiv 2506.11487) [P, https://arxiv.org/html/2506.11487]
(1) Lean; a revival of [F §2.1]. (2) An LLM sketch of subgoals with their hypotheses; two fixed
masking rules: for a malformed subgoal "the subgoal line and all subsequent dependent lines are
directly commented out", and an erroneous proof line becomes `sorry`. (3) The theorem and an
informal draft; a syntax error triggers a mask. (4) Syntax only; wrongly formalised subgoals were
found after the proving phase. (5) https://github.com/microsoft/DSP-Plus. (6) See K §1.5.
ProofCompass (arXiv 2507.14335) [P abstract] has an LLM that "analyzes failed attempts to select
intermediate lemmas". Sonoda et al. (arXiv 2602.10512) [P abstract] argue from sample complexity
for learning a proof DAG that "solves each shared block once"; the argument is K's.

---

## 5. Program verification

### 5.1 Why3 transformations [P, https://www.why3.org/doc/technical.html]
(1) The verification condition (VC) of a WhyML function. (2) Fixed transformations, applied by the
user or a strategy: `split_goal` ("Change conjunctive goals into the corresponding set of
subgoals"), `case` ("Split a goal into two subgoals, using the excluded middle on a given
formula"), `assert`, `destruct` ("Eliminate the head symbol of a hypothesis"), `induction_ty_lex`.
(3) The connective structure: "splitting stops at disjunctive points like symmetric disjunction
and left-hand sides of implications". The author can steer it with the `by` and `so` connectives
and the attributes `[@stop_split]` and `[@case_split]`. (4) None described. (5)
https://www.why3.org. (6) None.

### 5.2 Boogie VC splitting (Leino, Moskal, Schulte, 2008) [P, https://mmoskal.github.io/pdf/splitting.pdf]; Dafny [P, https://dafny.org/latest/VerificationOptimization/VerificationOptimization]
Boogie. (1) One procedure's VC, split into several whose conjunction is equivalent. (2) A fixed
rule with a cost search. (3) The control-flow graph, a cost per node, and the paths that reach
each assertion: "We choose the horizontal split, where the sum of estimated times of resulting
VCs is minimal", time being cost squared, which favours equal parts. A dynamic mode splits on
timeout. (4) The split is proved sound and complete. (5) In Boogie. (6) See K §1.5. Dafny by default
"combines every assertion within that definition into a single assertion batch";
`{:isolate_assertions}`, `{:split_here}` and `{:focus}` cut it. The guide's manual moves are
intermediate assertions, `calc`, `assert ... by`, lemmas and opaque definitions, and its signal of
trouble is a coefficient of variation of the solver's resource count above 20 %.

### 5.3 Learned assumptions (Cobleigh, Giannakopoulou, Păsăreanu, TACAS 2003; RIACS report read) [P, https://ntrs.nasa.gov/citations/20030017771]
(1) A property P of two composed components. (2) The L* algorithm learns an automaton A such that
M1 under A satisfies P and M2 satisfies A: assumptions "are initially approximate, but become
gradually more precise by means of counterexamples". (3) The interface alphabet and the
counterexample traces. (4) Each conjectured A is model-checked against both premises. (5) LTSA.
(6) One NASA system. It is the one case found in which an *interface lemma* is produced by
counterexample-guided learning and not from the form of the goal.

### 5.4 Bi-abduction (Calcagno, Distefano, O'Hearn, Yang, JACM 2011) [P in part, https://www.cs.ox.ac.uk/people/hongseok.yang/paper/jacm11-biabduction-webversion.pdf]
(1) Memory safety of a program, reduced to Hoare triples per procedure: "each procedure is
analyzed independently of its callers". (2) Fixed proof rules: bi-abduction "jointly infers
anti-frames (missing portions of state) and frames (portions of state not touched by an
operation)". (3) Call sites and the form of the separation-logic assertions. (4) "guessing
preconditions is a potentially unsound step", so a forwards analysis checks them afterwards. (5)
Infer [S]. (6) Runs on sendmail and a Linux distribution. Diaframe (PLDI 2022) [P abstract] brings
"ideas from linear logic programming and bi-abduction" to Iris.

### 5.5 AutoCorres and crunch [D §1.2, §1.3]
AutoCorres produces each abstraction with its refinement proof by "a set of syntax-directed
rules" [P, https://trustworthy.systems/publications/nicta_full_text/7629.pdf]: the trigger is the
form of each statement. `crunch` generates one preservation lemma per callee by recursion over
the constants in a definition [D §1.2]: the trigger is the call graph. This is the library's
*per-callee-lemma* move in automated form.

### 5.6 Lemur (Wu, Barrett, Narodytska, ICLR 2024 [S, venue]) [P, https://arxiv.org/html/2310.04870]
(1) A C program with an assertion. (2) An LLM proposes an assumption at a program point, inside a
calculus (Propose, Decide, Backtrack, Repair, Success, Fail). (3) Trigger: the verifier answers
Unknown. Places: "right before loops and at the beginning of loops". (4) The verifier checks that
the assumption implies the goal; proposals are "treated as assumptions until we can prove that
they are invariants". (5) https://github.com/wu-haoze/Lemur-program-verification. (6) See K §1.5.

### 5.7 Loopy (Kamath et al., arXiv 2311.07948) [P, https://arxiv.org/html/2311.07948]
(1) C loops, checked by Frama-C. (2) An LLM proposes a *set* of invariants. (3) The program text;
repair prompts carry the checker's message. (4) Houdini removes candidates until it finds whether
a subset "is inductive and sufficient". (5) None in the text read. (6) 398 of 469; see K §1.5.

### 5.8 Laurel (Mugnier et al., OOPSLA 2025) [P, https://arxiv.org/html/2405.16792] [D §3]
(1) A Dafny lemma that fails for want of one `assert`. (2) An LLM writes it; a rule fixes where.
(3) The verifier's error message and the control-flow graph place a placeholder; in-context
examples are chosen by ProofSim, an edit distance over the lines and tokens of the surrounding
lemma. (4) Dafny re-verifies, up to 10 attempts. (5) Zenodo artifact; URL not in the extract. (6)
82 of 145 assertions; see K §1.5.

### 5.9 AutoVerus (Yang et al., OOPSLA 2025) [P, https://arxiv.org/html/2409.13082] [D §3]
(1) A Rust function with a Verus specification. (2) LLM agents in three phases. (3) A table from
error class to agent: "one repair agent is designed for each type of error" (invariant fails
before the loop, invariant fails at its end, assertion fails, overflow, postcondition fails). (4)
A static filter rejects candidates that change code or specification; a Houdini pass finds the
subset that verifies. (5) https://github.com/microsoft/verus-proof-synthesis [S]. (6) See K §1.5.

---

## 6. SAT/SMT divide and conquer, briefly

### 6.1 Cube-and-conquer (Heule, Kullmann, Wieringa, Biere, HVC 2011) [P, https://www.cs.utexas.edu/~marijn/publications/cube.pdf]
(1) A propositional formula, partitioned into cubes (partial assignments) for a CDCL solver. (2)
Lookahead search. (3) Two dynamic measures. The split variable is the one whose two branches both
simplify the formula most: variables are ranked by the product of the two branch evaluations. A
branch becomes a cube when "the product of the number of decisions and the number of assigned
variables" passes a threshold, which rises by 5 % per node and falls by 30 % on a conflict. (4)
The cubes cover the space by construction. (5) march_cc; no URL read. (6) See K §1.5. The aim is
that "the runtimes to solve each of the subproblems are comparable".

### 6.2 Partitioning for SMT (Wilson et al., FMCAD 2023) [P, https://ar5iv.labs.arxiv.org/html/2306.05854]
(1) An SMT query. (2) Cubes over chosen atoms, or one partition at a time. (3) After a warm-up
the atoms are read from solver state: the "variables with the highest activity scores", "the
earliest decisions in the trail", or the atoms most frequent in conflict clauses and theory
lemmas. (4) Exhaustive by construction. (5) In cvc5. (6) See K §1.5. AVATAR (Voronkov, CAV 2014) [S,
slides read] splits a clause into sub-clauses with pairwise disjoint variables and lets a SAT
solver choose the case. The family offers two ideas: choose a case split by its measured effect
on *both* branches, and stop by a cheap size proxy tuned to make the children comparable.

---

## 7. Explicit rule and pattern catalogues

### 7.1 A prover with human-style output (Ganesalingam and Gowers, arXiv 1309.4501) [P, https://ar5iv.arxiv.org/html/1309.4501, §1-2]
(1) Routine problems, "mostly but not exclusively in metric space theory", in the authors' own
prover. (2) Fixed rules: 27 named moves in five groups (deletion, tidying, applying, suspension,
equality substitution) in priority order. "The program repeatedly applies a move of the first
type it can from this list", without backtracking. (3) The head shape of a target or hypothesis.
Target ∀x (P ⇒ Q): peel and split. Target P ∧ Q: split. Hypothesis P ∨ Q: split into cases.
Target ∃x P: unlock with a placeholder variable. A definition is expanded when its expansion is
quantifier-free or begins with the right quantifier. (4) None described; the moves invent no
statement. (5) None in the part read. (6) See K §1.5.

### 7.2 The TLA+ Toolbox's Decompose Proof command [P, https://course.ccs.neu.edu/cs3650/parent/tla+/toolbox/plugins/org.lamport.tla.toolbox.doc_1.5.4.201710061831/html/prover/decompose.html]
(1) A TLAPS proof obligation. (2) A fixed menu; the user chooses by "clicking on the appropriately
labeled buttons". (3) The top connective. Goal P ⇒ Q becomes "the assumption P and the goal Q";
a universal goal introduces a new constant; a conjunctive goal becomes n steps; a disjunctive
assumption becomes a case split; an existential assumption becomes a constant and a fact. A
formula also qualifies if it is "a single occurrence of a user-defined operator whose definition
has that form". (4) TLAPS checks the generated steps afterwards. (5) In the Toolbox. (6) None.

### 7.3 Isabelle's `sketch` and `explore` (Haftmann, `HOL/ex/Sketch_and_Explore.thy`) [P, https://isabelle.in.tum.de/library/HOL/HOL-ex/Sketch_and_Explore.html]
(1) The current goal. (2) After an optional method given by the user, `sketch` prints "sketch of
Isar proof text after method application": `proof ... show ... sorry ... next ... qed`, with
`fix` and `assume` lines; `explore` prints `have ... moreover have ... ultimately show ?thesis`.
(3) None of its own: the children are the method's subgoals. (4) None. (5) In the distribution,
among "Experimental commands". (6) None. It is the mechanical half of the template moves of
[F §10, rules 5-9]: given the move as a method, it prints the children with their contexts.

### 7.4 Aesop (Limperg and From, CPP 2023 [S, venue]) [P, README, https://github.com/leanprover-community/aesop]
(1) Lean 4 goals. (2) User-registered rules: normalisation; safe ("A safe rule is applied eagerly
and is never backtracked"); unsafe, with success probabilities and best-first search. (3) A rule
fires on goals that match its index ("indexing methods similar to those of `simp`"); builders
include `apply`, `forward`, `destruct`, `constructors`, `cases`. (4) None. (5) The repository. It
is a catalogue whose applicability condition is an index pattern and a safety flag; of the
library's moves it holds case analysis and constructor introduction only.

### 7.5 PaMpeR (Nagashima and He, ASE 2018 [S, venue]) [P, https://ar5iv.labs.arxiv.org/html/1806.07239]
(1) An Isabelle/HOL proof state; the output ranks 239 methods, among them `induct`, `cases` and
`rule`. (2) One regression tree per method. (3) 108 hand-written boolean assertions on the first
goal and chained facts, for example: the outermost constant is the meta-level universal
quantifier; an HOL existential occurs but not outermost; there is a schematic variable; a
constant comes from the theory `Set`, `Nat` or `Real`; a type was introduced by `datatype`; a
constant was defined by `inductive` or by `fun`. (4) None; `why_method` explains a recommendation
by its assertions. (5) https://github.com/data61/PSL. (6) Trained on 425,334 points;
special-purpose methods are recommended well and general-purpose ones such as `safe` are not.

### 7.6 smart_induct and sem_ind (Nagashima, 2020-21) [P abstract, https://arxiv.org/abs/2001.10834; P, https://ar5iv.labs.arxiv.org/html/2009.09215]
(1) An inductive goal in Isabelle/HOL; the output is the arguments of `induct` (terms,
`arbitrary:`, rule). (2) 44 written heuristics score enumerated candidates. (3) The goal's syntax
and "the definitions of relevant constants": generalise a variable only if it changes in
recursive calls; compare the argument a defining equation recurses on with the position of the
induction term. (4) None. (5) https://github.com/data61/PSL. (6) The human's choice is ranked
first in 38.2 % of cases, against 20.1 % for smart_induct; see K §4.

### 7.7 TacticToe (Gauthier et al., arXiv 1804.00596) [P, https://ar5iv.labs.arxiv.org/html/1804.00596]
(1) HOL4 goals; the output is a tactic, never a lemma. (2) k-nearest neighbours over recorded
tactic calls, with tree search. (3) "names of constants, including the logical operators", type
constructors, and "subterms with all variables replaced by a single placeholder"; features of
assumptions and of the conclusion are tagged apart. (4) None. (5) `HOL/src/tactictoe`. (6) See
K §3, Table C.

### 7.8 Lean's functional induction (`Lean.Meta.Tactic.FunInd`) [P, https://lean-lang.org/doc/api/Lean/Meta/Tactic/FunInd.html]
The module derives `foo.induct` from a recursive definition: "For each branch of the original
function, there is a case in the induction principle", with a hypothesis per recursive call. The
split is a function of the definition, as in ACL2 (§1.4) and Isabelle's `f.induct`. The tactic
`fun_induction` is [S].

Catalogues without triggers. "QED at Large" (arXiv 2003.06458) [P, chapters 1-4] has no catalogue
of decomposition rules in the part read; its §6.2, "Proof Design Principles", was not reached.
Prog_Prove's patterns, Freitas and Whiteside, and Grov, Lin and Tumas are in [I §3.2].

---

## 8. Comparison on the six fields

**Table 1.** "by constr." means correct by construction; "—" means none or not described.

| Work | (1) Object | (2) Proposer | (3) Trigger or selecting features | (4) Check before effort | (5) Code | (6) Effect |
|---|---|---|---|---|---|---|
| CLAM methods §1.1 | inductive conjectures | fixed methods, planner | input pattern; meta-logic preconditions; recursion argument | — | — | examples |
| Rippling, IsaPlanner §1.2 | step cases, Isabelle/HOL | fixed heuristic | embedding of hypothesis, wave-fronts; `if`/`case`; common subterm | try to prove a branch first | project page | 47/87 |
| Critics, CLAM 3 §1.3 | failed step cases | fixed table, failure to patch | which precondition of rippling failed; missing sink | conjecture disprover | — | negative in IsaPlanner |
| ACL2 induction §1.4 | ACL2 conjectures | fixed rule | recursive calls on distinct variables; merge and veto | — | ACL2 | — |
| PSGraph, Tinker §1.5 | Isabelle, ProofPower goals | hand-drawn graph | goal-type predicates on wires | wire type must match | ggrov/tinker | — |
| QuickSpec §2.1 | signature to equations | enumeration over schemas | signature only | random testing; pruning | nick8325/quickspec | K §1.5 |
| HipSpec §2.2 | Haskell properties | bottom-up conjectures | signature; simplicity order | testing | danr/hipspec | K §1.5 |
| Hipster §2.2 | Isabelle/HOL | as HipSpec | user-named functions | testing; routine-tactic filter | IsaHipster | K §1.5 |
| IsaCoSy §2.3 | Isabelle/HOL theories | constrained synthesis | signature; irreducibility | quickcheck | in IsaPlanner | K §1.5 |
| TheSy §2.4 | signature | enumeration, symbolic evaluation | symbolic observational equivalence | screening | — | K §1.5 |
| CCLemma §2.5 | stuck equational goal | e-graph search, generalisation | e-class pairs with equal c-vecs; common subterms | c-vec mismatch; subsumption | cole-k/cc-lemma [S] | K §1.5 |
| lfind §2.6 | stuck Coq goal | generalise, sketch, synthesise | subterms of the goal; example values | QuickChick; triviality; redundancy | — | 144/222 |
| CVC4 subgoals §2.7 | quantified SMT conjecture | enumeration as splitting lemmas | active terms over the conjecture's variables | ground facts; equivalence | CVC4 | K §1.5 |
| ACL2(ml) §2.8 | ACL2 theorem | mutate an analogous lemma | term-tree matrix; definition clusters | counterexample checker | page named in paper | K §3 |
| Lemmanaid §2.9 | Isabelle theory symbols | LLM template, symbolic filling | symbols, types, definitions | well typed by constr. | anonymised | 50 % / 29 % |
| Cut introduction §3.1 | cut-free proof | extraction by grammar | regularity of instance terms | by constr. | GAPT | K §1.5 |
| Lemma mining §3.2 | HOL Light inference graph | extraction, scoring | uses, dependencies, size, PageRank | already theorems | traces | 21.4 % |
| REFACTOR §3.3 | Metamath proof tree | learned (GNN) | node text; tree edges | connectivity; verifier | jinpz/refactor | 19.6 % |
| ATP to Isar §3.4 | resolution refutation | extraction (redirection) | tainted atoms; disjunctive clause | preplay; merge within 50 % | Isabelle | — |
| kSubS, AdaSubS §4.1 | INT states | learned generator | state text | reachability; learned verifier | subgoal-search | K §1.5 |
| HTPS §4.2 | Metamath, Lean | learned tactic policy | goal tokens | tactic validity | — | K §1.5 |
| Subgoal demonstrations §4.3 | miniF2F, Isabelle | LLM with refinement | statement; informal proof | reachability of each subgoal | HKUNLP | K §1.2 |
| ProD-RL §4.4 | AFP, Isabelle | learned, lemmas in proof | theorem text | proof of the lemma | test sets | 40.8 to 45.5 % |
| Cobblestone §4.5 | Coq | mechanical cut in LLM samples | first error; bullets | Coq run; CoqHammer | Zenodo | K §1.1 |
| BFS-Prover-V2 §4.6 | Lean | LLM `have` list, replan | theorem text; budget exhausted | — | — | case study |
| DSP+ §4.7 | Lean | LLM sketch, masking rules | theorem, draft; syntax errors | syntax | microsoft/DSP-Plus | K §1.5 |
| Why3 §5.1 | VC | fixed transformations | conjunction structure; `by`/`so`; attributes | — | why3.org | — |
| Boogie, Dafny §5.2 | procedure VC | fixed rule, cost search | control-flow graph; path counts; cost squared; assertion positions | split proved sound | Boogie, Dafny | K §1.5 |
| Learned assumptions §5.3 | P of M1 with M2 | learned (L*) | interface alphabet; counterexample traces | model checking | LTSA | case study |
| Bi-abduction §5.4 | program, per procedure | fixed proof rules | call sites; assertion form | forwards re-analysis | Infer [S] | large code bases |
| AutoCorres, crunch §5.5 | C function; monadic invariant | syntax-directed rules; call graph | statement form; callees | generated proof | l4v | [D] |
| Lemur §5.6 | C program, assertion | LLM inside a calculus | verifier answers Unknown; loop heads | verifier | repo | K §1.5 |
| Loopy §5.7 | C loops | LLM candidate set | program text; checker message | Houdini, Frama-C | — | 398/469 |
| Laurel §5.8 | Dafny lemma | LLM; placement by rule | error message; control flow; ProofSim | Dafny | Zenodo | 82/145 |
| AutoVerus §5.9 | Rust with Verus | LLM agents | error class to agent | static filter; Houdini | repo [S] | K §1.5 |
| Cube-and-conquer §6.1 | CNF | lookahead search | product of branch reductions; decisions times assigned | by constr. | march_cc | K §1.5 |
| SMT partitioning §6.2 | SMT query | solver-state heuristics | activity; decision trail; conflict atoms | by constr. | cvc5 | K §1.5 |
| Ganesalingam-Gowers §7.1 | routine analysis problems | fixed priority list | head shape of target or hypothesis | — | — | K §1.5 |
| TLA+ Decompose §7.2 | TLAPS obligation | fixed menu, user picks | top connective; definition body | TLAPS afterwards | Toolbox | — |
| `sketch`, `explore` §7.3 | Isabelle goal | skeleton after a method | none of its own | — | Isabelle | — |
| Aesop §7.4 | Lean goal | registered rules, best-first | index pattern; safety flag; probability | — | repo | — |
| PaMpeR §7.5 | Isabelle proof state | regression trees | 108 boolean assertions | — | data61/PSL | K §4 |
| sem_ind §7.6 | Isabelle inductive goal | 44 written heuristics | goal syntax; constants' definitions | — | data61/PSL | 38.2 % top-1 |
| TacticToe §7.7 | HOL4 goal | k-NN, tree search | constants; type constructors; abstracted subterms | — | HOL4 | K §3 |
| Lean FunInd §7.8 | recursive definition | derived principle | branches and recursive calls | by constr. | Lean | — |

Reading the table. Column (3) sorts the works into three groups: fixed rules and searches name
their features, and the names recur (§9); learned generators take text; verification tools read
the program or the verifier's reply. Column (4) shows a pre-proof check wherever statements are
*invented* (rows §1.3 and §2.1-2.8; in TheSy the check is symbolic) and none where the split is a
sound transformation of the goal (rows §5.1, §7.1-7.4). The learned generators of §4 invent
statements and check them only by attempting the proof, kSubS and AdaSubS excepted.

---

## 9. Goal features that prior automation keys on

**Table 2.** The last column says whether the feature can be computed from the source text of a
statement and its definitions, or needs a running prover.

| Feature | Works that use it | How it is computed | Source text alone, or prover |
|---|---|---|---|
| Top connective and quantifier prefix of the goal | Ganesalingam-Gowers; TLA+ Decompose; Why3 `split_goal`; PSGraph `top_symbol`; PaMpeR; Aesop's index | syntactic, on the parsed statement | source; exposing a connective by expanding a definition needs the prover |
| Shape of a hypothesis: disjunction, existential, conjunction, universal implication | Ganesalingam-Gowers; TLA+ Decompose; Why3 `destruct`, `[@case_split]`; Aesop `cases`, `forward`; Sledgehammer redirection | syntactic | source for stated assumptions; the context inside a proof needs the prover |
| Recursive functions in the goal and their recursion arguments | Bundy 1988; ACL2; sem_ind; Lean FunInd | lookup of the definitions of the goal's constants | source if the definitions are in the corpus; derived induction rules need the prover |
| Type of each variable: inductive datatype or not | PSGraph `inductable`; HipSpec; CVC4; PaMpeR | type-level | prover, or source where binders are annotated |
| `if`, `case` or `match` in the goal or in an unfolded definition | IsaPlanner case analysis; TheSy; Lean FunInd; Laurel's placement | syntactic, after unfolding | source for definitions; the simplified goal needs the prover |
| Difference between hypothesis and conclusion: embedding, wave-fronts, measure | rippling in CLAM and IsaPlanner; PSGraph `hyp_embeds`, `measure_reducible` | comparison of two terms | source when both terms are given (a parent and a child statement); otherwise prover |
| How the last attempt failed: failed precondition, blocked term, error position, error class, budget | critics; Cobblestone; Laurel; AutoVerus; DSP+; BFS-Prover-V2; the sorrifiers of [F §3] | dynamic | prover only |
| Repeated or common subterms | lemma calculation; the generalisation critic; CCLemma; lfind; the Δ-vector of cut introduction | syntactic | source |
| The signature: symbols in scope, their types and definitions | QuickSpec; HipSpec; Hipster; IsaCoSy; TheSy; CVC4; Lemmanaid | set of symbols | source for names; types need the prover or annotations |
| Values on test inputs: equivalence classes, characteristic vectors, symbolic examples | QuickSpec; HipSpec; CCLemma; lfind; TheSy | evaluation | prover, or an executable semantics |
| Known rewrite rules: irreducibility, subsumption | IsaCoSy; QuickSpec; CCLemma; CVC4 | rewriting | prover-side library |
| Program syntax: statement kind, loop heads, call sites, assertion positions, paths | Why3; Boogie; Dafny; AutoCorres; crunch; Lemur; Loopy; bi-abduction | syntax-directed | source with a parser; the VC needs the tool |
| Interface alphabet between components | Cobleigh et al. | set of shared actions | source |
| Proof-graph statistics: uses, dependencies, chain length, PageRank, size | Kaliszyk-Urban; REFACTOR's training signal | graph analysis | proof dependencies from the prover; textual citation approximates them |
| Provenance of a constant: defining theory and defining command | PaMpeR; ACL2 `:induction` rules | lookup | source in most cases |
| Bag of constants, type constructors and abstracted subterms | TacticToe; ACL2(ml) | syntactic | source |
| Raw text, learned representation | kSubS; HTPS; ProD-RL; REFACTOR; Lemmanaid; the LLM planners | learned | source |
| Size and cost counts used to stop splitting | orders in QuickSpec, HipSpec, CVC4; Boogie's cost; the cube cutoff; Sledgehammer preplay; the footprint of [F §10, rule 13] | counting; preplay is timing | source for counts; prover for timing |
| Variable-disjointness of disjuncts | AVATAR [S] | syntactic | source |

Three things follow. First, most named features can be computed from a statement and the
definitions it mentions, and the library holds both: each entry copies its source files whole and
records the parent's and the children's statements. Second, the one class that cannot be computed
from text, the manner of failure, is the one that critics, Laurel, AutoVerus and the mechanical
harnesses of [F] rely on most; the library records decompositions that worked and no failed
attempt in machine-readable form. Third, beyond the bag of constants a goal contains (PaMpeR,
TacticToe), no work found keys on what the statement is *about* (an inequality between sums, a
simulation between two machines). The library's `applicability.goal_shape` texts are written at
that level, in prose. I think this gap is the main risk for the feature extractor: the features
with precedent are shallow, and the ones the library's analysts wrote down are not.

---

## 10. What could be tried on the library

The library as counted on 2026-11-15: 229 entries from 94 sources; 17 move labels with 2 to 23
entries each; 118 Lean, 54 Rocq, 27 Isabelle and 30 non-prover entries; 213 parent statements
and 891 children, of which 848 carry a statement (43 have a null statement with a note). Every
entry is a decomposition that worked, so there are positive examples only. The opinions below are
mine, and each says how sure I am.

1. **A head-symbol rule table as the baseline selector.** Precedent: §7.1, §7.2, §5.1, PSGraph's
   `top_symbol`. Needs: `parent.statement` parsed to its top connective, quantifier prefix and
   hypothesis shapes; the `move` label. Check: a confusion matrix of predicted against labelled
   move, per language; for Isabelle entries the predicted move can be run through `sketch` (§7.3)
   and its children compared with the entry's. Opinion: fairly probable that it separates
   iff-split, extensionality, witness and the disjunctive kind of case-split, and says nothing
   about suffices-or-strengthen, key-invariant or interface-lemma. It is the floor that a learned
   selector has to beat.
2. **Recursion-structure features for induction and per-callee-lemma.** Precedent: §1.1, §1.4,
   §7.6, §7.8, `crunch` [D §1.2]. Needs: the definitions of the parent's constants, from the
   entry's `code/`: whether each is recursive, on which argument, and whether the goal has a
   variable there; for per-callee entries, the callees of the parent's subject. Check: on the 17
   induction entries, whether the suggested variable and scheme are the ones used; on the 16
   per-callee entries, whether the callee set equals the child set. Opinion: more probable than
   not for structural inductions and per-callee lemmas. Some induction entries induct on a
   measure ("s+t", "group order"), which recursion analysis does not suggest.
3. **Parent-child difference features.** Precedent: rippling's embedding (§1.2); common-subterm
   generalisation (§1.3, §2.5, §2.6). Needs: the parent and child statements. Compute by
   anti-unification whether the parent is an instance of a child (generalise-then-instantiate),
   whether a child adds hypotheses to the parent's conclusion (strengthening, invariant), and
   whether a child's conclusion is a subterm of the parent's (extract-have). Check: compare the
   computed relations with the move labels and read the disagreements by hand, since either side
   may be wrong. Opinion: I think this is the most useful of the eight, because it turns labels
   that an analyst assigns into relations that a script computes. More probable than not for
   generalise-then-instantiate; not much better than a guess for key-invariant.
4. **PaMpeR-style assertions with a shallow tree.** Precedent: §7.5, §7.7. Needs: the features of
   candidates 1-3 as booleans, and the labels. Check: leave-one-source-out accuracy against the
   majority class and against candidate 1; the tree's splits read against the `use_when` texts.
   Opinion: 229 entries over 17 labels is small beside PaMpeR's 425,334 points. My guess is that
   a tree of depth two or three rediscovers the head symbol and the recursion features and no
   more, and that the general-purpose labels (calc-chain, suffices) are predicted worst, as
   PaMpeR's result suggests. It is worth having as a description, not as a predictor.
5. **Inlining to manufacture cut-point data.** Precedent: REFACTOR (§3.3); the scores of §3.2.
   Needs: sources that build; a script that inlines a child's proof at its point of use. Check:
   the inlined file must build; a rule or model is asked for the cut, and its answer is compared
   with the original child. Every other cut point in the inlined proof is a negative example,
   which the library lacks. Opinion: inlining is mechanical in Metamath and is not in Isar or
   Lean. My guess is that it works for `have`-level children and single-use lemmas only; one
   source is enough for a trial.
6. **Calibrating the pre-proof counterexample gate.** Precedent: CLAM's disprover (§1.3), the
   filters of §2, [F §10, rule 1]. Needs: the 27 Isabelle entries; mutants of their child
   statements made by dropping one hypothesis or weakening one bound. Check: quickcheck and
   nitpick should find nothing on the true children and something on the mutants; a sample of
   surviving mutants is checked by hand, since some will still be true. Opinion: fairly probable
   that detection is high for statements over numbers and lists and near zero over locales and
   abstract structures; the precedents all work in the first domain.
7. **Granularity proxies.** Precedent: Boogie's squared cost (§5.2); the cube cutoff (§6.1);
   Hipster's two tactics (§2.2); [D §1.5]; [F §10, rule 13]. Needs: `shape.child_lines`,
   `metrics.children_closed_by_automation`, symbol counts of child statements. Check: rank
   correlation of statement size with child proof length, within and across sources. Opinion: I
   expect a weak correlation within a source and none across sources. Hipster's definition is the
   better label where it can be run: a child is trivial if the routine tactic closes it.
8. **Template mining over child statements.** Precedent: Lemmanaid's templates (§2.9);
   QuickSpec's schemas (§2.1); the preservation shape that `crunch` generates. Needs: child
   statements with their non-logical constants replaced by holes. Check: a template counts if it
   recurs in two sources or more (the "known uses" rule of [I §3.1]); then Lemmanaid's test,
   instantiating templates with a held-out source's constants and counting how many results
   exist there. Opinion: more probable than not that interface and per-callee lemmas fall into a
   handful of templates (preservation, monotonicity, commutation); for the mathematics entries I
   have no expectation.

Order: 1, 3 and 2 need only text and should come first; 7 and 8 reuse their parsing; 6 and 5 need
builds. Two cautions apply to all eight. The labels were assigned by a model-driven harvest and
then reviewed, so a disagreement between a computed feature and a label is evidence about both.
And the lesson of §1.3 holds: a rule with a clean applicability condition may apply to almost
nothing, so each rule's coverage on the library should be reported beside its accuracy.

---

## 11. Unverified items and notes on A, B, D, F and I

- **[U]** The four critics in the form of the 1996 JAR paper; how ACL2(ml) picks its source
  lemma; whether the IsaPlanner, ACL2(ml) and GAPT URLs are live; the code locations of TheSy, lfind,
  Loopy, HTPS and Laurel; the venues of Lemur, Aesop and PaMpeR; AutoVerus's repository (from
  [D]'s index, where it is listed under VeruSAGE); the `fun_induction` tactic; all of Ωmega/MULTI,
  IsaScheme, AVATAR and Vampire beyond one sentence each.
- **Numbers.** Each figure was read in the source named and checked against no second source; K
  is the place for them. Laurel's paper gives 145 tasks in one place and 143 in another.
- **No error was found in the parts of [A] and [F] that this survey overlaps.** What follows are
  gaps and matters of scope. (i) [A §0] and [F] omit DSP+, BFS-Prover-V2's planner, ProofCompass,
  Cobblestone, ProD-RL, HyperTree Proof Search and the subgoal-demonstration paper that precedes
  SubgoalXL. (ii) [F §0, finding 2] and [F §9, "Missing in the field", item 1] hold for LLM
  harnesses and not for the field at large: finding 5. (iii) [F §8] lists "Generalise /
  strengthen" as a free move without evidence; mechanical forms exist and have evaluations (§1.3,
  §2.5, §2.6). (iv) [F §9, item 4] names one granularity check that is not an LLM judgement;
  Hipster's routine-tactic filter, Boogie's cost estimate and the cube cutoff are three more.
  (v) [F §9, item 5] finds one no-progress check; IsaCoSy's irreducibility, QuickSpec's pruning
  and CCLemma's subsumption test all reject a lemma that follows from what is known.
- [B §A4] records the success numbers of Sledgehammer's Isar output as unread; they remain so.
  [I §3.2] cites "QED at Large" as arXiv 2003.06458 [S]; the identifier is correct [P]. [D §3]
  describes AutoVerus and Laurel from abstracts or secondary sources; §5.8 and §5.9 agree with it.

## Source index

Web: the URL of each source is given inline at its entry; all were fetched on 2026-11-15. Not
reachable: https://www.research.ed.ac.uk/files/408877/Productive_Use_of_Failure_in_Inductive_Proof.pdf
(403); https://www.dfki.de/web/forschung/projekte-publikationen/publikation/3745 (403);
https://ar5iv.labs.arxiv.org/html/cs/9604101 and https://ar5iv.labs.arxiv.org/html/2009.04826
(conversion failed); https://cseweb.ucsd.edu/~lerner/papers/lfind-oopsla2022.pdf (certificate);
https://lean-lang.org/blog/2024-5-17-functional-induction (redirect). Read in place of a primary
source: https://cs.utexas.edu/~moore/acl2/seminar/2015.02.17-heule/avatar.pdf (slides on AVATAR).
Abstract pages only: https://arxiv.org/abs/2211.15864 (Peano); https://arxiv.org/abs/2507.14335
(ProofCompass); https://arxiv.org/abs/2602.10512 (Sonoda et al.);
https://pldi22.sigplan.org/details/pldi-2022-pldi/7/Diaframe-Automated-Verification-of-Fine-Grained-Concurrent-Programs-in-Iris .

Local: `library/README.md`, `library/INDEX.md` and `library/entries/*/entry.json` (counted by a
script on 2026-11-15); surveys A, B, D, F and I in `docs/research/`.
