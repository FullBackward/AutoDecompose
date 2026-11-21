# From Sorry to QED: Refining LLM Math Proofs via Angelic Execution (MathEye)

| Field | Value |
|---|---|
| Authors, organisation | Yanju Chen, Hanzhi Liu, Ruizhe Qian, Jiaming Shan, Xu Yang, Yufei Ding, Osbert Bastani, Yu Feng. University of California San Diego, University of California Santa Barbara, Pennsylvania State University, University of Pennsylvania |
| Date and version read | 17 November 2026, version 1, marked "A Preprint" |
| Source | arXiv 2611.22103, https://arxiv.org/abs/2611.22103 . The paper gives no link to code |
| Licence of the source | arXiv non-exclusive licence to distribute. A third party cannot redistribute the PDF |
| Files in this folder | `paper.pdf`, `note.md`, `figures/fig2-1-workflow.png` |
| What was read | Full main text (Sections 1 to 9) from the arXiv HTML. Figure 2.1 viewed. Figure 7.3 (bar chart for each benchmark) not viewed; its totals are in the text |
| Read on | 21 November 2026 |

Confidence tags: **[P]** read in the primary source at the place given. **[S]** from a secondary
source. **[U]** not verified. Statements marked "reader's" are the inference of the writer of this
note.

## 1. What the work is

MathEye is a tool for Lean 4. A language model writes a proof that is not correct in all its
parts. MathEye keeps the correct structure and isolates the parts that fail. Then it selects a
small set of mathematical claims, and a person answers "yes" or "no" to each claim. The paper
claims that this procedure completes 28 of 30 graduate examination problems, and that the
selection step removes 55 % of the questions [P, abstract; Section 7]. The evidence is one set of
30 problems, a comparison with five models, and one ablation.

## 2. How it works

The procedure has four stages [P, Section 2, "Framework overview"; Algorithm 1].

1. **Sketch.** A language model (ChatGPT 5.1 Extended Thinking) splits the theorem into lemmas and
   writes a first Lean proof [P, Section 6].
2. **Optimistic check.** Lean examines the proof. When a tactic fails, MathEye replaces the block
   that contains it with `sorry`. `sorry` is the Lean placeholder that closes a goal without a
   proof. If the error stays, MathEye goes up one level in the syntax tree and replaces the larger
   block [P, Section 4.2]. The result is an "angelic proof": Lean accepts the structure, and each
   `sorry` marks one "residual goal". The word "angelic" comes from program analysis. It means
   that the checker assumes the best result for each unknown part.
3. **Residual analysis.** MathEye builds a "proof dependence graph". Each node is a symbol of the
   proof: a hypothesis, a parameter, or a declaration made by `have`, `lemma`, `theorem` or `let`.
   Each edge is a hyperedge: it goes from the set of symbols that a proof fragment refers to, to
   the set of symbols that the fragment derives [P, Definition 5.1]. A hyperedge is necessary
   because one step needs all of its premises together.
   - The graph can be in separate pieces, because a `sorry` hides what a step uses. MathEye adds
     edges with rules that persons wrote. One rule says that a continuously differentiable
     function satisfies the fundamental theorem of calculus. The paper shows nine rules from three
     areas and does not give the total number [P, Section 5.2; Figure 5.3].
   - MathEye writes the graph as logical constraints of five types, and a MaxSAT solver (Z3)
     selects the "minimal residual core". This is the set of open nodes with the lowest cost such
     that the theorem follows when each node in the set is confirmed [P, Section 5.3; Section 6].
4. **Refinement.** MathEye writes each selected node as a question in ordinary mathematical
   notation. If the person confirms the claim, MathEye records it as a "certified assumption" and
   continues [P, Section 4.1; Definition 3.2].

**The cost model.** The cost of a selected set K is the mean, over the nodes of K, of a difficulty
value, plus a penalty in proportion to the size of K. The difficulty value has two parts: a score
between 0 and 1 that a language model estimates, and a measure of the size of the Lean proof state
[P, Section 5.3, "Cost model"]. The paper does not give the values of the three weights.

## 3. How it splits a proof

- **Unit.** A symbol of the proof: a lemma or a `have` step.
- **Who chooses.** The language model chooses the split when it writes the sketch. MathEye does
  not make new lemmas. It selects among the nodes that the sketch contains.
- **Check before work.** There is no check of the split before the proof attempt. The optimistic
  check does the equivalent after the attempt: Lean accepts the structure with `sorry` in place
  of the failed parts.
- **Record.** A directed hypergraph.
- **When a child fails.** The child becomes a residual goal. Then MathEye asks about the child, or
  about a node above it that covers it.

## 4. What it says about scale

- 30 problems. Each proof has "7 to 10 major logical transitions" [P, Section 7.1].
- Questions for each problem: minimum 1, median 5, mean 6.23, maximum 15. Human time for each
  problem: minimum 25 s, median 184 s, mean 191 s, maximum 380 s [P, Table 7.2].
- No figures given for the size of the graphs, the solver time, the tokens of the sketch model,
  or the number of persons who answered.

## 5. Evidence

| Result | Value | Place |
|---|---|---|
| MathEye, problems completed | 28 of 30 (93.3 %) | Table 7.1 |
| Five models together, one attempt each | 6 of 30 (20.0 %) | Table 7.1 |
| Five models together, repair loop with a limit of 20 minutes | 9 of 30 (30.0 %) | Table 7.1; footnote 2 |
| Questions without the graph analysis | 416 | Section 7.5 |
| Questions with the graph analysis | 187 (a reduction of 55 %) | Section 7.5 |
| Largest reductions | 54 to 12 (benchmark 25); 10 to 1 (benchmark 2) | Section 7.5 |

The baselines are DeepSeek-Prover-V2, ChatGPT 5.1 Extended Thinking, ChatGPT 5.4, ChatGPT Codex 5.3
and Claude Opus 4.6. A problem counts for the baselines when one of the five completes it
[P, Section 7.2; Section 7.3].

**The ablation isolates the selection step, not the split.** It compares "ask about each leaf"
with "ask about the selected set". No experiment changes the sketch.

## 6. Limits

Stated by the authors [P, Section 7.6; Section 9]:

- The answers depend on the persons who gave them.
- The set has 30 problems.
- If the first sketch is fully wrong, the procedure cannot recover.
- The cost model does not measure how much a question helps a person to understand the proof.

Found by the reader:

- **A human "yes" is an assumption.** Definition 3.2 permits a "certified assumption supplied by a
  human oracle" in place of a proof. Footnote 1 of Section 7.3 says that the final proof has no
  `sorry`. The text does not say how a confirmed claim becomes a proof that the kernel accepts.
  Thus the 93.3 % is not comparable with the rate of an automatic prover.
- **The formula and the example do not agree.** The example in Section 2 adds the costs: 3 for two
  leaves against 2 for one lemma. The formula in Section 5.3 uses the mean: 1.5 against 2, so the
  two leaves win unless the size penalty is large. The costs in the figure can be on a different
  scale, but the direction of the effect is the same.
- **A superset can cost less.** With a mean, the addition of one easy question to a set makes the
  first term smaller.
- The paper gives no code, no weights, no number of rules and no number of participants.
- The baselines get credit when a model "axiomatizes atomic operations" [P, Section 7.3,
  footnote 1]. This rule favours the baselines, so it does not weaken the comparison.

## 7. Relation to Turing Agent and to earlier work

- **Turing Agent (arXiv 2611.21299), one day earlier.** See the note in
  `../turing-agent-2611.21299/note.md`, Section 7. Neither work cites the other.
- **Replacement of failed parts by `sorry` is older.** APOLLO (arXiv 2505.05758, May 2025) and
  MechMath (arXiv 2603.24465, March 2026) replace failed sub-proofs with `sorry` and work on the
  extracted goals. ProofFlow (arXiv 2510.15981) builds a dependency graph of a proof. MathEye
  cites none of the three (searched in the full text and in its reference list). The notes for
  those works in this folder give the details.
- **What MathEye adds.** The selection of a set of questions by an exact solver on a hypergraph,
  and a person as the oracle.
- **Origin of the method.** The paper names angelic execution, counterexample-guided synthesis and
  abductive inference from program verification as its sources [P, Section 8]. The writer of this
  note did not read those works.

## 8. What this repository can use

All items in this section are the reader's proposals. No test supports them at this time.

- **The selection is a minimum cut in one condition.** If each node has a maximum of one
  derivation, a sufficient set is a set of nodes that every path from an open node to the theorem
  goes through. With costs that add, the max-flow algorithm finds the best set. The library's
  graphs satisfy the condition, because each declaration has one proof.
- **Use a sum, not a mean.** A sum removes the two defects in Section 6.
- **Use a probability as the cost.** Let the cost of a node be the negative logarithm of the
  probability that a prover closes it. Then the best cut is the set with the highest probability
  of a complete proof, if the results are independent.
- **Hyperedges are not necessary for completed proofs.** A plain "uses" arrow is sufficient when
  each node has one derivation. The library's graphs can stay as they are.
- **Make new nodes.** MathEye cannot add a lemma that the sketch does not contain. The library's
  17 moves can propose alternative splits for a node that is too hard.
- **Search for a counterexample before a question.** A false claim costs a question and gives
  nothing.

## 9. Open points and things not read

- How a confirmed claim enters the final Lean proof.
- The sizes of the graphs, and how frequently a rule adds a second derivation to a node.
- Whether the two largest reductions come from a node before the failed steps or after them.
- Figure 7.3 was not viewed. The works on angelic execution and abduction were not read.
