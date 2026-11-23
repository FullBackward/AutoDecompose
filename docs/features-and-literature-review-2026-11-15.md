# Review of surveys J and K and of the two feature extractors (2026-11-15)

Five agents worked on 2026-11-15: two wrote literature surveys, two wrote feature extractors over
the 229 entries of `library/`, and one filled a gap between the surveys. This note is the review
of that work by the session that commissioned it. Section 1 gives the verdict, Section 2 the
method and its limits, Sections 3 and 4 the surveys and the extractors, Section 5 sets the
features that were built against the features the literature has evidence for, Section 6 lists
what the work found wrong in the library itself, and Section 7 says what I think should come next.
Opinions are marked as such.

## 1. Verdict

1. **The surveys can be relied on for what they cite.** The 69 arXiv identifiers of the two first
   drafts all resolve to the papers named, and about 90 quoted sentences and numbers from 21
   papers match the sources. I found no invented citation and no wrong number. Four one-line
   summaries in J overstated a result or hid a baseline and are corrected (Section 3).
2. **The extractors are reproducible.** Each gives identical bytes under three hash seeds and from
   a second working directory, uses the standard library only, and has a `--check` mode that fails
   on any difference.
3. **One defect was found in an extractor and fixed.** The count of children cited by the glue
   missed a lemma used through Lean dot notation (`foo.2`, `foo.mp`), in 8 entries.
4. **The extracted features are syntactic.** No prover was available, so an edge is a token that
   names a declaration and a detector is a token pattern. Both documents say so.
5. **The agreement between code detectors and move labels is an in-sample figure.** The detectors
   were tuned on this corpus and on the audited samples.
6. **The features with the strongest evidence in the literature are not built yet** (Section 5).
7. **The work exposed faults in the library's own checks and entries** (Section 6). None was
   changed.

## 2. Method, and what was not checked

**Surveys.** (i) All arXiv identifiers of the first drafts were looked up through the arXiv API
and the returned title and authors compared with the citation. (ii) For 21 papers I downloaded
the HTML and searched it for the quoted sentences and numbers: 9 papers for J, 10 for K's first
draft, and 6 for the section added afterwards, 4 of which were among J's 9. (iii) J's pointers to
K were checked mechanically. (iv) J's counts of the library were recomputed.

**Extractors.** (i) Each was rerun with `PYTHONHASHSEED` 3, 99 and 5, the last from another
directory, and the SHA-256 of the output compared. (ii) The output format was checked: LF only,
229 records, ids equal to the entry directories, sorted keys, no absolute path or timestamp. (iii)
The table of detectors against labels was recomputed from the output alone. (iv) Six entries,
chosen at fixed positions (3/7 and 5/7 of each language's sorted ids), had their parsed parent
statement compared with the source. (v) One Lean entry had every edge out of its parent compared
with the file, and five more had citation counts compared with an independent word count. (vi)
The two extractors were compared with each other and with `glue_check` of `validate_entry.py`.

**Not checked.** Sources that exist only as PDF (Bundy 1988, Johansson's thesis, Blanchette et al.
2015 and about 25 others) were read by the agents from converted text and not by me. The agents'
hand audits were not repeated; their counts are reported as theirs. `terms.md` is 1,515 lines, of
which I read the definitions I tested and the headings of the rest. The T2 designs in both feature
documents describe tools from memory and are marked unverified by their authors.

## 3. The surveys

**J, mechanisms** (`docs/research/survey-J-decomposition-automation-2026-11-15.md`, 725 lines, 44
entries in seven families). Its finding of most use here is Table 2: the goal features that
symbolic automation keys on are few and syntactic (top connective, quantifier prefix, the
recursive functions in the goal and their recursion arguments, an `if` or `case`, the difference
between hypothesis and conclusion), and most can be computed from source text. Its warning is that
no work it read keys on what a statement is about beyond its bag of constants, which is the level
at which the library's `applicability.goal_shape` texts are written.

**K, experiments** (`docs/research/survey-K-decomposition-experiments-2026-11-15.md`, 837 lines).
Three findings bear on the plan. No study predicts a lemma-level move from the statement; the
nearest, PaMpeR, needs the prover and puts `induct` in its top five 27 % of the time. No corpus of
proof moves reports whether annotators agree, and the library's labels have not been re-labelled
blind. The one direct test of a human decomposition handed to a fixed model gave opposite signs
on two sets of 100 theorems.

**The gap between them.** J left the numbers of its works to K, and K, written in parallel,
satisfied 6 of J's 29 pointers. A wrap-up agent read the evaluation of each of the 25 uncovered
works and added K §1.5 with Table A2; J now points at K by section. The addition changed the
picture in two places. ProD-RL, which J reported as "40.8 % to 45.5 %", has a fine-tuned arm
without lemma proposal at 43.4 %: under supervised training, proposing lemmas lowers the pass
rate, and the gain of the method over that arm is 2.1 points in distribution and 0.1 out of it.
And per-proposal rejection rates, which K had said were unreported, are reported by symbolic and
verification tools (lfind, Lemmanaid, kSubS, AutoVerus), though by no LLM prover.

**Corrections made in review.** J: the count of child statements (848 of 891 children carry one);
four one-line effects that overstated a result or hid a baseline (Lemmanaid, cut introduction,
ProD-RL, BFS-Prover-V2). K: an author's name; three sentences that the new section qualifies
(§1.4, and gaps 4 and 9 of §5).

**What remains weak.** By the agents' own account: several of J's families rest on one or two
papers (assume-guarantee on one paper of 2003; cut introduction on the 2014 paper alone); J's
findings 9, 10 and 12 are claims of absence over a sampled literature or rest on abstracts; K's
finding 9 joins results from four different tasks; DSP+'s ablation figures were read from rendered
images. K §8 lists places where surveys D, E, F and H are too narrow or out of date; those surveys
have not been amended.

## 4. The extractors

| | `feature_graph.py` | `feature_terms.py` |
|---|---|---|
| Output | `graphs.jsonl`: 4,316 nodes, 10,511 edges over 199 entries; `graph-features.jsonl`: 94 features | `term-features.jsonl`: statement skeletons, relations, proof steps, 14 detectors, 138 flat features |
| Self-test | 52 cases | 103 cases (6 added in review) |
| Agent's audit | frozen test sample, 265 edges: none wrong, 10 missed; recall is an upper bound | two samples of 12: 11 of 12 skeletons right in each; both samples were then used for fixing |
| Reviewer's check | every parent edge of one Lean entry right; an Isabelle fact and a constant of the same name kept apart | 5 of 5 parsed statements right in my sample; detector table reproduced |

**The defect.** `d_glue_children_cited` compared the last dotted component of each identifier
with the child's name, so `G_imag_axis_pos.2` was read as `2`. The matcher now asks whether the
name is a whole dotted component. Agreement with the validator's count rose from 185 to 193 of 195
entries; the two left differ by definition. The extractor is at version 1.0.1.

**The two tools agree where they overlap.** They compute the same input digest for all 229
entries without sharing code. Their counts of cited children agree on 195 of 198 entries; the
three differences, and the validator's, are definitions and are set out in
`library/features/README.md`.

**What the detectors show.** Moves named after a tactic can be read off the code: induction 17 of
17 labelled entries, case-split 16 of 16, witness 13 of 15, calc-chain 16 of 22, iff-split 9 of
12. Moves that are a relation between statements cannot: suffices-or-strengthen 8 of 19,
generalise-then-instantiate 2 of 14, interface-lemma 0 of 16, and key-invariant has no detector.
A detector firing is weak evidence of the move: case-split fires on 62 entries labelled otherwise.
On the goal side, a parent whose core is an iff is labelled iff-split in 9 of 13 cases and one
whose core is an existential is labelled witness in 12 of 33; binder and hypothesis counts are
flat across moves.

## 5. Features built against features with precedent

K §6 lists 23 features that prior work computed and tested; J's Table 2 lists those that symbolic
automation keys on. The comparison below is mine.

| Feature with precedent | Evidence (K §6 row; J) | Built here |
|---|---|---|
| Top connective, quantifier prefix, head symbol | row 7; J Table 2 | yes (`g_concl_class`, `g_core_class`, `g_core_head`, `g_quant_prefix`) |
| Premise and hypothesis counts, clause-like shape | row 9 | yes, approximately; whether a binder is a hypothesis is a T2 question |
| Bag of constants | row 1 | yes, unweighted; rarity weights are a later computation over the corpus |
| Text size | row 11 | yes |
| Proof-style counts, per-step tactic table | rows 13, 14 | yes (head classes and sequences per site) |
| Position in the dependency graph: users, dependencies, depth | row 16 | yes, inside the copied files only |
| Statement-level against proof-level references | row 17 | yes (each edge records statement and body counts) |
| Pairwise symbol overlap | row 18 | yes (`d_jaccard_*`, `stmt_dep_jaccard`) |
| Subterm patterns with variables abstracted; walks in the term tree; depth-by-arity matrix; formula graph | rows 2, 3, 15, 19: the largest measured effects | **no**: the parser stops at connectives and relations, and what lies below is one leaf |
| Recursive functions in the goal and their recursion arguments | row 8; J §1.1, §1.4, §7.6 | **partly**: graph nodes carry a `recursive` flag; the argument position is not analysed |
| Difference between two statements by anti-unification | J §1.2, §10 candidate 3 | **no**: exact-match traces only, which explains the 2 of 14 for generalise |
| Types, type classes | row 4 | no; T2 |
| Similarity retrieval (BM25 over statements or proofs) | row 20 | no; computable later from the stored tokens |

## 6. Faults found in the library itself

Nothing in this section was changed.

1. **`glue_check` can pass on weak evidence.** It searches raw site text, so a child counts as
   cited by its own declaration inside the parent site, by its own `have` line, or by a comment.
   In `lean-interface-lemma-carleson-50fa619f` all eleven children pass this way; in two entries a
   child `have` step is never mentioned again.
2. **Labels.** Two entries labelled iff-split have a parent that is not an iff
   (`lean-iff-split-numina-putnam2025-95670702`, `isabelle-iff-split-munkres-isabelle-05cdf9d1`).
   Appendix G7 of `terms.md` lists every entry where detector and label disagree.
3. **Entry structure.** Five parents are not named by a declaration identifier; three entries have
   child sites that no child names; 25 parent sites and 63 child sites are not exactly one
   declaration, so `shape.glue_lines` and `shape.child_lines` are site lengths.
4. **Tools.** `strip_comments` does not handle nested Lean block comments or comment markers in
   strings; it feeds the sorry scan (no site is affected today) and `normalised_hash`, hence the
   content keys (effect not measured). `statements.DECL["lean"]` lacks `problem`.
5. **Line endings.** `entry.json` is not protected in `.gitattributes`, so a hash of its raw bytes
   depends on the checkout. Both extractors work around this.

## 7. What I think should come next

These are opinions, in the order I would take them.

1. **Re-label the moves blind before treating them as ground truth.** Every later use of the
   labels rests on them, and no agreement figure exists here or, by K §4, anywhere. The list in G7
   gives the first entries to look at. It is fairly probable that some labels change.
2. **Test the extractors on entries they have not seen.** A later harvest, run through both tools
   unchanged, gives the first fair figure for the detectors.
3. **Parse below the connectives.** Subterm patterns and term walks have the best evidence and
   need a term parser for the inner syntax of three provers. My guess is that this is the largest
   piece of work on the list.
4. **Use the graph for the relational moves.** Per-callee-lemma and interface-lemma have no
   syntactic signature in a proof, and the graph holds what would define them: the callees of the
   parent's subject against the child set, and the users of each child.
5. **Measure T1 against the prover on a small subset.** Installing one toolchain and building a
   few sources would turn the sampled precision and recall of the edges into a measured one. This
   needs the owner's decision.
6. **Decide the faults of Section 6.** Tightening `glue_check` changes a gate and so needs a dated
   protocol amendment.
