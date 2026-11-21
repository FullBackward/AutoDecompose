# <Title of the work>

| Field | Value |
|---|---|
| Authors, organisation | |
| Date and version read | |
| Source | arXiv id and URL; code or project URL if one exists |
| Licence of the source | as stated on the source page |
| Files in this folder | `paper.pdf`, `note.md`, figures if any |
| What was read | for example: full main text; appendix B searched; figures 2 and 6 viewed |
| Read on | date |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

## 1. What the work is

Three to six sentences in Simplified Technical English: short, active, present tense, one idea in
each sentence. Say what the system or study is, what it claims, and what evidence it gives.

## 2. How it works

The mechanism, step by step. Define each technical term in a full sentence when it first occurs.
Say why each step exists. Give one example from the work where one exists.

## 3. How it splits a proof

- The unit of a split (tactic step, `have` step, lemma, file, statement card).
- Who chooses the split (a person, a model, a rule) and from what input.
- The check that a split is correct before work starts on the children, if there is one.
- The record of the split (tree, directed acyclic graph, hypergraph, none).
- What the system does when a child fails.

Write "the work does not split proofs" if that is the case.

## 4. What it says about scale

Size of the developments (lines, lemmas, files), number of agents, parallel work, cost in money,
tokens or time, rebuild time, merge conflicts, human hours. Write "no figures given" where the
work gives none.

## 5. Evidence

A table of the main results, each with its place in the source. Name the baselines. Say plainly
whether an ablation isolates the effect of the split, and what it shows.

## 6. Limits

First the limits that the authors state. Then the limits that the reader found, marked as the
reader's.

## 7. Relation to the two anchors

Turing Agent (arXiv 2611.21299) and MathEye (arXiv 2611.22103). For each: what is the same, what
is different, and which work came first. Say whether the anchor cites this work.

## 8. What this repository can use

Ideas for the decomposition library, the feature graphs, or the proposed algorithm. One idea in
each bullet, with the reason.

## 9. Open points and things not read

Questions the work leaves open. Parts of the source that were not read.
