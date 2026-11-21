# Automated Error Diagnosis Using Abductive Inference

| Field | Value |
|---|---|
| Authors, organisation | Isil Dillig and Thomas Dillig (College of William & Mary), Alex Aiken (Stanford University) |
| Date and version read | PLDI 2012, 11 to 16 June 2012; the copy on the first author's page |
| Source | https://www.cs.utexas.edu/~isil/pldi022-dillig.pdf ; DOI 10.1145/2254064.2254087 |
| Licence of the source | Copyright ACM 2012. A third party cannot redistribute the PDF |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Sections 1 (start), 4, 5 and 6 (start), from text that `pypdf` extracted. Sections 2, 3, 7 and 8 not read |
| Read on | 21 November 2026 |

Confidence tags: **[P]** read in the primary source at the place given. **[S]** from a secondary
source. **[U]** not verified. Statements marked "reader's" are the inference of the writer of this
note.

This note is in the survey because MathEye names abductive inference as a source of its method
[P, MathEye Section 8], and its reference list contains this paper. The work is about programs,
not about proofs of mathematics.

## 1. What the work is

A program verifier can fail to decide if a program is correct. Then a person must decide if the
error report is a real error or a false alarm. This work computes a short question for that
person. A "yes" answer gives a definite result. The work claims that the questions increase the
proportion of correct decisions from 33 % to 90 %, and decrease the time from approximately 5
minutes to less than 1 minute [P, abstract]. The evidence is a study with 49 programmers and 11
problems.

## 2. How it works

- **The abduction problem.** The verifier knows facts I about the program. It must prove a
  condition φ. Abduction is the search for a missing fact Γ such that Γ together with I implies
  φ, and Γ does not contradict I [P, Definition 1]. The paper calls Γ a "proof obligation".
- **The trivial answer.** Γ = φ is always a solution: the tool asks the person to prove the full
  condition [P, Section 4.1]. A useful solution must be simpler than that. MathEye has the same
  property: the theorem itself is always a sufficient set.
- **Cost.** The cost of a fact is the sum of the costs of the variables in it. A variable that
  stands for a local loss of precision has cost 1. A variable that stands for a program input has
  a large cost [P, Definition 2]. The reason: a local fact is easier for a person to decide.
- **Weakest minimum.** The tool finds a fact of minimum cost. Among the facts of minimum cost, it
  selects one that is not stronger than the others [P, Definition 3]. The reason: the tool must
  not ask the person to confirm more than is necessary.
- **The dual question.** The tool also computes a "failure witness": a fact that, if it can occur
  in one execution, proves a real error [P, Definition 8]. In each round the tool asks the
  cheaper of the two questions [P, Figure 6, line 9].
- **Each answer gives information.** A "no" to a proof obligation becomes a known witness. A "no"
  to a witness becomes a known invariant. The tool computes the next question with this new
  information [P, Section 4.3].
- **"I do not know"** is a permitted answer [P, Section 5].

## 3. How it splits a proof

The work does not split proofs. It splits a question: an invariant question becomes one question
for each conjunct, and a witness question becomes one question for each disjunct
[P, Section 4.4].

## 4. What it says about scale

The problems have 66 to 363 lines of code and one assertion each. A problem needs 1 to 3
questions. The time to compute a question is less than 0.1 s [P, Section 6]. No figures given
for larger programs.

## 5. Evidence

| Measure | By hand | With the questions | Place |
|---|---|---|---|
| Correct decisions, mean of 11 problems | 32.9 % | 89.6 % | Figure 7 |
| Wrong decisions | 51.1 % | 7.3 % | Figure 7 |
| "I do not know" | 16.0 % | 2.3 % | Figure 7 |
| Mean time for one problem | 293 s | 55 s | Figure 7 |

The study recruited 56 programmers and kept 49, after three test questions removed 7
[P, Section 6]. Each person did approximately half of the problems by hand and half with the
questions.

## 6. Limits

Stated by the authors: the tool does not examine the answer of the person. A wrong "yes" gives a
wrong result [P, Section 4.1.2, last paragraph]. The cost function is an approximation of human
effort [P, Section 4.1].

Found by the reader: with the questions, 7.3 % of the decisions are still wrong. Thus a person's
"yes" is not a proof.

## 7. Relation to the two anchors

- **MathEye** uses the same pattern 14 years later: find the missing facts, give each a cost, ask
  a person the cheapest sufficient question, and accept "yes". MathEye cites this work.
  Three differences are important.
  1. This work adds the costs. MathEye uses a mean (see the MathEye note, Section 6).
  2. This work asks the dual question, which can show that the goal is false. MathEye asks only
     for confirmation.
  3. This work reports how frequently the persons are wrong. MathEye does not.
- **Turing Agent** has no relation to this work and does not cite it.

## 8. What this repository can use

- **A question that can refute.** For each open lemma, the cheapest test that shows the lemma is
  false has the same value as a proof attempt. A counterexample search is the proof-assistant
  form of the failure witness.
- **The weakest sufficient child.** A split must not ask for more than the parent needs. This is
  the same point as the check that each child is necessary (see the Turing Agent note,
  Section 8).
- **Use each failure.** A failed child is information. It must change the next split, and not
  only start a new attempt.
- **Measure the error rate of the oracle.** If a person or a model confirms a claim, the
  experiment must report how frequently the confirmation is wrong.

## 9. Open points and things not read

Sections 2, 3, 7 and 8 were not read. The algorithm for a minimum satisfying assignment is in a
different paper, reference [3] of this work, which was not read.
