# A Human Audit of OpenAI's AI-Generated Mathematical Proofs

| Field | Value |
|---|---|
| Authors, organisation | Mikołaj Sienicki (Polish-Japanese Academy of Information Technology, Warsaw) and Krzysztof Sienicki (Chair of Theoretical Physics of Naturally Intelligent Systems, Podkowa Leśna) |
| Date and version read | Version 3, 9 September 2026. Version 1 is dated 3 August 2026, version 2 is dated 25 August 2026 (arXiv submission history) |
| Source | arXiv 2608.14673, https://arxiv.org/abs/2608.14673 ; review corpus at DOI 10.5281/zenodo.22218229 |
| Licence of the source | CC BY 4.0 (arXiv page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Full main text (Sections 1 to 8, the closing statements, the reference list) from the arXiv HTML. The Zenodo corpus was not opened |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given. **[S]** the statement comes from a secondary source, which is named. **[U]** the
statement is not verified. A number without a tag is not permitted.

## 1. What the work is

The work is a study of review reports. It is not a system, and it proves nothing new. It asks what
human scrutiny established about ten results that OpenAI announced on 1 August 2026 [P, abstract].
**The audited release is the August release, "Ten Advances in Mathematics and Theoretical Computer
Science". It is not the October release of 721 manuscripts.** The source record has two parts
[P, Section 1]. One is the manuscript of 1 August 2026. The other is the repository
`openai/ten-proofs` at commit 94bc0fe, dated 2 August 2026, with Lean 4.32.0. The authors read 18
chapter reports. They conclude that no
confirmed error in a principal result survives [P, Section 3]. They state that this conclusion is
weaker than "all ten proofs are verified" [P, Section 6].

## 2. How it works

The corpus was examined on 27 August 2026. It holds 23 LaTeX documents: 18 reports on one chapter
each, and 5 protocol documents [P, Section 2.1]. The ten chapters have 2, 2, 2, 1, 3, 1, 2, 2, 1
and 2 reports [P, Table 1].

The authors sort each finding into one of four classes [P, Section 2.2]. A *confirmed mathematical
error* is a false statement, an invalid inference, a violated hypothesis or a reproducible
counterexample. An *unresolved proof gap* is a necessary step without sufficient justification. An
*expository omission* is a missing derivation that a reader can recover. *Verification incomplete*
means that the check was not deep enough for a judgement. The classes matter because "no error
found" and "verified" are different results.

The authors also separate three objects [P, Section 2.2]. T_formal is the proposition that Lean
checks. T_published is the theorem in the manuscript. C_advertised is the achievement that the
announcement claims. Lean compares none of these. A person must compare T_formal with T_published
and must judge C_advertised separately.

## 3. How it splits a proof

The work does not split proofs. It does not examine how the Lean developments are organised. Its
unit is the chapter of the OpenAI manuscript. One chapter holds one result.

## 4. What it says about scale

No figures are given for lines, lemmas, files, agents, cost or build time. The article makes two
statements about the Lean artefact [P, Section 1]. The repository metadata list a `sorry_count` of
zero for the ten principal results. Comparator challenge files hold `sorry` placeholders on
purpose. Human effort appears only as document counts. The authors say that 18 documents
are not 18 independent reviewers [P, Section 6].

## 5. Evidence

| Result | Place |
|---|---|
| 23 documents, of which 18 are chapter reports | Section 2.1 |
| No confirmed substantive error in a principal result | Section 3 |
| Chapter 8: two reports, one recommends major revision; status "verification incomplete" | Section 3.2 |
| Chapter 6: an objection to a conditioning lemma was withdrawn | Section 3.1 |
| Chapter 7: a later paper improves n^(1/400) to n^(1/8-ε) and n^(1/200) to n^(1/4-ε) | Section 4.4 |

There is no baseline and no ablation, because the work is not an experiment. The Chapter 6 case
carries the most information. A reviewer read the proof from text that a PDF extraction tool
produced. The tool dropped an overbar, so a failure probability became a success probability. The
objection was correct for the changed formula and wrong for the manuscript [P, Section 3.1].
Version 2 of this arXiv entry had the title "Auditing an AI-generated mathematical proof: Human
assessment of OpenAI's quantum parallel-repetition argument" [P, reference list]. Version 3 is
therefore a wider paper under the same identifier.

## 6. Limits

Limits that the authors state:

- The authors organised the review project and wrote the Chapter 6 audit. They are "not
  independent of the corpus" [P, "Author involvement and conflicts of interest"].
- Generative AI assisted the writing and checking of the article [P, "AI assistance and
  responsibility"].
- Chapters 4, 6 and 9 have one report each [P, Table 1].
- The reviewer form is dated 15 August 2026, after some reports were written [P, Section 2.1].

Limits that the reader found:

- The article names the comparison of T_formal with T_published as a task. It shows no result of
  that comparison for any of the ten Lean statements.
- The article gives no data for each report (reviewer, hours, depth).

## 7. Relation to the two anchors

**Turing Agent (arXiv 2611.21299).** The audit is earlier by about ten weeks. Turing Agent
formalises three problems that an earlier system left unverified. The audit concerns ten other
problems, which OpenAI formalised itself. The two works share one concern: a Lean proof is only as
good as its statement. Turing Agent measures this as "faithful statements" on Formal TCS Bench. The
audit names it "semantic correspondence" and leaves it to people. Turing Agent does not cite the
audit (checked in `refs_2611.21299.json`).

**MathEye (arXiv 2611.22103).** MathEye asks a person yes or no questions about open obligations.
The audit shows how such a human check can fail: the person judged a formula that the tool chain
had changed. MathEye does not cite the audit (checked in `refs_2611.22103.json`).

The audit cites no proof-decomposition work and not Prove2Me. Its references are OpenAI sources,
follow-up mathematics papers, MathWorld pages and the Lean 4 system paper.

## 8. What this repository can use

- **Check the typeset source before a claim enters a note or an entry.** The Chapter 6 case shows
  that text extraction can change a formula. This repository reads papers through HTML-to-text and
  PDF-to-text tools.
- **Use the four classes as review verdicts.** The library's verification step can record
  "verification incomplete" as a value different from "no error found", because the two values
  lead to different next actions.
- **Record three statements for each decomposition:** the formal child statements, the informal
  statements, and the claim made about the split. A split can be correct in Lean and still not
  match the informal plan.

## 9. Open points and things not read

- The 18 reports on Zenodo were not read. The depth of each report is not known to this note.
- Commit 94bc0fe was not opened. The GitHub API gives 5 August 2026 as the creation date of
  `openai/ten-proofs` [P, api.github.com/repos/openai/ten-proofs, field `created_at`], three days
  after the commit date in the paper. The reason is not known [U].
- No audit of the October release by these authors was found in a web search on 21 November 2026
  [U].
