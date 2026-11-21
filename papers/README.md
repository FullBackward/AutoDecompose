# Papers: survey M

Survey M reads 28 works around two anchor papers of November 2026: Turing Agent and MathEye. It
has three subjects: what the works add to the ideas of the anchors, what companies contribute,
and the scaling problem that Prove2Me names.

- **Results:** `survey-M-results-2026-11-21.md`.
- **Form of a note:** `NOTE_TEMPLATE.md` (a header table and nine sections).
- **One folder for each work.** A folder holds `note.md` and the source: `paper.pdf` for a paper,
  `source.pdf` for web pages printed to PDF. Some folders hold figures or data.
- **The PDFs are not in git.** `.gitignore` has the line `papers/**/*.pdf`, because the licences
  differ. The table gives the licence of each source. Each note gives the address of its source,
  so a reader can download the PDF again.

## How the notes were made and checked

The two anchors and the 2012 paper were read by the writer of the results. Four agents read the
other 25 works on 21 November 2026. The writer then compared approximately 110 figures and
quotations from those 25 notes with the saved sources; all agree. Each note says what was read
and what was not read. Each figure in a note has a tag: [P] read in the primary source at the
place given, [S] from a secondary source, [U] not verified.

## Index

### Anchors

| Folder | Work | Date | Licence of the source |
|---|---|---|---|
| `turing-agent-2611.21299` | Turing Agent: Agentic Formal Verification for Mathematical Research. Also `traces/`: measures from the proof graphs on the project page | 16 Nov 2026 | CC BY 4.0 |
| `matheye-2611.22103` | From Sorry to QED: Refining LLM Math Proofs via Angelic Execution (MathEye) | 17 Nov 2026 | arXiv non-exclusive; no redistribution |

### Agent harnesses for research mathematics (the lane of Turing Agent)

| Folder | Work | Date | Licence of the source |
|---|---|---|---|
| `theo-beyond-the-library-2606.31134` | Beyond the Library (Theo) | 30 Jun 2026 | CC BY 4.0 |
| `aiprover-2610.05367` | AIProver: certificate-driven evolving harness | 4 Oct 2026 | arXiv non-exclusive; no redistribution |
| `archon-rethlas-2604.03789` | Automated Conjecture Resolution with Formal Verification (Rethlas and Archon) | 4 Apr 2026 | CC BY 4.0 |
| `lea-2611.08849` | Lea: An Agent Backbone for Mathematician-Controlled Formalization in Lean | 6 Nov 2026 | CC BY 4.0 |
| `numina-fuse-2610.33860` | Numina Fuse: Interactive Autoformalization in Lean 4 | 24 Oct 2026 | CC BY 4.0 |
| `leanmarathon-2606.05400` | LeanMarathon: Long-Horizon Lean Autoformalization | 3 Jun 2026 | CC BY 4.0 |

### Dependency graphs and repair with `sorry` (the lane of MathEye)

| Folder | Work | Date | Licence of the source |
|---|---|---|---|
| `apollo-2505.05758` | APOLLO: Automated LLM and Lean Collaboration | 9 May 2025 | CC BY 4.0 |
| `mechmath-2603.24465` | MechMath: Sorrifier-Driven Formal Decomposition Workflow | 25 Mar 2026 | CC BY 4.0 |
| `proofflow-2510.15981` | ProofFlow: A Dependency Graph Approach to Faithful Proof Autoformalization | 13 Oct 2025 | CC BY 4.0 |
| `dependency-graphs-of-arguments-2610.36776` | Dependency Graphs of Mathematical Arguments | 27 Oct 2026 | CC BY 4.0 |
| `network-structure-of-mathlib-2604.24797` | The Network Structure of Mathlib | 26 Apr 2026 | CC BY 4.0 |
| `agents-diverge-from-human-preferences-2611.06995` | Autonomous AI Agents Systematically Diverge From Human Preferences in Proof Formalization | 4 Nov 2026 | CC BY 4.0 |
| `abductive-error-diagnosis-pldi2012` | Automated Error Diagnosis Using Abductive Inference (the source of MathEye's selection method) | Jun 2012 | Copyright ACM; no redistribution |

### The scaling problem

| Folder | Work | Date | Licence of the source |
|---|---|---|---|
| `prove2me-2608.28433` | Prove2Me: An Open Collaborative Platform for Scaling Math Formalization, with the public pages and repositories | 28 Aug 2026 | Paper: arXiv non-exclusive; no redistribution. Corpus: Apache 2.0 |
| `automatic-textbook-formalization-2604.03071` | Automatic Textbook Formalization (Gloeckle et al.) | 3 Apr 2026 | CC BY 4.0 |
| `mip-star-re-long-horizon-2609.19814` | Long-horizon autoformalization of a core theorem underlying MIP* = RE | 17 Sep 2026 | arXiv non-exclusive; no redistribution |
| `m2f-2602.17016` | M2F: Automated Formalization of Mathematical Literature at Scale | 19 Feb 2026 | CC BY 4.0 |
| `lean-module-system` | The Lean module system and the rebuild of dependent files (reference manual, talk, discussion thread, pull request) | 2025 to 2026 | Not stated on the pages |
| `proof-change-isolation-rocq-isabelle` | How Rocq and Isabelle isolate a change in a proof (official documentation) | Rocq 9.3.0; Isabelle2026 | Not stated on the pages |

### Companies and company releases

| Folder | Work | Date | Licence of the source |
|---|---|---|---|
| `openai-math-release-2026-10` | OpenAI mathematics release (`openai/math`) | 6 Oct 2026; read at 29 Oct 2026 | Apache 2.0 |
| `human-audit-openai-proofs-2608.14673` | A Human Audit of OpenAI's AI-Generated Mathematical Proofs (the release of August 2026) | 3 Aug 2026 | CC BY 4.0 |
| `from-solvers-to-research-2607.07779` | From Solvers to Research (survey, 41 authors) | 8 Jul 2026 | CC BY 4.0 |
| `axiom-math` | Axiom Math: the classification of finite simple groups and the Stacks Project in Lean (posts and repositories) | Oct to Nov 2026 | Posts: copyright Axiom Math. Repositories: Apache 2.0 |
| `deepmind-aletheia-alphaproof` | Google DeepMind: AlphaProof Nexus, with a comparison to Aletheia | May 2026 | CC BY-NC-ND 4.0 |
| `mathinc-gauss` | Math Inc: "Abstraction considered helpful" and the sphere-packing report | Read 21 Nov 2026 | Not stated on the pages |
| `lean-pool-2609.25199` | Lean Pool: An AI-Maintained Archive of Formalized Mathematics | 21 Sep 2026 | CC BY 4.0 |

The dates are those of the first version. Each note gives the version that was read.
