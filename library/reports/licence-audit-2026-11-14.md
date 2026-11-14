# Licence audit, 2026-11-14

Every one of the library's 106 sources now records a licence read by a person from its evidence;
none rests on the detector alone. The audit changed the licence of 15 sources and 28 entries.
12 sources remain `LicenseRef-unknown`, because nothing in them grants a licence. Section 1 says
how the licences were read, Sections 2 to 4 what was wrong, Section 5 what the library contains
for publication, and Section 6 what was changed so that the next registration does not repeat
the mistakes. The appendix lists every source.

## 1. Method

Three things were read for each source:

(i) each copied licence file, in full where it was not a standard text, against the licence the
detector named;
(ii) the licence lines in the header of every file copied into an entry, against the entry's
recorded licence;
(iii) for each source without a recognised licence, the whole file tree for licence-like names,
the README for a licence statement, and the project's own metadata (the AFP's
`metadata/entries/*.toml`).

Corrections go through `register_source.py --set-licence`. It keeps the detector's value as
`licence_detected`, records the evidence as `licence_note`, and appends an event to
`ledger/sources.jsonl`. Each changed entry carries a `provenance_log` record. No file under
`code/` was touched. The verifiers' review records were not re-run: they stand as written,
and the change records sit beside them.

## 2. Sources corrected

The detector made four kinds of mistake.

**It took the first match for the whole.**
- l4v named the CC-BY-SA tag of `LICENSE.md` itself.
- jormungand and cogent each vendor GPL-2.0 trees.
- compcert dual-licenses `lib/` and `common/` under LGPL-2.1-or-later and ships flocq under
  LGPL-3.0-or-later.
- vst holds INRIA-licensed `compcert/` directories.

These now carry per-file expressions:
- l4v: `GPL-2.0-only AND BSD-2-Clause`
- jormungand: `BSD-2-Clause AND GPL-2.0-only`
- cogent: `BSD-2-Clause AND GPL-2.0-only`
- compcert: `LicenseRef-INRIA-Non-Commercial AND (LicenseRef-INRIA-Non-Commercial OR LGPL-2.1-or-later) AND LGPL-3.0-or-later AND BSD-3-Clause`
- vst: `BSD-2-Clause AND (LicenseRef-INRIA-Non-Commercial OR LGPL-2.1-or-later) AND LicenseRef-INRIA-Non-Commercial`
- wasmcert-coq: `MIT AND LGPL-2.1-or-later`, corrected earlier.

**It joined a choice with AND.** fiat-crypto (corrected earlier) and con-nf offer their
licences as alternatives. con-nf is `(Apache-2.0 OR MIT) AND LicenseRef-all-rights-reserved`,
the second covering only `Old/`, which its README says is under no open-source licence.

**It could not tell "only" from "or later".** A GNU licence text does not say which. The file
headers do:
- corn: `GPL-2.0-or-later`
- bertrand: `LGPL-2.1-or-later`
- topology: `LGPL-2.1-or-later`
- rocq-stdlib: `LGPL-2.1-only`
- isabelle-pide-ai: `LGPL-3.0-only`, since nothing in the repository says "or later".

**It misnamed or missed a text.**
- fiat-crypto's BSD-1 file was read as BSD-2 (corrected earlier).
- UniMath's licence was read as MIT. It is the MIT grant without MIT's warranty disclaimer, so
  it is now `LicenseRef-UniMath`.
- Apple's licence in ml-hilbert was missed. It is SPDX `AML` word for word, apart from the
  copyright line.
- The DeepSeek Licence Agreement in deepseek-prover-v2 was missed. It is now
  `LicenseRef-DeepSeek-License-1.0`; it covers documentation as "Complementary Material" and
  restricts use of the model.

**Four unknown sources state a licence elsewhere:**
- afp: each AFP entry names its licence in `metadata/entries/<entry>.toml`. The AFP's BSD
  text, published at isa-afp.org and now copied with `--licence-url`, has the "Neither the name"
  clause. The source is `BSD-3-Clause AND LGPL-2.1-only`.
- numina-lean-agent: its README says "MIT License".
- goedel-prover-v2: its README carries an Apache 2.0 badge.

Neither of these last two ships a licence text, and the source notes say so.

Two sources were read and kept, with licence files added:
- flt-anthropic: `ATTRIBUTION.md`, which carries the per-file notices for its FLT, flt-regular
  and Mathlib material.
- humanfia-hoa-qed: QuAIR's `lean-qit-qlg/QIT/LICENSE`.

## 3. Entries corrected

28 entries changed licence. 13 are accepted and 15 draft. Each entry now records the licence of
the files it copies, which may be narrower than its source's:
- the five AFP entries: `BSD-3-Clause`, since all four AFP entries they use are marked "bsd";
- the two cogent entries: `GPL-2.0-only`;
- the two humanfia entries: `Apache-2.0` (Lean files), not `Apache-2.0 AND CC-BY-4.0`;
- con-nf: `Apache-2.0 OR MIT`;
- compcert `6decbbae`: non-commercial for `backend/Inliningproof.v` and dual for
  `common/Smallstep.v`;
- the rest follow their source: corn, bertrand, topology, rocq-stdlib (3), unimath (3),
  ml-hilbert (2), deepseek-prover-v2, numina-lean-agent (2), goedel-prover-v2 and
  isabelle-pide-ai (2).

Nineteen entries record a licence narrower than their source's. Each was checked against the
headers or directories of its copied files.

## 4. Sources still unknown

Twelve sources grant no licence that covers the files the library draws on:
- **No licence anywhere in the tree or README:** harmonic-imo2025, jordan-curve-theorem,
  mechmath-imo2026, munkres-isabelle, strongpnt and veriso.
- **No licence, and no entries yet:** hopcroft-verif, timsort and verified-consensus. The
  licences in the last two cover vendored subtrees only.
- **A licence that covers other files:**
  - formal-proofs: `lean3/.../semantics/LICENSE` covers only that Lean 3 tree.
  - perennial: `goose/LICENSE` covers only `goose/`, and the pinned branch `lean` has no root
    licence.
  - lean-liquid: a header template cites a `LICENSE` file that does not exist.

Code without a licence is all rights reserved by default. *The 19 entries from these sources
cannot be published without the authors' permission.* Eight of them are accepted.

## 5. What the library contains

Of the 225 live entries, 181 are under permissive licences (Apache-2.0, MIT, the BSDs,
CECILL-B, AML, UniMath's). The other 44 need a decision before publication (protocol §2,
decision 1):

| Class | Entries | Accepted | Sources |
|---|---|---|---|
| unknown | 19 | 8 | the twelve of Section 4 |
| weak copyleft (LGPL, MPL-2.0, CECILL-C) | 11 | 9 | bertrand, topology, rocq-stdlib, coq-library-undecidability, mathcomp-analysis, apery, isabelle-pide-ai |
| copyleft (GPL, CC-BY-SA) | 10 | 6 | l4v, jormungand, cogent, corn, trailofbits-skills |
| non-commercial (INRIA) | 3 | 3 | compcert |
| use-restricted (DeepSeek) | 1 | 0 | deepseek-prover-v2 |

## 6. Changes to the detector

`register_source.py` gained three things.

**New rules.** AML and the DeepSeek agreement are recognised. Boost is tested before MIT. MIT
needs its notice condition and its disclaimer, so a variant such as UniMath's stays unknown. A
BSD text without the binary-form clause is BSD-1-Clause.

**A `licence_to_read` list.** Each new registration records why the licence still needs a
person to read it:
- a GNU text, which does not say "only" or "or later";
- several licence files;
- a NOTICE file;
- an SPDX tag in a Markdown licence file;
- a text that assigns licences by file or directory;
- no licence found.

`SOURCE.md` then reads "detected, not yet read", and `--set-licence` clears the list.

**`--licence-file` and `--licence-url`.** These copy licences found below the root or
published outside the repository.

**Test.** Run over the 110 licence files copied before the audit, the new rules change exactly four
readings: fiat-crypto's BSD-1, UniMath, ml-hilbert and deepseek-prover-v2. Every source this
audit corrected would now be either read correctly or flagged.

## Appendix: every source

"Confirmed" means the detector's reading was checked and kept. "Corrected" means the licence was
changed after reading. "Read, kept" means the licence was kept with a note or extra files.
Counts of entries exclude deprecated ones.

| Source | Licence | Reading | Entries |
|---|---|---|---|
| abel | `CECILL-B` | confirmed | 1 |
| afp | `BSD-3-Clause AND LGPL-2.1-only` | corrected | 5 |
| analysis | `Apache-2.0` | confirmed | 1 |
| apap | `Apache-2.0` | confirmed | 2 |
| apery | `CECILL-C` | confirmed | 1 |
| arklib | `Apache-2.0` | confirmed | 2 |
| autocorrode | `MIT` | confirmed | 3 |
| axiom-imo2026 | `MIT` | confirmed | 4 |
| bedrock2 | `MIT` | confirmed | 2 |
| bertrand | `LGPL-2.1-or-later` | corrected | 1 |
| brouwer | `MIT` | confirmed | 0 |
| brownian-motion | `Apache-2.0` | confirmed | 2 |
| cam-combi | `Apache-2.0` | confirmed | 0 |
| carleson | `Apache-2.0` | confirmed | 6 |
| cedar-spec | `Apache-2.0` | confirmed | 3 |
| certicoq | `MIT` | confirmed | 3 |
| chandra-furst-lipton | `Apache-2.0` | confirmed | 1 |
| classfieldtheory | `Apache-2.0` | confirmed | 2 |
| cogent | `BSD-2-Clause AND GPL-2.0-only` | corrected | 2 |
| compcert | `LicenseRef-INRIA-Non-Commercial AND (LicenseRef-INRIA-Non-Commercial OR LGPL-2.1-or-later) AND LGPL-3.0-or-later AND BSD-3-Clause` | corrected | 3 |
| compfiles | `Apache-2.0` | confirmed | 10 |
| con-nf | `(Apache-2.0 OR MIT) AND LicenseRef-all-rights-reserved` | corrected | 1 |
| coq-library-undecidability | `MPL-2.0` | confirmed | 1 |
| coqeal | `MIT` | confirmed | 1 |
| corn | `GPL-2.0-or-later` | corrected | 1 |
| cvm | `BSD-2-Clause` | confirmed | 1 |
| deepseek-prover-v2 | `LicenseRef-DeepSeek-License-1.0` | corrected | 1 |
| dirac-imo2026 | `MIT` | confirmed | 2 |
| equational-theories | `Apache-2.0` | confirmed | 4 |
| fiat-crypto | `MIT OR Apache-2.0 OR BSD-1-Clause` | corrected | 2 |
| flt-anthropic | `Apache-2.0` | read, kept | 6 |
| flt-imperial | `Apache-2.0` | confirmed | 4 |
| flt-regular | `Apache-2.0` | confirmed | 2 |
| formal-conjectures | `Apache-2.0` | confirmed | 2 |
| formal-proofs | `LicenseRef-unknown` | unknown | 3 |
| fourcolor | `CECILL-B` | confirmed | 3 |
| gaia | `MIT` | confirmed | 1 |
| goedel-prover-v2 | `Apache-2.0` | corrected | 1 |
| hardernarasimhan | `Apache-2.0` | confirmed | 0 |
| harmonic-imo2025 | `LicenseRef-unknown` | unknown | 3 |
| hopcroft-verif | `LicenseRef-unknown` | unknown | 0 |
| humanfia-hoa-qed | `Apache-2.0 AND CC-BY-4.0` | read, kept | 2 |
| hydra-battles | `MIT` | confirmed | 2 |
| infinity-cosmos | `Apache-2.0` | confirmed | 2 |
| interaction-trees | `MIT` | confirmed | 2 |
| isa-blueprint | `MIT` | confirmed | 0 |
| isabelle-dist | `BSD-3-Clause` | confirmed | 3 |
| isabelle-llvm | `BSD-3-Clause` | confirmed | 1 |
| isabelle-pide-ai | `LGPL-3.0-only` | corrected | 2 |
| isabelle-stark | `BSD-3-Clause` | confirmed | 0 |
| jasmin | `MIT` | confirmed | 1 |
| jordan-curve-theorem | `LicenseRef-unknown` | unknown | 1 |
| jormungand | `BSD-2-Clause AND GPL-2.0-only` | corrected | 1 |
| l4v | `GPL-2.0-only AND BSD-2-Clause` | corrected | 3 |
| lean-atiyah-singer | `Apache-2.0` | confirmed | 1 |
| lean-autoformalization-skills | `CC-BY-4.0` | confirmed | 2 |
| lean-liquid | `LicenseRef-unknown` | unknown | 2 |
| lean-stat-learning-theory | `Apache-2.0` | confirmed | 1 |
| lean4-skills | `MIT` | confirmed | 5 |
| leanprover-skills | `Apache-2.0` | confirmed | 3 |
| leray-hopf | `Apache-2.0` | confirmed | 0 |
| math-comp | `CECILL-B` | confirmed | 2 |
| mathcomp-analysis | `CECILL-C` | confirmed | 2 |
| mathlib4 | `Apache-2.0` | confirmed | 12 |
| mechmath-imo2026 | `LicenseRef-unknown` | unknown | 2 |
| metarocq | `MIT` | confirmed | 3 |
| mipre-formalization | `Apache-2.0` | confirmed | 1 |
| ml-hilbert | `AML` | corrected | 2 |
| munkres-isabelle | `LicenseRef-unknown` | unknown | 3 |
| munta | `MIT` | confirmed | 1 |
| navierstokesandeuler | `Apache-2.0` | confirmed | 2 |
| numina-lean-agent | `MIT` | corrected | 2 |
| numina-putnam2025 | `MIT` | confirmed | 4 |
| odd-order | `CECILL-B` | confirmed | 2 |
| odd-order-2 | `Apache-2.0` | confirmed | 1 |
| opengauss | `MIT` | confirmed | 0 |
| perennial | `LicenseRef-unknown` | unknown | 1 |
| persistentdecomp | `Apache-2.0` | confirmed | 0 |
| pfr | `Apache-2.0` | confirmed | 6 |
| physlib | `Apache-2.0` | confirmed | 2 |
| pnt-and | `Apache-2.0` | confirmed | 6 |
| poincare-conjecture | `Apache-2.0` | confirmed | 0 |
| pramaana-imo2026 | `MIT` | confirmed | 2 |
| qcert | `Apache-2.0` | confirmed | 1 |
| reglang | `CECILL-B` | confirmed | 1 |
| rocq-stdlib | `LGPL-2.1-only` | corrected | 3 |
| sampcert | `Apache-2.0` | confirmed | 2 |
| seed-prover | `Apache-2.0` | confirmed | 3 |
| seymour | `Apache-2.0` | confirmed | 2 |
| sphere-eversion | `Apache-2.0` | confirmed | 2 |
| sphere-packing | `Apache-2.0` | confirmed | 4 |
| ssprove | `MIT` | confirmed | 2 |
| strongpnt | `LicenseRef-unknown` | unknown | 3 |
| tarjan | `CECILL-B` | confirmed | 1 |
| timsort | `LicenseRef-unknown` | unknown | 0 |
| topology | `LGPL-2.1-or-later` | corrected | 1 |
| trailofbits-skills | `CC-BY-SA-4.0` | confirmed | 3 |
| unimath | `LicenseRef-UniMath` | corrected | 3 |
| utp-main | `BSD-3-Clause` | confirmed | 1 |
| vellvm | `MIT` | confirmed | 2 |
| verdi | `BSD-2-Clause` | confirmed | 2 |
| verified-consensus | `LicenseRef-unknown` | unknown | 0 |
| veriso | `LicenseRef-unknown` | unknown | 1 |
| voblint-verification-master-thesis | `BSD-3-Clause` | confirmed | 2 |
| vst | `BSD-2-Clause AND (LicenseRef-INRIA-Non-Commercial OR LGPL-2.1-or-later) AND LicenseRef-INRIA-Non-Commercial` | corrected | 2 |
| wasmcert-coq | `MIT AND LGPL-2.1-or-later` | corrected | 1 |
