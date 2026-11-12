# The decomposition library: structure, tools and harvest protocol

AutoDecompose, 2026-11-12. A plan, not a record: nothing in it has been run.
It draws on three surveys made for it, of Claude research skills [G], code and
formal-library search [H] and the organisation of large searches [I], and on
the research note's Section 7 and surveys D to F for what the library should
contain.

The owner's goal is a library of decompositions and formalisation skills
taken from large proving projects and from harnesses, each entry carrying real
code from a pinned commit and a specification of why it is good, gathered by a
swarm of agents. The owner asked for the structure first, so that the swarm is
built once. Section 1 says what the library is; Section 2 which existing Claude
skills to reuse; Section 3 how agents find and fetch code; Section 4 the
harvest protocol and the swarm's roles; Section 5 the entry; Section 6 the
start set; Section 7 what to build and in what order; Section 8 the decisions
the owner must make before any tokens are spent.

My conclusions, stated first.

(i) No existing skill does this job. Anthropic publishes the parts
(subagents, skills, and in `math-proof:siege` a strict loop of fresh workers,
an append-only ledger and blind verifiers), and the community publishes the
data model (a schema first, then one validated record per item). The right
course is a project-local skill that copies these mechanisms, not an installed
third-party one [G §4, §5].

(ii) No single search service covers the corpus. grep.app lacks l4v and the
AFP, Sourcegraph lacks the AFP and Carleson, and Isabelle FindFacts was down
on the day of the survey. Each source is pinned to a commit and its files
fetched by raw view at that commit when needed; remote search serves only to
discover sources [H §0, §5]. (The survey's advice to mirror each source was
dropped by the owner's decision of Section 8.)

(iii) The harvest should be run as a systematic review, not a crawl: a written
protocol, a source ledger, two independent discovery strategies,
schema-checked extraction, a verifier that never sees the extractor's
reasoning, and a stop rule [I §2.8, §4].

(iv) A pilot of about 20 sources must come first. The cost per accepted entry
is unknown, Anthropic's multi-agent research system spends about fifteen times
the tokens of a chat, and agents' citations are 40 to 80 % accurate with 3 to 13 % invented
URLs, so the checks must be mechanical and their cost measured before the full
run [I §0, §1.1, §4.8].

## 1. What the library is

An entry is of one of three kinds [I §4.1]:

- an *instance*: a parent goal, its children, the skeleton joining them, and
  how each child closed;
- a *skill*: a rule, prompt, tactic recipe or skill file for stating, splitting
  or closing goals, with evidence of its effect;
- an *anti-pattern*: a decomposition that failed (a false or insufficient
  child, a wrong definition), kept because large projects fail on statements
  [note §7.1, point 4].

Every entry carries one move from a vocabulary fixed before extraction: the
moves of [F §10] (case split with its exhaustiveness obligation, induction with
its `arbitrary:` set, the two directions of an iff, a named witness, set
equality, a calculational chain, `suffices` and strengthening, a key invariant
or auxiliary statement, an interface or locale lemma, a generated per-callee
lemma [D §1.1], sorrify at the failure site), and "other" with a note. The
vocabulary is amended once, after the pilot.

The library exists to test the rule set. Each accepted entry records which
rule of [F §10] it supports or contradicts, and the first coverage target is
that each of those 18 rules has at least two instances from independent
projects or is marked unsupported.

## 2. Existing Claude skills: what to reuse

[G] catalogued 55 candidates and read 13 in detail. Anthropic publishes no
general deep-research or literature-review skill [G §1].

*Adopt as they are*: Claude Code's built-in subagents (Explore for locating,
general-purpose for analysis) with `memory: project`, `maxTurns` and
`disallowedTools`; `skill-creator`, to draft the project skill and test it on
three scenarios before the harvest [G §5.1].

*Adapt*, copying the mechanism and not the code:

| Mechanism | Source | Used for |
|---|---|---|
| append-only ledger with typed status (proved, refuted, open); rounds gated by a script; fresh verifiers that see only the artefact | `math-proof:siege`, Anthropic's official plugin marketplace [G §3.2] | verification phase; `ledger.jsonl` |
| schema first; one JSON record per item; a validator; `[uncertain]` marks; resume | Weizhena Deep-Research-skills [G §3.3] | entry format; `validate_entry.py` |
| locator agents, then analyser agents; links pinned to a commit; record, do not judge, while locating | HumanLayer `research_codebase` [G §3.6] | discovery and site finding |
| one state file; deduplication; one-hop citation chasing; saturation stop | `scholar-deep-research` [G §3.4] | snowballing through papers |
| no URL without a retrieval; a source ledger; a citation pass that may not edit text | daymade `deep-research`; Anthropic cookbook prompts [G §3.1, §3.5] | provenance gate |

*Avoid*: collections of persona prompts with no mechanism; anything that calls
paid APIs or other providers' models; unlicensed tools and anything with a
Sci-Hub fallback; any third-party skill run with permissions disabled outside a
container [G §5.3].

Nothing is to be installed now. A third-party skill wanted later is read in
full and vendored at a pinned commit.

## 3. Retrieval: how agents find and fetch code

For each source, in this order [H §5.2]:

1. *Register* it: canonical upstream URL, commit hash, licence (per entry for
   the AFP, per file for l4v), size. One agent registers all sources before any
   harvesting.
2. *Fetch by raw view, never mirror* (owner's decision, Section 8). The commit
   is pinned with `git ls-remote`; the file list comes from jsDelivr's keyless
   listing at that commit, or a blobless tree fetch; each file is fetched from
   `raw.githubusercontent.com` (or a GitLab `/-/raw/` URL) at the commit. Files
   fetched only for searching go to a disposable, git-ignored cache. Workers
   never clone.
3. *Read the structure the project already publishes* before searching text:
   blueprint dependency graphs (PFR's page embeds 219 nodes and 403 edges),
   LeanArchitect JSON, the imports of Anthropic's FLT (each proof file imports
   exactly the theorems it cites), AFP "Depends on" lists, session `ROOT` files
   [H §2.4, §5.1].
4. *Locate* instances with ripgrep on the mirror, by mechanical signals: Isar
   `proof (induct`, `proof (cases`, `consider`, `obtain`, `also ... finally`,
   locales, `crunch`; Lean `suffices`, `calc`, `induction ... generalizing`,
   `rcases`, blueprint `\uses{}` [I §4.2].
5. *Cite by permalink*, `.../blob/<sha>/<path>#L<a>-L<b>`; a `blob/master` link
   is re-pinned before it enters the library.
6. *Confirm every cited lemma name*: `find_theorems` through the Pool Server for
   Isabelle, Loogle for Lean. A name that does not resolve does not go in.

Remote search is for discovery only. GitHub code search needs a token (the
`gh` CLI is not installed here); searchcode needs no key and found 1 138 AFP
`consider` splits in 28.6 s; grep.app and Sourcegraph sample popular
repositories. DeepWiki is a map, never evidence. Limits to respect: GitHub
anonymous, 60 core requests an hour and 10 searches a minute; Loogle, 3
requests per 30 s, so bulk lookups need a local Loogle [H §5.3].

## 4. The harvest protocol and the swarm

Seven phases, each writing files that the next reads [I §4.2]:

| Phase | Roles | Writes | Gate |
|---|---|---|---|
| 0 Protocol | owner, lead | `protocol.md`, start set, hidden gold standard, move vocabulary, schema | owner approval; pilot |
| 1 Discovery | two discoverers, different strategies | `ledger/queries.jsonl`, `ledger/sources.jsonl` | forks resolved; commit pinned |
| 2 Screening | two screeners, an adjudicator; site finders | `ledger/screening.jsonl`, `ledger/sites.jsonl` | a criterion code per decision |
| 3 Extraction | one extractor per site | `entries/<id>/entry.md`, `entries/<id>/files/` | schema valid; code copied by tool |
| 4 Verification | verifier without the extractor's transcript; build checker | `checks/<id>.json` | provenance, build, fidelity, sufficiency, claims |
| 5 Specification | one writer per entry | "why it is good", rule mapping | every claim tied to evidence |
| 6 Review | deduplicator; one reviewer per lens; owner sample | `reviews/<id>.json`, `reports/` | no open objection |

The two discovery strategies are search strings over GitHub, the AFP index,
Mathlib and arXiv, each query logged as run, and snowballing from the start
set, backward through dependencies and citations and forward through importers
and citing papers. Their overlap estimates what both missed [I §4.7].

The verifier checks, in order: the commit, path and lines exist and the excerpt
is byte-identical; the excerpt builds at that commit (the Pool Server for
Isabelle, `lake build` at the pinned toolchain for Lean); it rebuilds with only
its declared context, since extraction loses assumptions [D §1.9]; the parent
builds with every child `sorry` [F §9]; each child closes by the method named;
and each claim is verified, refuted or unverifiable. These checks spend prover
time, not model tokens.

*The swarm.* The phases become one saved workflow, `.claude/workflows/harvest-library.js`.
The lead only coordinates. Workers run in parallel only over disjoint shards,
one source or one directory each, with a four-part brief (objective, output
format, tools and sources, boundaries); they write files and return ids, never
content [G §4; I §0]. A smaller model screens and finds sites; a stronger one
writes specifications and reviews; the model id is recorded per field.
Concurrency stays within 16, and the 25-agent mark is the point to check the
pilot's extrapolation [I §4.8].

*Stopping.* Recall of at least 0.8 against the hidden gold standard (30 to 50
known instances, chosen in Phase 0 and withheld from the discoverers); per move
and source stratum, two rounds with no new cluster; a token ceiling per phase.
Empty cells of the coverage matrix (move by prover by domain by source kind)
are reported, not filled by loosening the criteria [I §4.7].

## 5. The entry

Each entry is a directory, `library/entries/<id>/`, holding `entry.md` (YAML
front matter and prose) and `files/` (the excerpt at its original relative
path, with the context it needs). The fields, in full in [I §4.4]:

- *identity*: id `<prover>-<move>-<source>-<8 hex>`, kind, status, title,
  intent, move;
- *content*: applicability (the goal shape, and when not to use the move);
  parent and children verbatim; the skeleton joining them; the excerpt;
- *provenance*: URL, full commit hash, path, lines, retrieval date, how found,
  harvest run, and which agent and model wrote each field;
- *licence*: SPDX identifier and whether the excerpt may be stored or only
  pointed to [H §6];
- *checks*: prover and version; build, fidelity, sufficiency, how each child
  closed and its size; each pass, fail or not run, with its log;
- *why it is good*: numbered claims, each with its kind of evidence (a check,
  an author's statement with its location, a measurement with its budget, a
  known use), a pointer and the verifier's verdict, with counter-evidence;
- *metrics, consequences, known uses, related entries, the rule supported, and
  review*.

An entry is accepted only with one passing prover check and at least one other
kind of evidence, and "pattern" requires two independent projects. Duplicates
are found by location, by a hash of the excerpt with names normalised, by the
parent's canonical statement, and by move with goal shape; a cluster keeps its
best verified instance and lists the others as known uses [I §4.5].

## 6. The start set

The table below is the start set as first proposed, from [H §3, §4.1, §6].
After the owner's decisions (Section 8) every source is copied whatever its
licence, Rocq sources were added, and the batches run Lean first, then Rocq,
then Isabelle. The operative list is `library/sources/start-set.json` (31
Lean, 16 Rocq and 6 Isabelle sources; 45 of the Lean and Rocq ones are
registered, and the two hosted on the MPI-SWS GitLab, Iris and std++, could
not be reached from the harvest machine).

| Source | Prover | Kind | Licence | Storage |
|---|---|---|---|---|
| AFP (release tarball) | Isabelle | instances | BSD or LGPL, per entry | copy (LGPL: see Section 8) |
| Isabelle distribution, `src/HOL`, `src/Doc` | Isabelle | instances, skills | BSD-style | copy |
| seL4 `l4v` (`proof/`, `lib/`, `docs/Style.thy`) | Isabelle | instances, skills | GPL-2.0 proofs, BSD libraries, per file | per file (see Section 8) |
| AutoCorrode, incl. `isabelle-assistant/prompts/` | Isabelle | instances, skills | MIT | copy |
| Munkres in Isabelle (`isa_top_autoform1`) | Isabelle | instances, skill | none found | pointer |
| kappelmann `isabelle-pide-ai` skills | Isabelle | skills | LGPL-3.0 | see Section 8 |
| Mathlib, incl. `Archive/` | Lean | instances | Apache-2.0 | copy |
| PFR, Carleson, sphere packing, Imperial FLT, Anthropic FLT, ETP | Lean | instances (blueprints, statement graphs) | Apache-2.0 | copy |
| Formal Conjectures | Lean | instances, anti-patterns | Apache-2.0; some text CC BY-SA | per file |
| lean4-skills, leanprover/skills, LeanAutoformalizationSkills | Lean | skills | MIT, Apache-2.0, CC-BY-4.0 | copy |
| Trail of Bits `writing-lean-proofs` | Lean | skill | CC-BY-SA-4.0 | see Section 8 |
| CakeML, Flyspeck | HOL4, HOL Light | instances | BSD-3, MIT | copy |
| CompCert | Coq | instances | non-free, non-commercial | pointer |
| harnesses of [F] (humanize2, numina-lean-agent and others) | various | skills (procedures, prompts) | per repository | per repository |

## 7. What to build, in order

(a) *Without model calls.* `library/protocol.md`, the schema and the move
vocabulary; scripts in the standard library only (`ledger.py`,
`validate_entry.py`, `dedupe.py`, `permalink_check.py`, `saturation.py`,
`build_index.py`); the project skill `.claude/skills/harvest-decompositions/`
(`SKILL.md` with `disable-model-invocation: true`, `references/fields.md`,
`references/corpora.md`, `references/briefs.md`); three agent definitions:
`harvest-locator` (read and fetch only), `harvest-analyst` (writes only under
`library/entries/`) and `harvest-verifier` (no web search; runs the permalink
check; cannot edit entries) [G §5.4]. Then the source register and the corpus
mirror. The skill is tested with `skill-creator` on three scenarios.

(b) *The pilot*, which needs the owner's go-ahead because it spends tokens:
about 20 sources through every phase, chosen to span Isabelle and Lean,
mathematics and verification, human and agent projects. It measures tokens per
source screened, per site extracted and per accepted entry, prover time per
entry, and the owner's agreement with the verifier on a sample. The vocabulary
and schema are amended once, by dated amendment.

(c) *The full run*, in batches, with an owner gate between batches and the
budget per batch derived from the pilot.

## 8. The owner's decisions (2026-11-12)

The questions put to the owner, and the answers, which supersede the
recommendations above where they differ:

1. *Copyleft and other restricted code*: copied whole, like everything else,
   so that every entry is readable at once; the upstream link goes in a note.
   Each entry and source note records its licence, and the library README
   warns that non-permissive entries must be reviewed before the repository is
   ever published.
2. *Where the library lives*: `library/` in this repository.
3. *Corpus mirror*: none. Since the code that matters is copied into the
   library, files are fetched by raw view at the pinned commit when needed.
4. *GitHub token*: none; raw view, `git ls-remote` and jsDelivr's listing
   suffice.
5. *Budget*: the owner will pay for deep and wide searches; the pilot measures
   the cost per accepted entry, and each run still needs a go-ahead.
6. *Languages*: Lean first, then Rocq, Isabelle later; no translation. Each
   source keeps its own language, because the languages differ in what they
   make easy.

## 9. State of the build (2026-11-12)

Step (a) of Section 7 is built: `library/protocol.md`, the tools in
`library/tools/`, the project skill `.claude/skills/harvest-decompositions/`,
the agent definitions `.claude/agents/harvest-{locator,analyst,verifier}.md`
and the workflow `.claude/workflows/harvest-library.js`. The tools were tested
on one exemplar entry (`lean-case-split-compfiles-6ac56e7f`): it validates,
its copied file is byte-identical upstream, a retyped code block is rejected,
and promotion is refused until an independent verifier records the build and
a verdict per claim. No Lean or Rocq toolchain is installed, so build checks
use the source's CI record and the fidelity and sufficiency checks do not run.

Because the owner's Claude plan must keep about 30 % of its weekly limit, the
workers run on DeepSeek instead: `library/tools/run_harvest.py` drives the same
phases with headless Claude Code processes pointed at DeepSeek's
Anthropic-compatible API (`deepseek-flash` for locators,
`deepseek-v4-pro` for analysts and verifiers). Each worker gets only its
role's tools; the driver stops if any reply comes from a Claude model, and
stops launching work at the config's token or call ceiling. The pilot's
configuration is `library/runs/pilot-1.json`.
