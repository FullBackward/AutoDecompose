# The Lean module system and the rebuild of dependent files

| Field | Value |
|---|---|
| Authors, organisation | Lean FRO (reference manual; talk by Sebastian Ullrich); Mathlib maintainers and users (Zulip thread opened by Kim Morrison) |
| Date and version read | Reference manual for Lean 4.37.0-rc1. Talk of 24 Apr 2026. Zulip thread of 19 Nov 2025 to 1 Feb 2026. Pull request merged 5 Nov 2025 |
| Source | (1) https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/ , Sections 5.3 to 5.6; https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/ , Section 25.1.2. (2) https://lean-lang.org/presentations/20260424_INRIA/ . (3) https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Mathlib.20has.20moved.20to.20the.20new.20module.20system.html . (4) https://github.com/leanprover/lean4/pull/11097 |
| Licence of the source | No licence is stated on pages (1) to (3). The `lean4` repository is Apache 2.0 (GitHub API) |
| Files in this folder | `source.pdf` (60 pages: sources 1 to 4 in this order, printed with headless Edge), `note.md` |
| What was read | Sections 5.3 to 5.6 in full; Section 25.1.2 in part. All slides of the talk (text; the animation only at its first frame). The whole Zulip thread. The diff and title of the pull request (it has no description) |
| Read on | 2026-11-21 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

The chapter that the Zulip thread calls "The Module System" is now Section 5.4, "Modules and Visibility" [P] (Zulip, 1 Feb 2026). No earlier survey in `docs/research/` covers this topic.

## 1. What the work is

The Lean module system is an opt-in feature of Lean 4. A file that starts with the keyword `module` separates public information from private information [P] (Reference 5.4). Lean then guarantees that private information "can change without affecting clients that import only its public information" [P] (Reference 5.4). Mathlib moved to the module system on 19 Nov 2025 [P] (Zulip, first message). The sources claim that an edit of a proof no longer rebuilds the files that import it. The evidence is two build logs, one animation and one memory figure. No source gives a systematic measurement of rebuild time.

## 2. How it works

A module has two scopes. The public scope is the information that an importing module can see. The private scope is the information that only the module itself can see [P] (Reference 5.4). Lean writes three `.olean` files for a module: private, public and server information [P] (Reference 5.5). Lake, the build tool, stores a hash of each input of each artifact and does not rebuild an artifact when all inputs are unmodified [P] (Reference 25.1.2, "Replaying traces"). The talk gives the rule in one line: "changes to private data stop at the end of the file; public changes at the next import" [P] (talk, slide "Basic module system optimizations").

Default visibility:

- Names are private unless they are in a `public section` or carry `public` [P] (Reference 5.4).
- The body of a public definition is private unless the definition carries `@[expose]` [P] (Reference 5.4).
- Proofs of theorems are private, "both for public and private theorems" [P] (Reference 5.4, example "Proofs are Private").
- A plain `import` adds the imported public scope to the private scope of the importer. A `public import` passes it on to the importers of the importer [P] (Reference 5.3.1).

**Edits that do not rebuild the importers.**

| Edit | Source |
|---|---|
| A change inside the proof of a theorem | [P] Reference 5.4; Zulip, 19 Nov 2025 |
| A change of a comment or a docstring | [P] Reference 5.4 |
| A change of the body of a public definition that is not exposed | [P] Reference 5.4, "Control over API evolution" |
| A new or changed private declaration, except for modules that use `import all` | [P] Zulip, Kim Morrison, 19 Nov 2025, 11:11 |

**Edits that still rebuild the importers.**

| Edit | Source |
|---|---|
| A new public theorem: "recompilation of everything downstream" | [P] Zulip, Kim Morrison, 19 Nov 2025, 11:10 |
| A change of the statement of a public declaration | reader's inference from Reference 5.4 |
| A change of the body of an exposed definition | reader's inference from Reference 5.4 |
| A change of a theorem proved by `:= rfl`: the mark is "part of your module's interface" | [P] Zulip, Sebastian Ullrich, 29 Nov 2025 |
| A change of the compiled form of a module that is imported with `meta import` | [P] Reference 5.4.1 |
| A new private theorem, when the importer uses `import all` | [P] Zulip, Kim Morrison, 19 Nov 2025, 11:11 |
| Any change in a file that has no `module` header | reader's inference: Reference 5.4 gives the guarantee to modules only |

Two facts make the second table larger in Mathlib. The porting recipe puts `@[expose] public section` at the top of each file and makes each import a `public import` [P] (Reference 5.6.1). In November 2025 this was the state of "basically all of mathlib" [P] (Zulip, Jovan Gerbscheid, 27 Nov 2025). So in Mathlib each new lemma is public and each definition body is exposed. Only edits of proofs, comments and docstrings are free (reader's summary).

Pull request 11097 closes one hole. The transition option `backward.privateInPublic` exports private declarations. The change switches the option off inside theorem bodies, "to make sure they stay irrelevant for rebuilds" [P] (diff, comment in `src/Lean/Elab/MutualDef.lean`; 3 lines added).

## 3. How it splits a proof

The work does not split proofs. It has one consequence for a split (reader's inference). A private helper lemma costs no rebuild of the importers. A public helper lemma costs the whole cone.

## 4. What it says about scale

| Measurement | Value | Place |
|---|---|---|
| Rebuild after the removal of one option line before a theorem | 1 file built in 1.2 s; build of 7,687 jobs | Zulip, Sebastian Ullrich, 30 Nov 2025 |
| Rebuild after a change in one Fourier file | 1 file built in 13 s; build of 7,668 jobs | Zulip, Sebastian Ullrich, 9 Dec 2025 |
| Rebuild after a proof edit "in the middle of Mathlib" | "instant", an animation, no number | Zulip, Kim Morrison, 19 Nov 2025 |
| Full build of Mathlib | "9k+ files in 9min30s at 2300% CPU" on one AMD EPYC 9455 | talk, slide "File level" |
| Memory to import Mathlib | reduced by 2.8 GB, or 48 % | Zulip, Sebastian Ullrich, 19 Nov 2025 |
| Share of Mathlib data that is private | 64 % | talk, slide "Basic module system optimizations" |
| Cost of the move for one contributor | 2 to 3 hours to repair 50 open pull requests | Zulip, Yaël Dillies, 20 Nov 2025 |

All rows are [P]. No figures given: the number of files rebuilt for a typical pull request before and after the move; the rebuild time for a new public lemma; any measurement with many concurrent editors.

## 5. Evidence

The evidence is the two logs and the animation in Section 4. One user reported a rebuild after a linter option changed; the developer could not reproduce it [P] (Zulip, 28 Nov to 9 Dec 2025). The cause was the continuous integration. A local build did no work, "but the CI workflow run does a lot of work" [P] (Zulip, Michael Rothgang, 12 Dec 2025). The proposed remedy was to fetch the cache of the commit before the push [P] (Zulip, Sebastian Ullrich, 12 Dec 2025). No ablation exists.

## 6. Limits

Stated in the sources:

- The module system was "experimental" in November 2025 [P] (Zulip, first message).
- A project that imports Mathlib and has not opted in gets no memory benefit [P] (Zulip, 19 Nov 2025, 13:16).
- The effect of `@[expose]` on `abbrev`, `instance`, `structure` and `class` is not documented [P] (Zulip, Yaël Dillies, 1 Feb 2026).
- The compiler "creates less-stable public data"; separate compilation is "in progress" [P] (talk, slide "In progress: separate compilation").

Reader's:

- The module system addresses reason (i) only, and only for proof edits. It does not address reason (ii): two agents that edit one file still conflict.
- Prove2Me states that Lean rebuilds the cone "even for a proof-only edit" (arXiv 2608.28433v2, Section 2). For module files this was no longer true nine months before that paper. The card files in the Prove2Me paper have no `module` header [P] (Prove2Me, Figures 1 and 4).

## 7. Relation to the two anchors

Neither anchor cites the module system [S] (Semantic Scholar reference lists). Both anchors add lemmas during a run. Turing Agent finishes one problem with 108 auxiliary lemmas [S] (the shared brief). Under the module system, the visibility of each such lemma decides the rebuild cost (reader's inference).

## 8. What this repository can use

- A rule for the proposed algorithm: state children as private lemmas in the file of the parent when no other file needs them.
- A cost model for a split in Lean: zero dependent files for a proof edit; the import cone for a public statement.
- The library can record, for each Lean entry, whether the child lemmas are public or private.

## 9. Open points and things not read

- How large is the rebuild cone of one new public lemma in Mathlib today? Not measured in the sources.
- Not read: the Lean Together 2026 talk and the hackathon keynote that the slides name; https://radar.lean-lang.org ; the Lake source code; later frames of the animation.
