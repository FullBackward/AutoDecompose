# H. Code and formal-library search: the retrieval layer for the decomposition harvest (as of 2026-11-12)

Prepared 2026-11-12 for AutoDecompose. The owner's next goal is a library of good decompositions and
formalisation skills, harvested by a swarm of Claude agents from large proving projects (seL4/l4v,
AutoCorrode, Prove2Me, Anthropic's and Imperial's FLT, Mathlib, the AFP, PFR, the Equational Theories
Project, Carleson, sphere packing, CompCert, CakeML, Flyspeck) and from harness repositories, each entry
carrying real code and a statement of why it is good. This survey covers the *retrieval layer*: how an
agent finds and fetches the code. Survey I covers the orchestration method; a third survey covers
general Claude research skills. Neither is repeated here.

Method. Documentation and READMEs read through a fetch tool; GitHub REST metadata fetched
unauthenticated for sizes and licences; a small number of harmless read-only queries against public
search endpoints, run with `curl` on 2026-11-12 under a generic user agent and logged in §8. No API
keys and no paid calls were used. The only clone was one sparse, shallow checkout of the 6 MB PFR
repository into a scratch directory, to test the recipe. `gh` is not installed on this machine, so
GitHub code search (which requires a token) was read about but not run. Tags as in [B]:

- **[P]** read in the primary source, or observed in a query I ran, during this survey;
- **[S]** secondary source only (aggregator, search-engine summary, forum) -- treat as provisional;
- **[U]** unverified: not opened, not runnable here, or recalled rather than read.

---

## 0. Findings in brief

1. **No single tool covers the corpus.** grep.app indexes neither seL4/l4v nor the AFP mirror;
   Sourcegraph's public index lacks the AFP, the Isabelle mirror and Carleson; GitHub code search
   needs a token and has no regular expressions in its REST form. The one tool that answered both
   test questions is **searchcode**, which clones any public repository on demand: it found 1,138
   one-line `consider ... | ...` splits in the AFP mirror in 28.6 s, keyless [P].
2. **For anything bulk, fetch once and search locally.** The AFP release tarball is 105 MB [P];
   a sparse shallow clone of a blueprint directory costs a few hundred KB [P]. A swarm should share
   one local mirror per source and search it with ripgrep. Remote search is for *finding*, not for
   *harvesting*.
3. **The decomposition structure is often already published as data.** leanblueprint pages embed
   the whole dependency graph as DOT text (PFR: 219 nodes, 403 edges) [P]; LeanArchitect exports
   blueprint nodes as JSON (`lake build :blueprintJson`) [P]; Anthropic's FLT repository states each
   theorem in `Theorems/Thm_X_y.lean` and proves it in `P2M/Sol/S_X_y.lean`, "whose `import
   Theorems.Thm_...` lines are exactly the theorems it cites" [P], so its import graph *is* its
   lemma DAG; AFP entry pages give "Depends on"/"Used by" and a session graph PDF [P].
4. **Isabelle FindFacts, the only AFP-wide theorem search, was down** (HTTP 502 on every path
   tried, 2026-11-12) [P]. It ships inside Isabelle (`isabelle find_facts_index -A :`,
   `isabelle find_facts_server`) with a REST API (`api/query`, `api/blocks`, `api/block`) [P source],
   so it can be self-hosted. Otherwise, Isabelle name lookup goes through `find_theorems` in a live
   session (IPS `isabelle_query`, Isabelle-MCP, PIDE AI) and only sees imported theories [P].
5. **Lean search services work but are rate-limited and drift.** Loogle's JSON API answered and
   states its Mathlib revision [P]; LeanSearch answered with the proof body (`value`) included,
   but placed `Real.sqrt` in `Mathlib.Data.Real.Sqrt` where Loogle has `Mathlib.Analysis.Real.Sqrt`,
   i.e. its index lags current Mathlib [P]. Moogle did not respond [P]. lean-lsp-mcp throttles
   remote search to 3 requests per 30 s [P].
6. **Skill files worth harvesting exist on both sides**, with very different licences: lean4-skills
   (MIT), Trail of Bits `writing-lean-proofs` (CC-BY-SA-4.0, ShareAlike), LeanAutoformalizationSkills
   (CC-BY-4.0), leanprover/skills (Apache-2.0), kappelmann's Isabelle skills (LGPL-3.0), AutoCorrode's
   style guide and prompt templates (MIT), the Munkres CLAUDE.md (no licence file: link, do not copy) [P].
7. **Licences constrain copying more than access.** Mathlib, both FLTs, PFR, ETP, Carleson and sphere
   packing are Apache-2.0; AFP entries are BSD or LGPL per entry; l4v mixes GPL-2.0 (kernel proofs)
   and BSD-2-Clause (libraries) per file; CompCert is under a non-free INRIA non-commercial licence [P].
   The library must record a licence per snippet.

---

## 1. General code search reachable from Claude Code

### 1.1 Comparison

| Tool | Coverage (tested) | Query language | Auth / limits | Cost | MCP | Provenance in results |
|---|---|---|---|---|---|---|
| grep.app MCP | "over a million public GitHub repositories" [P]; FLT, PFR yes; **l4v, AFP mirror no** [P] | literal or regex (`useRegexp`), `repo`, `path`, `language`, case, whole word [P] | none observed; web JSON API blocked to curl by a Vercel challenge (429) [P]; limits unstated [U] | free | `https://mcp.grep.app`, one tool `searchGitHub` [P] | repo, path, `blob/master` URL, licence; no SHA [P] |
| Sourcegraph public (sourcegraph.com) | popular repos: PFR, FLT, ETP, l4v yes; **AFP mirror, Isabelle mirror, Carleson no** [P] | regex `/.../`, `repo:`, `file:`, `lang:`, `select:repo`, `count:` [P] | stream API works anonymously [P]; limits unstated [U] | free (public) | MCP is Enterprise-only, on your own instance [P] | repo, path, line, commit SHA [P] |
| searchcode | any public git repo, one per call, cloned on demand [P]; l4v and AFP mirror both worked [P] | keywords, `OR`/`NOT`, phrases, `/regex/`, fuzzy, `file:`, `path:`, `lang:`, `ext:` [P] | "Free during beta. No signup. No API key." [P]; limits unstated [U] | free (beta) | `https://api.searchcode.com/v1/mcp`, also REST [P] | repo, file, line, `commit_sha` [P] |
| GitHub code search (REST) | default branch, files < 384 KB [P]; AFP-mirror coverage [U] | legacy syntax, qualifiers `repo:`, `org:`, `language:`, `path:`, `filename:`, `extension:` [P GitHub MCP README]; no regex documented [P] | **token required** (anonymous call: 401) [P]; 10 requests/min, 1,000 results, 256-char queries, ≤5 boolean operators [P] | free with token | official `github/github-mcp-server`, remote `https://api.githubcopilot.com/mcp/`, OAuth or PAT; `search_code`, `get_file_contents` [P] | repo, path, SHA |
| GitHub repo search (REST) | names, descriptions, topics | `language:`, `topic:`, `stars:` | anonymous: 10/min [P] | free | via GitHub MCP | repo metadata |
| DeepWiki | public GitHub repos; an l4v wiki exists [P] | natural language; generated wiki pages | MCP free, no auth [P]; web pages returned 429 to curl [P] | free | `https://mcp.deepwiki.com/mcp`; `read_wiki_structure`, `read_wiki_contents`, `ask_question` [P] | LLM-written prose; **not evidence** |
| Software Heritage | archive of public code; l4v archived (241 visits, last 2026-10-17) [P] | origin search, SWHID lookup; no full-text code search in the API index page [P] | docs: 120/h anonymous, 1,200/h authenticated [P]; origin search returned `X-Ratelimit-Limit: 10` [P] | free | none found | SWHIDs (permanent) |
| Context7 | library *documentation*: Mathlib4 entry has 728 snippets, about 98k tokens [P] | library id + topic | key optional [S] | free tier | yes | docs only, useless for theorems |
| raw.githubusercontent.com | any public file at any ref | URL | unauthenticated downloads rate-limited since May 2025, numbers not published [P changelog] | free | n/a | exact SHA if the URL uses one |
| GitHub tarball / codeload | any public repo at a ref | URL | `api.github.com/.../tarball/{ref}` counts against the 60/h core limit and redirects to codeload [P]; codeload direct answered 200 [P] | free | n/a | ref in URL |
| Sparse shallow clone | any git repo | `git sparse-checkout set <dirs>` | clones are rate-limited unauthenticated [P changelog] | free | n/a | full SHA |

### 1.2 Notes per tool

**grep.app MCP** [P]. The tool description advertises literal patterns and regular expressions,
including `(?s)` for multi-line matches. In practice regex queries over the whole index timed out
(HTTP 504, twice), and a query containing `\uses{` returned HTTP 500; literal queries with a `repo`
or `path` filter came back in about a second. One call returned at most about ten files and the
schema has no paging parameter, so grep.app answers "show me some real uses of X", not "enumerate
every X". Each hit carries its licence string, which is useful for the library.

**Sourcegraph** [P]. The anonymous stream endpoint
`https://sourcegraph.com/.api/search/stream?q=...&v=V3` returns server-sent events with matches,
filters and alerts. Forks and archived repositories are excluded unless `fork:yes`/`archived:yes`.
`lang:Isabelle` is unreliable: a `consider` regex under `lang:Isabelle` returned 17 matches, ten of
them in apple/corecrypto; filter by `file:\.thy$` instead. Its value is cross-repository regex over
popular repositories with commit SHAs. The Sourcegraph MCP server is documented as "Supported on
Enterprise plans" and runs on one's own instance [P], so it is not an option here.

**searchcode** [P]. `code_search` takes `repository` (one full git URL, required; "There is no
cross-repository or global search"), `query`, `snippet_mode` (`auto`, `grep`, `summary`), `context_lines`,
`max_results` (≤100), `offset`, and a structural `code_filter`. Other tools: `code_analyze`,
`code_get_file` (by symbol name or line range), `code_get_files`, `code_file_tree`,
`code_get_findings` [P]. First call on l4v took 5.3 s and a repeat 0.17 s; the cold AFP query took
28.6 s. A regex containing backslashes was rejected with "Parse error: invalid JSON" (twice, with two
escaping styles); the same pattern written with character classes (`[|]`, ` *`) worked [P]. It
recognises `.thy` files as Isabelle [P]. Being a beta with unstated limits, it should be used for
targeted queries, not as the harvest's bulk channel.

**GitHub code search** [P docs]. Requires authentication even for public code; 10 requests per
minute; only the default branch; only files under 384 KB; at most 1,000 results per query. The web
UI's newer engine supports `/regex/`, but the REST endpoint (and so the GitHub MCP `search_code`
tool, which forwards REST syntax) documents no regex [S for the web-UI contrast]. With a token it is
the best way to enumerate *which repositories* contain a pattern (for example blueprint files across
GitHub), followed by local search.

**DeepWiki** [P]. Free, unauthenticated MCP; `read_wiki_structure` on seL4/l4v returned a table of
contents (overview, verification framework, per-architecture refinement, information flow, CapDL...).
Useful to orient a fresh agent in an unfamiliar repository; its pages are model-generated and must
never be quoted as the reason a decomposition is good.

**Fetching.** All raw fetches in this survey (about fifteen files) succeeded [P]. Pin by SHA:
`https://raw.githubusercontent.com/<owner>/<repo>/<sha>/<path>`. The sparse recipe, tested on PFR [P]:

```
git clone --depth 1 --filter=blob:none --sparse https://github.com/teorth/pfr.git pfr
cd pfr && git sparse-checkout set blueprint/src     # 311 KB working tree, 127 tracked paths listed
```

### 1.3 The two test questions

*All Isabelle `consider ... | ...` case splits in the AFP.*

- searchcode, run [P]: `code_search(repository="https://github.com/isabelle-prover/mirror-afp-devel",
  query="/^ *consider .*[|]/ ext:thy", snippet_mode="summary")` gave `total_matches: 1138` with
  `has_more: true` and a commit SHA; first hits in `Hales_Jewett`, `Galois_Energy_Games`,
  `Quasi_Borel_Spaces`. The same query on l4v gave one match (`lib/Word_Lib/Word_Lemmas.thy:1531`):
  l4v seldom uses Isar `consider`.
- The regex sees one-line splits only. Multi-line `consider` blocks need local search after the
  tarball, for example `rg -n -A4 --glob '*.thy' '^\s*consider\b' thys/` and a filter on `|`
  within the block [S, not run here].
- AFP sources on disk use ASCII symbol escapes (`\<in>`, `\<noteq>`), as the matches show [P]; patterns
  must target those, and conversion goes through the IPS translator, never a hand-made table
  (README convention).
- grep.app and Sourcegraph cannot answer: the AFP mirror is not in either index [P].

*All Lean blueprint `\uses{}` nodes on GitHub.*

- Enumerate projects. Sourcegraph, run [P]: `file:blueprint/src/.*\.tex$ \uses{ select:repo`
  (literal) gave six repositories (ByteDance-Seed/EdgeBench, ImperialCollegeLondon/FLT,
  Verified-zkEVM/ArkLib, math-inc/strongpnt, teorth/equational_theories, teorth/pfr), so its index
  is far from complete. grep.app, run [P]: `searchGitHub(query="uses{", path="blueprint/src/content.tex")`
  gave nine others (math-inc/ZkLinalg, math-inc/KakeyaFiniteFields, emilyriehl/infinity-cosmos,
  b-mehta/ABC-Exceptions...). GitHub repository search, run anonymously [P]: `blueprint language:Lean`
  gave 62 repositories. With a token, GitHub code search `"\uses{" path:blueprint/src extension:tex`
  should be the most complete enumeration [U, not run].
- Per project, take the graph, not the grep. See §2.4.

---

## 2. Formal-library search

### 2.1 Isabelle

| Tool | Indexes | Access | Limits | Agent-callable | Decomposition evidence |
|---|---|---|---|---|---|
| FindFacts (hosted, `search.isabelle.in.tum.de`) | distribution + AFP | web + REST | n/a | **down: 502 on `/`, `/app`, `/v1/`** [P] | -- |
| FindFacts (self-hosted) | sessions you index, AFP via `-A` [P] | `isabelle find_facts_index [-A ROOT] [-N] [-d DIR] [-n] [SESSIONS]`; `isabelle find_facts_server [-p PORT]`; REST `api/query`, `api/blocks`, `api/block` [P source] | local | yes (HTTP JSON) | each *block* is one command span with `src_before`/`src`/`src_after`, session, theory, start line, and the constants, types and theorems it names; facets on chapter, session, theory, command, kinds [P] |
| AFP site search | entry titles, abstracts, authors, topics, keywords | client-side FlexSearch over `/entries/index.json`, `/authors/index.json`, `/topics/index.json`, `/data/keywords.json` [P] | static files | yes (fetch JSON) | entry-level only |
| AFP entry metadata | 1,054 entries in `index.json` (1.3 MB; fields `abstract, authors, date, link, permalink, related, shortname, title, topic_links, topics, year`) [P] | `https://isa-afp.org/entries/index.json`; per entry `metadata/entries/<Name>.toml` in the repository (title, topics, abstract, `license`, authors, `history`) [P] | static | yes | entry DAG: "Depends on" / "Used by" on each entry page; `session_graph.pdf`, `outline.pdf`, `document.pdf`, per-theory HTML under `browser_info/current/AFP/<Entry>/` [P] |
| AFP statistics | 1,053 entries, 616 authors, ~332,900 lemmas, ~5,601,400 lines; "most used" table led by List Index (26 users) [P] | `https://isa-afp.org/statistics/` | static | yes | which libraries everything rests on |
| `find_theorems` / `find_consts` in a live session | only theories transitively imported by the current one [P, kappelmann skill] | IPS: `POST /api/v1/sessions/{id}/diagnostic` and MCP `isabelle_query` (also `facts/global`) [P local README]; Isabelle-MCP (xqyww123, LGPL-2.1): `isabelle_find_theorems` [P local source]; PIDE AI: output arrives in `get_state` [P skill] | local CPU | yes | name and statement confirmation; generated facts (datatype) included [P] |
| `sledgehammer` via a server | same scope | IPS `POST .../sledgehammer`, `fill_sorries` [P local] | CPU-heavy | yes | which facts close a step (MePo/MaSh premise lists) |
| kappelmann `isabelle-pide-ai` | your sessions | MCP + CLI `pide_ai_cli`; tools include `get_state`, `get_session_state`, `edit_get_state`; sledgehammer as optional extension [P] | local | yes | proof states (only if the base session was built with `show_states`, per [B]) |

FindFacts is the only tool that searches *all* of the AFP by theorem content; with the public
instance down, the harvest should either self-host it on the AFP tarball or fall back to text search.
The Find_Facts paper is arXiv 2204.14191 (Huch and Krauss) [S].

### 2.2 Lean

| Tool | Indexes | Endpoint (tested) | Limits | Returns | Decomposition evidence |
|---|---|---|---|---|---|
| Loogle | Mathlib at a stated revision ("serving mathlib revision 1d2d28f") [P] | `GET https://loogle.lean-lang.org/json?q=Real.sqrt, "le"` → "Found 399 declarations mentioning Real.sqrt. Of these, 111 have a name containing "le"" [P] | 3 req/30 s (lean-lsp-mcp) [P]; local mode `--loogle-local` [P] | name, type, module, doc | none directly; exact existence checks |
| LeanSearch | Mathlib (lagging) | `POST https://leansearch.net/search` `{"query":["square root is monotone"],"num_results":3}` → `Real.sqrt_monotone` [P] | unstated [U] | name, kind, signature, type, **`value` (proof)**, informal name and description [P] | proof bodies of retrieved lemmas |
| Lean Finder | Mathlib | via lean-lsp-mcp at `https://lean-lsp-proxy.leanfinder.workers.dev` (arXiv 2510.15940) [P] | 3 req/30 s [P] | ranked declarations | -- [not called] |
| LeanExplore | Mathlib, Batteries, Std, Init, Lean, PhysLean, CSLib, FLT, FormalConjectures [S] | MCP tools `search`, `get_by_id`, **`get_dependencies`**; `--backend api` with key or `--backend local` after `data fetch` [P docs] | key for remote | statement groups | **dependency lists per declaration** |
| Moogle | -- | `www.moogle.ai`: no connection [P] | -- | -- | treat as gone [U whether permanent] |
| Mathlib docs (doc-gen4) | Mathlib, nightly | per-module HTML (`.../mathlib4_docs/Mathlib/Analysis/Real/Sqrt.html`, 176 KB) and `declarations/declaration-data.bmp` (68.8 MB, modified 2026-11-12) [P] | static | all declarations (the `.bmp` is the search index) [S on format] | source links per declaration |
| lean-lsp-mcp | your project + remote services | `lean_local_search` (ripgrep), `lean_loogle`, `lean_leansearch`, `lean_leanfinder`, `lean_hammer_premise` (default `http://leanpremise.net`), `lean_references`, `lean_declaration_file`, `lean_file_outline`, `lean_verify` (axioms) [P docs] | remote 3/30 s [P] | -- | `lean_references` gives use sites; `lean_verify` the axiom check |
| Leandex (Numina) | Mathlib, semantic | used by numina-lean-agent; keyless, "limits the number of concurrent queries" [P README] | concurrency cap | -- | -- [U] |
| Formal Conjectures | open conjectures from Wikipedia, MathOverflow, OEIS, bbchallenge, ETP, arXiv [P] | repository; attributes `@[category]`, `@[formal_proof]`, `@[AMS]`, `@[question]` [P] | -- | statements | statements; root files `PROOFS.md` and `STATEMENTS.md` [P], contents not read [U] |

Loogle query forms, from its front page [P]: by constant (`Real.sin`), by name substring (`"differ"`),
by subexpression (`_ * (_ ^ _)`), by main conclusion (`|- tsum _ = _ * tsum _`), combined with commas.

### 2.3 Rocq and HOL Light (brief)

- Rocq: the in-system `Search`/`SearchPattern` commands remain the retrieval primitive [S]. `rocq-mcp`
  (PyPI) wraps coq-lsp/Petanque and exposes `rocq_search` [S]; the coq-lsp README says development
  "is not active anymore" as of 0.2.5 [S]. The Rocq-MCP Putnam system (arXiv 2603.20405) designed its
  tools from logs [B]. CompCert's value to the harvest is structural (pass-by-pass simulation
  proofs), and its licence limits copying (§6).
- HOL Light: `search` over the loaded theorem database [U]; Flyspeck (MIT, 179 MB git) is best read
  as text after a clone [P size/licence].

### 2.4 Blueprint graphs: how to scrape them

- **leanblueprint web output** [P]. `dep_graph_document.html` embeds the graph as a DOT
  `strict digraph` passed to `renderDot`; edges appear as `"zero-large" -> "sym-zero"`. Node shapes
  encode kind (PFR: 30 `box` definitions, 189 `ellipse` results) and fill colours encode status.
  Each node also has a modal with its statement and links of class `lean_decl` to
  `docs/find/#doc/<Lean name>`. Extraction: `curl -s <url> | grep -o '"[^"]*" -> "[^"]*"'`
  (PFR: 403 edges, 219 node modals). Carleson's page has 179 node modals [P]; ETP and sphere
  packing pages exist [P]. FLT splits the graph per chapter (`dep_graph_chapter_1.html` ...
  `_7.html`); `dep_graph_document.html` returns 404 there [P].
- **Blueprint LaTeX** [P, PFR source]: `\label{...}`, `\lean{Decl.name}`, `\leanok`, and
  `\uses{a, b}` inside `theorem` and `proof` environments; a sparse clone of `blueprint/src` and a
  regex parser recover statement-uses and proof-uses separately (the HTML graph merges them).
- **LeanArchitect** (Apache-2.0) [P]: `@[blueprint]` on declarations, dependencies *inferred from the
  constants used* (overridable with `uses`/`proofUses`), readiness inferred from sorry-freeness;
  `lake build :blueprintJson` writes machine-readable nodes to `.lake/build/blueprint`. When a project
  uses it, prefer it: edges are then checked by Lean, not hand-written.
- **verso-blueprint** [P]: directives `:::theorem "label"`, `{uses "foo"}[]`, optional `autoDeps`;
  `--dump-manifest`/`--dump-schema` for machine-readable output; reference blueprints
  `ejgallego/verso-flt` and `ejgallego/verso-sphere-packing`. The FLT repository now carries a
  `blueprint-verso` directory beside `blueprint` [P].
- Hand-written `\uses` can be wrong or stale ([E §2.5]); a library entry built from a blueprint graph
  should be cross-checked against the Lean declarations (`lean_references`, imports, or LeanExplore
  `get_dependencies`).

---

## 3. Existing formalisation skill files

| Skill / file | URL | Licence | What it teaches (decomposition-relevant) | Concrete code? | Quality note |
|---|---|---|---|---|---|
| lean4-skills (Freer) | https://github.com/cameronfreer/lean4-skills | MIT [P] | `draft`/`prove`/`autoprove`/`review`/`refactor`/`golf` workflows [B]; `references/proof-templates.md` (induction, case analysis, calc, existential, strong and well-founded induction, uniqueness, equivalence); `sorry-filling.md` (five sorry types, "Blocked-Goal Triage", when to escalate); `subagent-workflows.md` (23 KB) [P] | yes: 76 Markdown files; 42 Lean blocks in `domain-patterns.md`, 14 in `calc-patterns.md`; scripts `sorry-analyzer`, `search-mathlib`, `find-usages` [P] | the most complete Lean set; 485 stars [P]; wrapped by Math Inc's OpenGauss [P] |
| Trail of Bits `writing-lean-proofs` | https://github.com/trailofbits/skills/tree/main/plugins/writing-lean-proofs | **CC-BY-SA-4.0** (repository) [P] | "design top-down, prove bottom-up" [B]; **the extraction ladder**: state the fragment and search by shape first; repeated sub-argument → local `have`; independently interesting or sheds hypotheses → standalone lemma ("Dropping unneeded hypotheses is the stronger trigger"); "long and unwieldy" → split [P] | 16 KB SKILL.md, 8 reference files, two Lean examples in the main file; **ships evals** (5 cases, including `04-structural`) [P] | says it is distilled from Mathlib review practice and from LTE, PFR and FLT [P] |
| leanprover/skills | https://github.com/leanprover/skills | Apache-2.0 [P] | `lean-proof`: "Work on the Hardest Case First"; move sorries earlier by stating `lemma1`, `lemma2` and rewriting the main theorem with them; "Generalize First, Instantiate Last" [P]; also `mathlib-review`, `lean-mwe`, `lean-bisect` | short examples | official; small (last push 2026-02-25) [P] |
| LeanAutoformalizationSkills (Armstrong) | https://github.com/scottnarmstrong/LeanAutoformalizationSkills | CC-BY-4.0 (own material; adapted MIT/Apache parts keep theirs) [P] | 12 skills, among them `build-proof-dependency-graph`, `lean-orchestrator` (bounded proof tasks, independent review), `lean-statement-audit`, `lean-search-discovery`, `lean-proof-patterns` [P] | no Lean code visible on the README; templates under `assets/` [P] | PDE/probability bias; README contradicts itself on whether access is restricted [P] |
| kappelmann `isabelle-pide-ai` skills | https://github.com/kappelmann/isabelle-pide-ai (`.claude/skills/`) | LGPL-3.0 [P] | `isabelle` (4.7 KB): principles in priority order; "Work top-down: state definitions and lemmas with sorry and check that they suffice"; `try0` before sledgehammer; robustness order of methods; "Turn hard steps into a structured proof or a separate lemma"; `find_theorems` scope [P]. `pide-ai` (2.4 KB), `isabelle-ml` (2.1 KB) | inline snippets only [P] | best current Isabelle skill; terse |
| AutoCorrode style guide and prompts | local clone, `design-documents/05-agent-generated-isabelle-style.md`; `isabelle-assistant/prompts/` (upstream https://github.com/awslabs/AutoCorrode) | MIT [P] | style: Isar over one-liners, no opaque `metis`/`smt` where a short derivation exists, acceptance checks [P]. 26 task templates plus six system-prompt files, incl. `extract_lemma.md` (+`_retry`), `refactor_to_isar.md`, `suggest_strategy.md`, `planning_agent_system.md` ("Before referencing a theorem ... verify it exists"), `system/01_isabelle_style.md`, `system/03_task_planning.md` [P] | templates with variables (`{{selected_text}}`, `{{goal_state}}`) [P] | the only industrial Isabelle prompt set found; note that `CLAUDE.md` and `MCP.md` in the local clone are untracked local files, not upstream [P] |
| Munkres-Isabelle `CLAUDE.md` | https://github.com/JUrban/isa_top_autoform1 | **none detected** [P] | gradual `sorry` policy ("Add intermediate lemmas with `sorry` rather than getting stuck"); "isolate the hard part into one or more lemmas"; "Always split automation into visible steps" (`apply` per tactic, to locate timeouts) [P] | Isabelle snippets [P] | produced 806 results [A §1.11]; link, do not copy |
| l4v `docs/Style.thy` | https://github.com/seL4/l4v/blob/master/docs/Style.thy | per-file SPDX [P] | proof style for a large verification codebase; the one passage seen (line 537) warns that a device "used too frequently" makes a proof unreadable and one used "too specifically" makes it break "for not-interesting reasons" [P] | Isabelle theory, 25 KB [P] | not read in full [U] |
| numina-lean-agent | https://github.com/project-numina/numina-lean-agent | README: MIT; GitHub detects none [P both] | `prompts/`, `skills/`, `CLAUDE.md`; skills include `sorrifier`, `informal_prover`, `search`; a "sorry2lemma" command [P README] | [U] not read | contents not inspected |
| OpenGauss (Math Inc) | https://github.com/math-inc/OpenGauss | MIT (fork of hermes-agent; submodules have own terms) [P] | orchestrates lean4-skills workflows; blueprint repos registered via `/project convert` [P] | -- | no separate decomposition doctrine [P] |
| Anthropic FLT repository | https://github.com/anthropics/fermats-last-theorem | Apache-2.0 [P] | not a skill but an exemplar: `PROOF-PATH.md` names each step and its Lean theorem; `formalization.yaml` (mathlib-initiative schema v0.4); statement/proof file split [P] | the proof itself (60,475 modules) [P] | "Not maintained and not accepting contributions" [P] |
| Harmonic, Axiom | -- | -- | no official public skill or prompt set found; community "aristotle-lean" wrappers call Harmonic's keyed API [S] | -- | [U] |

---

## 4. Bulk-access recipes

### 4.1 Sizes and channels

`size` is GitHub's repository size field in KB, roughly the packed history, not the checkout [S on
interpretation]; values read 2026-11-12 [P].

| Corpus | Repository | GitHub size | Licence (GitHub) | Best channel |
|---|---|---|---|---|
| AFP (development) | isabelle-prover/mirror-afp-devel (mirror of Heptapod `foss.heptapod.net/isa-afp/afp-devel`, Mercurial) [P] | 764 MB; pushed 2026-11-12 | none asserted | release tarball `https://isa-afp.org/release/afp-current.tar.gz` = **105,211,032 bytes**, modified 2026-11-11 (the download page still says "about 70 MB") [P]; per-entry tarballs `afp-<Entry>-current.tar.gz` [P]; sparse clone of `thys/<Entry>` + `metadata/` from the mirror |
| Isabelle distribution | isabelle-prover/mirror-isabelle | 1.06 GB | NOASSERTION | sparse clone of `src/HOL/...`, `src/Doc/` |
| seL4 proofs | seL4/l4v | 121 MB | NOASSERTION (per-file SPDX) | sparse clone of `proof/`, `lib/`, `docs/` |
| Mathlib | leanprover-community/mathlib4 | 496 MB | Apache-2.0 | shallow clone; `Archive/` holds olympiad solutions [P root listing] |
| Imperial FLT | ImperialCollegeLondon/FLT | 40 MB | Apache-2.0 | shallow clone incl. `blueprint/`, `blueprint-verso/` |
| Anthropic FLT | anthropics/fermats-last-theorem | 233 MB (includes `html/`) | Apache-2.0 | sparse clone of `Theorems/`, `P2M/`, `PROOF-PATH.md` |
| PFR | teorth/pfr | 6 MB | Apache-2.0 | full shallow clone |
| ETP | teorth/equational_theories | 165 MB | Apache-2.0 | sparse: `equational_theories/`, `blueprint/`, `full_entries.json`, `data/` |
| Carleson | fpvandoorn/carleson | 7.5 MB | Apache-2.0 | full shallow clone |
| Sphere packing | thefundamentaltheor3m/Sphere-Packing-Lean (math-inc copy 15 MB) | 18 MB | Apache-2.0 | full shallow clone |
| Formal Conjectures | google-deepmind/formal-conjectures | 15 MB | Apache-2.0 | full shallow clone |
| CompCert | AbsInt/CompCert | 22 MB | NOASSERTION (INRIA non-commercial) | clone for reading only |
| CakeML | CakeML/cakeml | 176 MB | BSD-3-Clause | sparse clone |
| Flyspeck | flyspeck/flyspeck | 179 MB | MIT | sparse clone |
| AutoCorrode | awslabs/AutoCorrode | 11 MB | MIT | local clone exists |

### 4.2 Extracting structure: Isabelle

From the system manual source (`src/Doc/System/Sessions.thy` on the GitHub mirror) [P]:

- `isabelle sessions -D AFP/thys` prints all AFP sessions in topological order; `-R` gives the sessions
  they require; `-b` follows build dependencies instead of source imports. This is the session DAG.
- `isabelle build -a -o browser_info` writes HTML presentation, including the session graphs that the AFP
  site already publishes per entry.
- `isabelle export -x "*:**" SESSION` extracts all theory exports from the build database (`-l` lists them).
- `isabelle dump -B SESSION` dumps the cumulative PIDE database (markup for everything); the manual warns
  that HOL-Analysis needs "several GB of heap", suggesting `-Xmx32g` and `--maxheap 32G`. Not worth it
  for the harvest except for a few chosen entries.
- `isabelle find_facts_index -A :` then `isabelle find_facts_server` gives an AFP-wide theorem search
  with a JSON API [P source]; build cost on the full AFP [U].
- For decomposition evidence inside proofs (Isar `have`/`show` skeletons, `consider`, `obtain`,
  `moreover ... ultimately`, induction cases), plain-text regex over `.thy` files is the practical
  route; FindFacts blocks are top-level commands and do not split proofs [S, from the block model].

### 4.3 Extracting structure: Lean

- `lake exe graph --to Module out.html` (also `.xdot_json`, `.pdf`; `--from`, `--doc-url`) from
  leanprover-community/import-graph (Apache-2.0) [P]; `#min_imports`, `#find_home` for placement.
  For Anthropic's FLT, the import graph of `P2M/Sol` restricted to `Theorems.*` *is* the citation DAG.
- LeanArchitect `lake build :blueprintJson` and verso-blueprint `--dump-manifest` (§2.4).
- cmu-l3/ntp-toolkit: `lake exe <tool>` or `scripts/extract_repos.py --config ...` with flags for
  `premises` (premises used by each constant), `declarations`, `full_proof_training_data`, `imports`,
  `state_comments` (proof states as comments after each tactic) [P README]; licence not stated [U].
- "The Network Structure of Mathlib" (arXiv 2604.24797): a multilayer graph of 308,129 declarations,
  8.4 million edges, 7,563 modules [P abstract]; whether the data are released [U].
- Axiom check before admitting any harvested Lean proof: `#print axioms` (or lean-lsp-mcp
  `lean_verify`); Anthropic's FLT builds this into `FinalCheck.lean` with `#guard_msgs` [P].

---

## 5. Retrieval stack recommended for the harvest

### 5.1 Which tool for which question

| # | Question an agent has | First choice | Fallbacks | Example (all but the last two run in this survey) |
|---|---|---|---|---|
| 1 | Which projects and entries exist, how big, under what licence? | AFP `entries/index.json` + `metadata/entries/*.toml`; GitHub REST repo metadata | GitHub repo search; Sourcegraph `select:repo` | `curl https://isa-afp.org/entries/index.json`; `GET https://api.github.com/repos/teorth/pfr` |
| 2 | What is the lemma or node DAG of a project? | published graph: blueprint DOT, LeanArchitect JSON, AFP "Depends on"/`session_graph.pdf`, FLT imports | `lake exe graph`; `isabelle sessions`; LeanExplore `get_dependencies` | `curl -s https://teorth.github.io/pfr/blueprint/dep_graph_document.html \| grep -o '"[^"]*" -> "[^"]*"'` |
| 3 | Where does pattern X occur in one known repo? | local ripgrep on the shared mirror | searchcode `code_search` (SHA-stamped) when no mirror exists yet | searchcode: `repository=…/mirror-afp-devel`, `query="/^ *consider .*[\|]/ ext:thy"` (as in §1.3) |
| 4 | Where does X occur across GitHub? | GitHub code search with a token (enumerate repos) | grep.app MCP (sample uses); Sourcegraph stream (regex, popular repos) | Sourcegraph: `file:blueprint/src/.*\.tex$ \uses{ select:repo` |
| 5 | Get the exact file at a pinned commit | `raw.githubusercontent.com/<o>/<r>/<sha>/<path>` | searchcode `code_get_file`; GitHub MCP `get_file_contents` | `.../mirror-afp-devel/master/metadata/entries/Jordan_Normal_Form.toml` |
| 6 | Does lemma L exist; what is its statement? | Lean: Loogle (exact, pattern); Isabelle: `find_theorems` via IPS `isabelle_query` in a session importing the entry | LeanSearch/LeanExplore (natural language); self-hosted FindFacts (AFP-wide) | Loogle `q=Real.sqrt, "le"`; LeanSearch `"square root is monotone"` |
| 7 | Get a whole corpus | release tarball (AFP) or sparse shallow clone | codeload tarball | `git clone --depth 1 --filter=blob:none --sparse ...; git sparse-checkout set blueprint/src` |
| 8 | Orient in an unfamiliar repo | searchcode `code_file_tree`/`code_analyze`; DeepWiki `read_wiki_structure` | README, ROOT/lakefile | DeepWiki on `seL4/l4v` |
| 9 | Harvest skill files | GitHub tree API + raw fetch of `SKILL.md`/`references/` | -- | `GET /repos/cameronfreer/lean4-skills/git/trees/main?recursive=1` |

### 5.2 Order of work for one harvest target

1. **Register the source**: repository URL, commit SHA, licence (repository and, for the AFP and l4v,
   per entry or per file), size. One agent does this for all sources before any harvesting.
2. **Mirror once**: tarball or sparse shallow clone into a shared read-only directory; record the SHA.
   Agents never clone independently.
3. **Read the published structure** (blueprint graph, LeanArchitect JSON, `PROOF-PATH.md`, AFP
   dependencies, session ROOTs) and choose candidate nodes from it, rather than from grep hits.
4. **Locate instances** with ripgrep on the mirror; use remote search only for sources not mirrored.
5. **Cite by permalink**: `https://github.com/<o>/<r>/blob/<sha>/<path>#L<a>-L<b>`; grep.app's
   `blob/master` URLs must be re-pinned before entering the library.
6. **Confirm names semantically** (Loogle, `find_theorems`) for every lemma a library entry cites;
   a name that does not resolve does not go in.
7. **Never cite DeepWiki or Context7** as evidence; they are maps, not territory.

### 5.3 Rate budget for a swarm

Loogle and the other services that lean-lsp-mcp calls: 3 requests per 30 s, client-side [P]; run
Loogle locally for bulk use. GitHub: 60 core requests per hour and 10 searches per minute
anonymously [P]; 10 code searches per minute with a token [P]. Software Heritage: 120 per hour
anonymously by its docs, 10 observed on origin search [P]. grep.app, searchcode, Sourcegraph, LeanSearch,
DeepWiki: unstated [U]; treat as one shared, polite client per swarm with a cache keyed on the query.

---

## 6. Licences

| Source | Licence | Consequence for copying into the library |
|---|---|---|
| Mathlib, Imperial FLT, Anthropic FLT, PFR, ETP, Carleson, sphere packing, LeanArchitect, leanblueprint, import-graph, leanprover/skills | Apache-2.0 [P] | copy with attribution; keep NOTICE where present (Anthropic FLT has `NOTICE`, `ATTRIBUTION.md`) [P] |
| Formal Conjectures | Apache-2.0 code, CC-BY-4.0 other material; third-party content (Wikipedia, MathOverflow, OEIS) CC BY-SA 4.0 [P] | per file; statements quoted from Wikipedia carry ShareAlike |
| AFP | per entry, `license = "bsd"` or LGPL in `metadata/entries/<Entry>.toml` [P for the field; LGPL value S] | record per entry; LGPL code copied into the library stays LGPL |
| Isabelle distribution | BSD-style [S]; GitHub reports NOASSERTION [P] | attribution |
| seL4/l4v | "proofs about the seL4 kernel code itself are licensed under GPL version 2, and general libraries and tools under the 2-Clause BSD license"; per-file SPDX; `LICENSE.md` itself CC-BY-SA-4.0 [P] | check each file's SPDX tag; GPL-2.0 snippets impose GPL on the containing work |
| CompCert | "INRIA Non-Commercial License Agreement ... a non-free license"; some files dual LGPL [P] | link and describe; quote only short excerpts |
| CakeML | BSD-3-Clause [P] | attribution |
| Flyspeck, AutoCorrode, lean4-skills, OpenGauss | MIT [P] | attribution |
| Trail of Bits skills | CC-BY-SA-4.0 [P] | **ShareAlike**: adapted text must stay CC-BY-SA |
| LeanAutoformalizationSkills | CC-BY-4.0 [P] | attribution |
| kappelmann isabelle-pide-ai | LGPL-3.0 [P] | skills text under LGPL; quote with care |
| Isabelle-MCP (xqyww123) | LGPL-2.1 [P] | tool, not copied |
| Munkres repository | no licence file detected [P] | default copyright: link and summarise, do not copy |
| numina-lean-agent | MIT per README; not detected by GitHub [P] | verify `LICENSE` before copying |
| ntp-toolkit, verso-blueprint | not stated on the pages read [U] | check before reuse |

grep.app returns a licence string with each hit [P], and searchcode returns the commit; neither
replaces a per-file check for l4v and the AFP.

---

## 7. Gaps and unverified points

- **FindFacts public instance**: down on 2026-11-12; whether temporarily or retired [U]. The cost of
  indexing the full AFP locally [U].
- **GitHub code search** was not run (no token, no `gh`): its coverage of the AFP mirror and of
  blueprint files, and its exact syntax for `\uses{` [U].
- **Rate limits** of grep.app, searchcode, Sourcegraph public search, LeanSearch and DeepWiki are not
  published [U]. raw.githubusercontent.com limits since May 2025 are not published either [P].
- **grep.app regex** queries timed out in this session; whether this is load or a standing limit [U].
- **searchcode** is a beta; the backslash-escape failure may be a JSON-handling bug [P observed, cause U].
- Lean Finder and Leandex were not called; LeanExplore's remote API was not called; Moogle's status
  beyond one failed connection [U].
- `isabelle dump`, `isabelle export`, `isabelle sessions`, `lake exe graph`, LeanArchitect and ntp-toolkit
  were read about, not run (no Isabelle or Lean toolchain used here).
- LeanAutoformalizationSkills, numina-lean-agent and l4v `docs/Style.thy` were read only at README or
  listing level; Math Inc, Axiom and Harmonic publish no official skill or prompt set that I found [U].
- The AFP licence split (how many entries are LGPL) was not counted [U]; the TOML field was read for one entry.
- Rocq and HOL Light search were covered from secondary sources only.
- The Mathlib network dataset (arXiv 2604.24797): release status [U].
- Prove2Me's own code: not located; Anthropic's FLT repository carries a `P2M/` directory [P], whose
  relation to Prove2Me the README extract does not state [U].

---

## 8. Query log (2026-11-12, curl, generic user agent)

- **grep.app**: JSON API `q=obtain&f.lang=Isabelle` → 429 (Vercel challenge). MCP: `tools/list` →
  `searchGitHub`; `leanok` in `teorth/pfr` → hits; `\uses{` with path filters → 500 ×2; three regex or
  `\leanok` queries → 504 ×3; `crunch` in l4v and `consider` in the AFP mirror → no results;
  `uses{` in FLT → 10 hits; `uses{` at `blueprint/src/content.tex` → 9 repositories.
- **Sourcegraph stream**: pinned PFR `\uses{` → 5 matches with SHA; `lang:Isabelle` consider regex
  → 17 (10 in apple/corecrypto); pinned AFP mirror, Isabelle mirror, Carleson → "No repositories found";
  `file:blueprint/src/.*\.tex$ \uses{ select:repo` → 6 repositories.
- **GitHub REST**: anonymous code search → 401; `rate_limit` ×2; 29 repository metadata calls; 4
  recursive trees; 5 root listings; repo search `blueprint language:Lean` → 62, `topic:lean-blueprint`
  → 2; tarball HEAD → 302 to codeload.
- **searchcode MCP**: `tools/list`; l4v `consider ext:thy` → 112 (5.3 s), regex → 1 (0.17 s), regex
  with backslashes → parse error ×2; AFP mirror regex → 1,138 (28.6 s).
- **Lean**: Loogle `Real.sqrt, "le"` and front page; LeanSearch one `POST`; Moogle (no connection);
  LeanExplore home (200).
- **Isabelle**: FindFacts `/`, `/docs`, `/app`, `/v1/` → 502; AFP `search/`, `search.js`,
  `entries/index.json`, one entry page, one `browser_info` index, tarball HEAD.
- **Other**: four blueprint graph pages and the FLT blueprint index; DeepWiki MCP
  `read_wiki_structure seL4/l4v` (web pages 429 ×2); Software Heritage origin search; Context7 search;
  one sparse clone of PFR; about fifteen raw.githubusercontent.com fetches (all 200).

---

## 9. Source index

General code search
- grep.app MCP: https://vercel.com/blog/grep-a-million-github-repositories-via-mcp ; endpoint https://mcp.grep.app
- Sourcegraph MCP docs: https://sourcegraph.com/docs/api/mcp ; stream API https://sourcegraph.com/.api/search/stream
- searchcode: https://searchcode.com/ ; MCP https://api.searchcode.com/v1/mcp
- GitHub REST search: https://docs.github.com/en/rest/search/search ; GitHub MCP server: https://github.com/github/github-mcp-server
- GitHub unauthenticated limits: https://github.blog/changelog/2025-05-08-updated-rate-limits-for-unauthenticated-requests/
- DeepWiki MCP: https://docs.devin.ai/work-with-devin/deepwiki-mcp ; Software Heritage API: https://archive.softwareheritage.org/api/
- Context7: https://context7.com/

Isabelle
- FindFacts source: https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/master/src/Tools/Find_Facts/src/find_facts.scala ; changeset https://isabelle.in.tum.de/repos/isabelle/rev/9bc4f982aef4 ; paper https://arxiv.org/abs/2204.14191 ; hosted (down) https://search.isabelle.in.tum.de/
- System manual, Sessions chapter: https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/master/src/Doc/System/Sessions.thy
- AFP: https://isa-afp.org/statistics/ , https://isa-afp.org/download/ , https://isa-afp.org/search/ (other AFP URLs inline in §2.1, §4.1)
- PIDE AI: https://github.com/kappelmann/isabelle-pide-ai ; Isabelle-MCP: https://github.com/xqyww123/Isabelle-MCP , https://pypi.org/project/isabelle-mcp/
- IPS: local `Isabelle_Pool_Server/README.md`, `mcp_servers/lsp/README.md`

Lean
- Loogle: https://loogle.lean-lang.org/ ; LeanSearch: https://leansearch.net/ , https://github.com/frenzymath/LeanSearch , https://arxiv.org/abs/2403.13310
- Lean Finder: https://arxiv.org/abs/2510.15940 , https://huggingface.co/spaces/delta-lab-ai/Lean-Finder
- LeanExplore: https://www.leanexplore.com/ , https://kellyjdavis.github.io/lean-explore/user-guide/mcp-server , https://arxiv.org/html/2506.11085v1
- lean-lsp-mcp: https://github.com/oOo0oOo/lean-lsp-mcp , https://raw.githubusercontent.com/oOo0oOo/lean-lsp-mcp/main/docs/tools.md
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- leanblueprint: https://github.com/PatrickMassot/leanblueprint ; LeanArchitect: https://github.com/hanwenzhu/LeanArchitect , https://arxiv.org/abs/2601.22554 ; verso-blueprint: https://github.com/leanprover/verso-blueprint
- Blueprint graphs (`<site>/blueprint/dep_graph_document.html`): https://teorth.github.io/pfr/ , https://florisvandoorn.com/carleson/ , https://teorth.github.io/equational_theories/ , https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/ ; FLT per chapter: https://imperialcollegelondon.github.io/FLT/blueprint/
- import-graph: https://github.com/leanprover-community/import-graph ; ntp-toolkit: https://github.com/cmu-l3/ntp-toolkit ; Mathlib network: https://arxiv.org/abs/2604.24797
- Formal Conjectures: https://github.com/google-deepmind/formal-conjectures

Rocq, HOL Light
- coq-lsp: https://github.com/LLM4Rocq/coq-lsp , https://ocaml.org/p/coq-lsp/latest/CHANGES.html ; rocq-mcp: https://pypi.org/project/iflow-mcp-rocq/ ; Flyspeck: https://github.com/flyspeck/flyspeck

Skill files: the URLs are in the §3 table; Trail of Bits page https://trailofbits.com/skills/writing-lean-proofs/ ; Munkres paper https://arxiv.org/abs/2604.07455

Corpora and licences
- seL4/l4v: https://github.com/seL4/l4v , https://github.com/seL4/l4v/blob/master/LICENSE.md , https://github.com/seL4/l4v/blob/master/docs/Style.thy
- Anthropic FLT: https://github.com/anthropics/fermats-last-theorem (README, `PROOF-PATH.md`, `formalization.yaml`)
- Imperial FLT: https://github.com/ImperialCollegeLondon/FLT ; PFR: https://github.com/teorth/pfr ; ETP: https://github.com/teorth/equational_theories ; Carleson: https://github.com/fpvandoorn/carleson ; sphere packing: https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean
- Mathlib: https://github.com/leanprover-community/mathlib4 ; CompCert: https://github.com/AbsInt/CompCert/blob/master/LICENSE ; CakeML: https://github.com/CakeML/cakeml
