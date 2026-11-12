# I. Search orchestration: how to run a multi-agent harvest that is systematic, reproducible and checkable (as of 2026-11-12)

Prepared 2026-11-12 for AutoDecompose. The owner's next goal is a swarm of Claude agents that
harvests, from large proving projects and harness repositories, a library of good decompositions and
formalisation skills, each entry carrying real code or files and a specification of why it is good.
This survey covers the *method* of the harvest: how the work is partitioned, recorded, checked and
stopped. Companion surveys cover existing Claude research skills and code and formal-library search
tools. Surveys D-F and the research note are cited as [D §x], [E §x], [F §x], [note §7.x].

Method. Web search, then reads of primary sources through a fetch tool that returns extracts:
Anthropic's engineering posts, the Claude Code documentation, OpenAI's and Google's product
descriptions, READMEs and abstracts of open systems and benchmarks, PRISMA 2020 and PRISMA-S
(PubMed Central copies). Four PDFs returned as binary were converted locally with `pdftotext`:
OpenAI's deep-research page as saved on OpenAI's CDN, Kitchenham and Charters 2007, Wohlin 2014,
Kalliamvakou et al. (extended). Prog_Prove's "Proof Patterns" was read in its source,
`src/Doc/Prog_Prove/Isar.thy`, on the GitHub mirror of Isabelle, because TUM hosts refused
connections. Tags as in [B]:

- **[P]** read in the primary source during this survey;
- **[S]** secondary source only (search summary, aggregator, forum) -- treat as provisional;
- **[U]** unverified: could not open the source, or recalled rather than read.

Could not be opened: the BMJ and Springer pages of PRISMA 2020 and PRISMA-S (PMC copies read
instead); full texts of Petersen et al. 2015, Zhang et al. 2011 and Freitas and Whiteside 2014; the
otto-SR preprint; the Software Heritage documentation (the SWHID specification at swhid.org was
read instead).

---

## 0. Findings in brief

1. **The orchestrator-worker shape is settled; what varies is who holds the plan.** Anthropic's
   research system, open_deep_research, GPT-Researcher and Gemini Deep Research all have a planner
   and parallel workers that return condensed findings (§1.1-1.5). Of Claude Code's mechanisms, only
   a *dynamic workflow* (a re-runnable script whose agents return schema-checked JSON and whose
   replay is deterministic) is built for hundreds of items (§1.3).
2. **Parallelise the search, not the writing.** Anthropic, LangChain and Cognition each report that
   workers with vague or overlapping briefs duplicate work or produce incompatible pieces (§1.1,
   §1.5, §1.6). Partition by disjoint sources; write each specification in one place.
3. **Agent citations need a mechanical check.** Audits find citation accuracy of 40-80 %, 3-13 % of
   cited URLs never existed, and a 91 % calibration error for Deep Research on BrowseComp (§1.6). For
   a code library the remedy is cheap: commit, path and lines, re-fetched and compared byte for byte.
4. **Tokens buy quality expensively.** Token usage explained 80 % of BrowseComp variance in
   Anthropic's analysis; multi-agent runs cost about 15 times a chat (§1.1). Budget per accepted
   entry and pilot first.
5. **Systematic reviews already define the reproducible record:** a protocol fixed in advance,
   searches "copied and pasted exactly as run" with dates and counts, deduplication, a screening log
   with agreement measured, a piloted extraction form, a flow from records found to items included
   (§2.8).
6. **GitHub has known traps:** a repository is not a project, most are personal and inactive, many
   are mirrors (§2.6). Resolve forks and mirrors before screening.
7. **Trusted catalogues share five guards:** a template with *consequences* and *known uses*, a build
   at a pinned version, refereeing, an erratum or flag, and named maintainers (§3). Without the
   second and fourth, more than half of miniF2F's formal statements came to differ from the informal
   ones (§3.5).
8. **Stopping can be measured:** recall against a quasi-gold standard, a capture-recapture estimate
   from two discovery strategies, and saturation (§2.5, §4.7).

---

## 1. Multi-agent research architectures

### 1.1 Anthropic, "How we built our multi-agent research system" (13 June 2025) [P]

https://www.anthropic.com/engineering/multi-agent-research-system

- **Partition.** A lead agent plans, saves the plan to memory (contexts beyond 200 000 tokens are
  truncated) and spawns parallel subagents. Each brief must state "an objective, an output format,
  guidance on the tools and sources to use, and clear task boundaries"; vague briefs meant "one
  subagent explored the 2021 automotive chip crisis while 2 others duplicated work".
- **Effort scaling in the prompt.** "Simple fact-finding requires just 1 agent with 3-10 tool calls";
  comparisons 2-4 subagents; complex research more than 10. Early versions were "spawning 50
  subagents for simple queries". The lead runs 3-5 subagents in parallel, cutting time "by up to
  90 %".
- **Merge and sources.** Subagents return condensed findings; the lead synthesises and "passes all
  findings to a CitationAgent". An appendix advises that subagents write to a filesystem and return
  references, to "minimize the 'game of telephone'".
- **Evaluation.** "We started with a set of about 20 queries representing real usage patterns." One
  LLM-judge call "outputting scores from 0.0-1.0 and a pass-fail grade" on factual accuracy, citation
  accuracy, completeness, source quality and tool efficiency agreed best with people; "end-state
  evaluation rather than turn-by-turn analysis". Humans found agents "chose SEO-optimized content
  farms over authoritative but less highly-ranked sources".
- **Results and cost.** Opus 4 lead with Sonnet 4 subagents "outperformed single-agent Claude Opus 4
  by 90.2 %"; agents use "about 4x more tokens than chat", multi-agent systems "about 15x"; on
  BrowseComp "token usage by itself explains 80 % of the variance".
- **Fit and failure.** Good for "breadth-first queries"; poor where agents "share the same context or
  involve many dependencies". Reported failures: too many subagents, endless search for absent
  sources, distracting updates, duplicated subtasks, and "small changes to the lead agent can
  unpredictably change how subagents behave". Errors compound, so runs resume from checkpoints.

### 1.2 Anthropic's guidance on agents, context and long horizons [P]

- "Building effective agents" (https://www.anthropic.com/engineering/building-effective-agents):
  *workflows* are "orchestrated through predefined code paths", *agents* "dynamically direct their
  own processes"; patterns include parallelisation by sectioning or voting, orchestrator-workers and
  evaluator-optimiser (given "clear evaluation criteria"); "find the simplest solution possible".
- "Effective context engineering"
  (https://www.anthropic.com/engineering/effective-context-engineering-for-ai-agents): *context rot*;
  sub-agents explore with "tens of thousands of tokens or more" and return "a condensed, distilled
  summary ... (often 1,000-2,000 tokens)"; hold "lightweight identifiers (file paths, stored
  queries, web links, etc.)".
- "Effective harnesses for long-running agents" (26 November 2025,
  https://www.anthropic.com/engineering/effective-harnesses-for-long-running-agents): agents tried "to
  one-shot the app", or would "see that progress had been made, and declare the job done". The fix: a
  progress file, an initial commit, and a JSON list of over 200 features all `"passes": false` that
  later sessions may only flip ("It is unacceptable to remove or edit tests"), because "the model is
  less likely to inappropriately change or overwrite JSON files compared to Markdown files".

### 1.3 Claude Code's own mechanisms, as documented [P]

From https://code.claude.com/docs/en/agents.md and https://code.claude.com/docs/en/workflows.md:

| | Subagents | Agent teams | Dynamic workflows |
|---|---|---|---|
| Who decides the next step | Claude, turn by turn | the lead, turn by turn | the script |
| Intermediate results | caller's context | shared task list | script variables |
| What is repeatable | worker definition | team definition | the orchestration itself |
| Documented scale | "a few delegated tasks per turn" | "start with 3-5 teammates" | "dozens to hundreds of agents per run" |

- **Subagents**: Markdown files with YAML frontmatter in `.claude/agents/`; each "runs in its own
  context window" with only its own prompt and returns a summary; nesting "up to three layers".
- **Agent teams** (experimental): a shared task list whose claiming "uses file locking"; not for
  "sequential tasks, same-file edits, or work with many dependencies". The competing-hypotheses
  example argues for independent checkers: "Sequential investigation suffers from anchoring". Hooks
  (`TaskCompleted`) can refuse completion until a check passes; task status "can lag".
- **Dynamic workflows**: JavaScript with `agent()`, `pipeline()` (one agent per item), `parallel()`,
  `phase()`. `agent()` may take a JSON `schema`; invalid output is retried up to five times. 16
  concurrent agents by default, 1 000 per run; a "Large workflow" warning above 25 agents or 1.5
  million projected tokens. `Date.now()` and `Math.random()` throw "so that a relaunched run repeats
  the same `agent()` calls", and a relaunch replays completed agents from saved results. Scripts can
  be saved to `.claude/workflows/`. The bundled `/deep-research` "votes on each claim" and lists a
  claim it cannot check "as unverified instead of counting it as refuted". Cost advice: run "on a
  small slice first".

### 1.4 OpenAI and Google deep research, as their makers describe them [P]

- **OpenAI** (2 February 2025; OpenAI's PDF copy of its launch page, the HTML returned 403): one o3
  agent "trained using end-to-end reinforcement learning on hard browsing and reasoning tasks",
  "backtracking and reacting to real-time information", able to "cite specific sentences or passages";
  5-30 minutes per report. It "can sometimes hallucinate facts", "may struggle with distinguishing
  authoritative information from rumors" and "shows weakness in confidence calibration". The
  partition is learned, not specified.
- **Gemini** (https://gemini.google/overview/deep-research/): a user-editable plan; the planner
  "determines which sub-tasks can be tackled simultaneously and which need to be done sequentially";
  "a novel asynchronous task manager that maintains a shared state between the planner and task
  models, allowing for graceful error recovery without restarting the entire task"; "multiple passes of
  self-critique".

### 1.5 Open systems [P]

- **GPT-Researcher** (https://github.com/assafelovic/gpt-researcher): planner questions, parallel
  executors, a publisher; "source-track each resource"; a tree mode with "configurable depth and
  breadth"; "~$0.4 per research" with o3-mini; warns that it favours repeated information.
- **STORM / Co-STORM** (https://github.com/stanford-oval/storm; arXiv 2402.14207, 2408.15232):
  partition by *perspective* through simulated expert interviews, outline before writing; judged
  better organised (25 points absolute) and about 10 % broader than a retrieval baseline; editors
  flagged "source bias transfer and over-association of unrelated facts".
- **open_deep_research** (https://github.com/langchain-ai/open_deep_research; blog 16 July 2025,
  https://www.langchain.com/blog/open-deep-research): scope, research, write; each researcher's last
  call "cleans up its findings"; "Only use multi-agent for easily parallelized tasks", because
  parallel section-writing gave reports "disjoint because the section-writing agents were not well
  coordinated"; the research brief is "our north star". Deep Research Bench: RACE 0.4309 for $45.98
  and 58 M tokens per full run with defaults, 0.4401 for $187.09 with Claude Sonnet 4.
- **Hugging Face open deep research** (https://huggingface.co/blog/open-deep-research): 55.15 % on
  GAIA validation against OpenAI's 67.36 %; JSON tool calls instead of code actions fell to 33 %.

### 1.6 Evaluations and failure studies, 2025-26

- **BrowseComp** (arXiv 2504.12516) [P]: 1 266 hard-to-find, easy-to-verify questions; trainers
  checked that existing models failed each one. Deep Research 51.5 %, GPT-4o with browsing 1.9 %;
  aggregating 64 attempts added 15-25 %, best-of-N most; 91 % calibration error.
- **BrowseComp-Plus** (arXiv 2508.06600) [P]: a fixed corpus, because "dynamic and opaque web APIs
  hinder fair comparisons and reproducibility". Lesson: freeze the corpus (commits, not branches).
- **DeepResearch Bench** (arXiv 2506.11763) [P]: 100 PhD-level tasks in 22 fields, scored on report
  quality and on citation accuracy and "effective citations"; the names RACE and FACT and the
  per-system citation figures are [S].
- **DeepTRACE** (arXiv 2509.04499) [P]: "large fractions" of statements unsupported by the systems'
  own sources; citation accuracy "40-80 % across systems"; per-system rates [S].
- **DEFT** (arXiv 2512.01948) [P]: 14 failure modes from about 1 000 reports; agents struggle "not
  with task comprehension but with evidence integration, verification".
- **Reference hallucination** (Rao, Wong, Callison-Burch, arXiv 2604.03173, April 2026) [P]: of over
  221 000 cited URLs, 3-13 % hallucinated and 5-18 % non-resolving; a URL-checking tool cut
  non-resolving citations 6-79x, to under 1 %.
- **MAST** (arXiv 2503.13657) [P]: 14 failure modes in three groups (system design, inter-agent
  misalignment, task verification), kappa 0.88, over 1 600 traces; multi-agent gains on benchmarks
  "are often minimal".
- **Cognition, "Don't Build Multi-Agents"** (12 June 2025,
  https://cognition.com/blog/dont-build-multi-agents) [P]: "Share context, and share full agent
  traces"; "Actions carry implicit decisions, and conflicting decisions carry bad results"; two
  subagents misread their halves of a Flappy Bird clone and the merger got incompatible parts.

### 1.7 Comparison

| System | Partition | Workers | Merge | Claim check | Failures, cost |
|---|---|---|---|---|---|
| Anthropic research | lead, bounded briefs | 1 to >10 by rule | lead; files | CitationAgent; LLM judge + humans | duplication, content farms; ~15x chat |
| Claude Code workflow | script, one agent per item | 16 concurrent, 1 000 per run | script, schema | `/deep-research` votes; unverified kept apart | warning >25 agents |
| OpenAI deep research | learned (RL) | one | n/a | none stated | hallucination, calibration |
| Gemini | editable plan | not stated | shared state | self-critique | waiting time |
| open_deep_research | supervisor, brief | configurable | compressed findings; one writer | none stated | parallel writing disjoint |
| STORM | perspectives | per perspective | outline first | none stated | source bias transfer |

### 1.8 What this means for the harvest

Script the orchestration (a saved workflow) so that partition, effort rules and stop rules are code;
partition by disjoint source shards; have workers write files and return identifiers; separate
producers from checkers and give checkers the artefact and the source but not the producer's
reasoning; treat every citation as unverified until a tool has re-fetched it; budget per accepted
entry and judge the end state (entry files), not transcripts.

---

## 2. Systematic-search methodology from science

### 2.1 PRISMA 2020 [P]

Page et al., BMJ 2021;372:n71 (https://pmc.ncbi.nlm.nih.gov/articles/PMC8005924/), 27 items. Item 5:
"Specify the inclusion and exclusion criteria"; 6: every source, with the date last searched; 7:
"Present the full search strategies ... including any filters and limits used"; 8: "how many
reviewers screened each record ... whether they worked independently, and if applicable, details of
automation tools used"; 9-10: data collection and defined data items; 11: risk of bias; 16a: a flow
from records identified to studies included; 24: registration, protocol and "any amendments".

### 2.2 PRISMA-S [P]

Rethlefsen et al., Systematic Reviews 2021 (https://pmc.ncbi.nlm.nih.gov/articles/PMC7839230/), 16
items from a Delphi process. Essential here: each source and platform (1); citation searching (5);
contacts (6); strategies "copied and pasted exactly as run" (8); limits (9); reused strategies (11);
updates (12); "the date when the last search occurred" (13); search peer review (14); total records
per source (15); deduplication process and software (16).

### 2.3 Kitchenham and Charters, 2007 [P]

EBSE-2007-01 v2.3. The protocol (questions, search strategy, selection criteria and procedures,
quality checklists, extraction strategy, synthesis, timetable) is "necessary to reduce the
possibility of researcher bias"; "Piloting the research protocol is essential." Searches are
"documented as it occurs and changes noted and justified", raw results "saved and retained". Report
the initial Cohen's kappa; a lone researcher can "re-evaluate a random sample" (test-retest).
Extraction pairs "the data extractor" with "the data checker", and the extractor is never a co-author
of the study.

### 2.4 Wohlin's snowballing guideline, EASE 2014 [P]

http://www.wohlin.eu/ease14.pdf. The start set should span communities, "publishers, years and
authors" ("The important issue here is diversity"). Backward snowballing screens references, forward
snowballing screens citing papers, by title, abstract, place of citation, then full text. Use a paper
for snowballing only once its inclusion is final, else "a rollback is needed"; "do one iteration at
the time to get traceability"; stop when an iteration finds nothing new, then ask active authors.
Wohlin's own start set was weak: its three papers shared an author.

### 2.5 Mapping studies, search recall, what was missed [S]

Petersen, Vakkalanka and Kuzniarz (IST 64, 2015) found two mapping studies of the same literature
classifying it differently: define and pilot the scheme first. Zhang, Babar and Tell (IST 53(6),
2011) measure a search's "quasi-sensitivity" against a *quasi-gold standard* of known relevant
studies. Capture-recapture estimates what two overlapping searches missed and has been proposed as a
stopping rule; it assumes independent searches. With counts n1, n2 and overlap m, the Lincoln-Petersen
total is n1 n2 / m (standard statistics).

### 2.6 Mining software repositories [P]

- **Kalliamvakou et al., "The Promises and Perils of Mining GitHub"** (MSR 2014; EMSE 2016; extended
  version at https://gousios.gr/pub/promises-perils-github-extended.pdf). Thirteen perils, including
  I "A repository is not necessarily a project" (analyse base and forks together); II-III low
  activity, mostly inactive (median 6 commits); IV "Many projects are not software development" (read
  READMEs, not file types); V "Most projects are personal" (67 % one committer); VI mirrors and work
  outside GitHub; XII "GitHub's API does not expose all data"; XIII GitHub keeps changing.
- **ACM SIGSOFT Empirical Standards, Repository Mining**
  (https://github.com/acmsigsoft/EmpiricalStandards/blob/master/docs/standards/RepositoryMining.md):
  justify sources and selection; validate criteria "by manually inspecting automated search results";
  multiple annotators with inter-rater reliability; threats from "selection of data source(s) and
  repositories, selection criteria, search strings"; a replication package; antipattern "using
  open-source repositories without any filtering criteria".

### 2.7 LLM screening [S]

The otto-SR preprint reports an LLM screener at 96.7 % sensitivity against 81.7 % for human dual
review; other 2025 studies range from 58 % to 100 %. Agent screening is plausible, but its recall
must be measured on our data (§4.7).

### 2.8 The minimal artefact set for a reproducible search

| Artefact | Content | Required by |
|---|---|---|
| Protocol, versioned | questions, criteria, sources, strings, extraction form, appraisal, stop rule, budget; amendments | Kitchenham; PRISMA 24 |
| Search log | each query as run, engine, date, filters, hit count; raw results | PRISMA-S 8, 9, 13, 15 |
| Source ledger | candidates, how found, dedup decision | PRISMA-S 5, 16; Wohlin; Kalliamvakou |
| Screening log | decision, criterion, screener; kappa or test-retest | PRISMA 8; Kitchenham |
| Extraction form and check | defined items, piloted; extractor and checker | PRISMA 9-10; Kitchenham |
| Quality appraisal | per source and per item | PRISMA 11 |
| Flow report | counts from identified to included, with reasons | PRISMA 16a |
| Replication package | data and tools | Empirical Standards |

---

## 3. Curated example libraries in programming and formal methods

### 3.1 The design-pattern entry [P]

The GoF template (https://hillside.net/gang-of-four-template): name; intent; also known as;
motivation; applicability (including how to recognise those situations); structure; participants;
collaborations; consequences ("trade-offs and results"); implementation; sample code; known uses
("at least two from different domains"); related patterns. *Consequences* forces the costs to be
stated; *known uses* stops one instance passing as a pattern.

### 3.2 Proof-pattern catalogues

- **Prog_Prove, "Proof Patterns"** [P]: "We show a number of important basic proof patterns. Many of
  them arise from the rules of natural deduction". Skeletons with the children as `show`: two forms
  of case analysis, iff, two forms of contradiction, `fix` for universals, a witness for existentials,
  `obtain`, set equality as two inclusions, subset, chains with `also`/`finally`; then datatype cases
  and structural, computation and rule induction. This is the closest existing catalogue to the move
  vocabulary of [F §10], and each pattern is already a skeleton with holes.
- **Freitas and Whiteside, "Proof Patterns for Formal Methods"** (FM 2014) [S]: patterns as "a common
  vocabulary" for proof obligations, after design patterns; entry fields not read [U].
- **Grov, Lin and Tumas, "Mechanised Verification Patterns for Dafny"** (FM 2016) [P, abstract]:
  patterns encoded as tactics and tested for generality: an executable pattern.
- **QED at Large** (Ringer et al., arXiv 2003.06458) [S] surveys proof engineering; the **Isabelle
  Cookbook** [S] keeps its examples "checked as far as possible" against recent Isabelle versions.
- **Mathlib documentation** (https://mathlib.org/contribute/doc.html) [P]: module docstrings with
  *Main definitions*, *Main statements*, *Notation*, *Implementation notes*, *References*, *Tags*;
  "Every definition and major theorem is required to have a doc string", enforced by `docBlame`.
  *Library notes* are cited as "see note [...]"; 2025 Zulip threads report unported notes [S].
  Lesson: a cross-cutting note needs a resolvable identifier.

### 3.3 The AFP and Mathlib as curated libraries [P]

- **AFP** (https://www.isa-afp.org/submission/): must "run in the current Isabelle/AFP release"; no
  `sorry`, `back`, `sledgehammer` or `smt_oracle`; an abstract; "should cite the sources"; a linter;
  "Your submission will be refereed"; authors "maintain your archive entry or nominate someone else".
  Entry licences not confirmed here [U].
- **Mathlib** (https://mathlib.org/contribute/index.html): "over 2600 open PRs" in mid 2026; the
  review team will "summarily close without comment any low quality PR produced using LLMs", and
  substantial LLM-generated code carries an `LLM-generated` label. A library built by agents should
  likewise say which fields an agent wrote.

### 3.4 Rosetta Code [P]

A task needs "at least one example implementation completed, tested, and working" and "a sample of
correct output"; new tasks start as `{{draft task}}`; `{{incorrect|lang|Explanation}}` flags a
solution that "does not accomplish the given task" and files it under examples needing attention
(https://rosettacode.org/wiki/Rosetta_Code:Add_a_Task, https://rosettacode.org/wiki/Template:Incorrect).

### 3.5 Benchmarks built by harvesting [P unless marked]

- **miniF2F**, audited (arXiv 2511.03108): discrepancies between formal and informal statements
  affect "more than half of the problems"; the best pipeline reaches 70 % on the corrected v2 against
  about 40 % on the original; "over 300" corrected statements is [S].
- **PutnamBench** (arXiv 2407.11214; https://github.com/trishullab/PutnamBench): "hand-constructed
  formalizations of 640 theorems"; the README now lists 672 Lean 4, 640 Isabelle and 412 Coq; errors
  via issues; licences per language; asks people not to publish proofs.
- **ProofNet** (arXiv 2302.12433): 371 textbook examples, each a Lean 3 statement with informal
  statement and proof. **FVEL** (arXiv 2406.14408): 758 Isabelle theories, 29 125 lemmas. Extraction
  can create false statements: 23 of 241 seL4 lemmas in one benchmark had lost their assumptions
  [D §1.9].
- **LeanDojo** (arXiv 2306.15626; https://leandojo.readthedocs.io): 98 734 theorems with premise
  annotations; a repository is traced as `LeanGitRepo(url, commit)`, so provenance is pinned at
  extraction.

### 3.6 Dataset documentation [P]

- **Datasheets for Datasets** (arXiv 1803.09010 v8, CACM 2021): motivation, composition, collection
  process, preprocessing/cleaning/labelling, uses, distribution, maintenance. Questions that carry
  over: the "sampling strategy", "Over what timeframe", "Was the 'raw' data saved?", is the
  processing software available, "tasks for which the dataset should not be used", licence, "Is there
  an erratum?". **Data Cards** (arXiv 2204.01075): "structured summaries of essential facts".
- **SWHID** (https://www.swhid.org/specification/v1.2/): `swh:1:<cnt|dir|rev|rel|snp>:<sha1>`,
  "computed from the content", with qualifiers `origin`, `visit`, `anchor`, `path`, `lines`. A
  content hash survives a moved or deleted repository; a URL does not (peril XII).

### 3.7 What an entry must contain to be trusted

| Reader's need | Field | Done by |
|---|---|---|
| What it is for | intent, applicability | GoF; Mathlib docstrings |
| Costs and limits | consequences | GoF |
| Not a one-off | known uses, two or more | GoF |
| The code works | build at a pinned version | AFP; Rosetta Code; Isabelle Cookbook |
| Where it came from | repository, commit, path, lines, citation | LeanDojo; SWHID; AFP |
| May it be copied | licence per file | PutnamBench; Datasheets |
| The statement says what it claims | fidelity to context and informal statement | missing in miniF2F; [D §1.9] |
| Still right | status, erratum, maintainer | Rosetta `{{incorrect}}`; AFP; Datasheets |
| Who wrote it | author, agent label | Mathlib `LLM-generated` |

---

## 4. A harvest protocol for the decomposition library

My proposal, assembled from §1-3 and [note §7], [D]-[F]. Nothing in it has been run.

### 4.1 Scope and unit

- **Question.** Which decomposition moves and formalisation skills used in real projects and
  harnesses are worth turning into AutoDecompose rules, and on what evidence?
- **Entry kinds.** (a) *Instance*: a parent goal, its children, the skeleton joining them, how each
  child closed. (b) *Skill*: a rule, prompt, tactic recipe or skill file used to state, split or close
  goals, with evidence of effect. (c) *Anti-pattern*: a decomposition that failed (false or
  insufficient child, wrong definition), kept because projects fail on statements [note §7.1 (4)].
- **Move vocabulary, fixed before extraction**, from [F §10] and Prog_Prove: case split (with
  exhaustiveness), induction (with `arbitrary:`), iff, witness/`obtain`, set equality, calculational
  chain, `suffices`/strengthening, key invariant or auxiliary statement, interface or locale lemma,
  generated per-callee lemma [D §1.1], sorrify at the failure site, other (with a note). Pilot on 20
  instances; amend once.
- **Corpus frozen by commit** when a source enters the ledger (the BrowseComp-Plus lesson).

### 4.2 Phases, roles and artefacts

| Phase | Agent roles | Writes | Gate |
|---|---|---|---|
| 0 Protocol | owner, lead | `protocol.md`, start set, quasi-gold standard, vocabulary, schema | owner approval; pilot on ~20 sources |
| 1 Discovery | two discoverers with different strategies | `ledger/queries.jsonl`, `ledger/sources.jsonl` | forks resolved; commit pinned |
| 2 Screening | two screeners, adjudicator; site finders | `ledger/screening.jsonl`, `ledger/sites.jsonl` | criterion code per decision; kappa |
| 3 Extraction | one extractor per site | `entries/<id>/entry.md`, `entries/<id>/files/` | schema valid; excerpt copied by tool |
| 4 Verification | verifier without extractor's transcript; build checker | `checks/<id>.json` | gates G2-G6 |
| 5 Specification | one specifier per entry | "why it is good", rule mapping | claims tied to evidence |
| 6 Review | dedup agent; reviewers by lens; owner sample | `reviews/<id>.json`, `reports/` | acceptance; flow, coverage, cost |

**0 Protocol.** Owner and lead write the question, criteria, sources and search strings, the entry
schema (§4.4, which is the extraction form), gates, stop rules and a budget per phase. Two more
artefacts: a *start set* for snowballing, drawn from surveys A-F to span Isabelle, Lean and Coq,
mathematics and verification, human and agent projects; and a *quasi-gold standard* of 30-50 known
in-scope instances, with commit and path, withheld from the discoverers. Changes later are dated
amendments. The orchestration is a saved workflow whose phases mirror this table.

Draft criteria. Include if public with an identifiable licence (I1), checking in a released prover
at the pinned commit (I2), and curated (AFP, Mathlib, seL4), cited, or a harness with a published
evaluation (I3). Exclude forks and mirrors in favour of upstream (E1); one-committer repositories
without CI unless cited (E2); excerpts whose dependency cone has `sorry`, `oops` or
`quick_and_dirty` (E3); unlicensed sources (E4). Agent-produced proofs form a tagged stratum, so that
results can be reported with and without them.

**1 Discovery.** Strategy A runs search strings over GitHub code search, the AFP index, Mathlib,
Reservoir and arXiv, logging each query as run with engine, date, filters and hit count. Strategy B
snowballs from the start set, backward through dependencies, citations and README links, forward
through importers and citing papers, one iteration at a time. Each candidate row holds the canonical
upstream, pinned commit, how found (query id, or parent and direction), prover and version, declared
licence, committer count, last activity, size and dedup decision. The strategies' overlap feeds §4.7.

**2 Screening.** Two screeners with different prompts read each source's README, ROOT or lakefile and
sample files and record decision and criterion code; an adjudicator settles disagreements; the owner
re-screens a random 10 %. Site finders then locate sites by mechanical signals, which are cheap and
reproducible: Isar `proof (induct ...)`, `proof (cases ...)`, `consider`, `obtain`, `also ...
finally`, locales, `crunch`; Lean `suffices`, `calc`, `induction ... generalizing`, `rcases`,
blueprint `\uses{}`; commits that split a lemma; harness prompt and skill files. Large sources are
sharded by directory, one extractor per shard.

**3 Extraction.** One extractor per site fills the schema as JSON validated by the workflow, rendered
to Markdown. Code is copied by tool from the pinned commit, never retyped, with its context (imports,
locale or `context`, local assumptions, unfolded definitions) at its original relative path. Unknowns
are recorded as unknown.

**4 Verification.** The verifier sees the entry and the source only, and checks in order: provenance
(commit, path, lines exist; excerpt byte-identical); build at the commit (Pool Server for Isabelle,
`lake build` with the pinned toolchain for Lean, or the source's CI record); fidelity (the excerpt
rebuilds with only its declared context [D §1.9]); sufficiency (the parent builds with every child
`sorry` [F §9]); child closure by the named method; and each claim, marked verified, refuted or
unverifiable. These checks spend prover time, not model tokens.

**5 Specification.** One specifier per entry writes intent, applicability, consequences, metrics and
the rule mapping from the verified record only; its own judgements go in a labelled paragraph.

**6 Review.** A dedup agent merges clusters (§4.5) into one entry with several known uses. Reviewers,
one lens each (prover correctness; generality of the move; provenance and licence), try to reject
each entry; a completion hook refuses acceptance while an objection is open. The owner audits a
stratified sample (at least 20 or 10 % per kind) and the agreement rate is reported. Reports: a
PRISMA-style flow (identified, deduplicated, screened, included; sites; extracted, verified,
accepted; reasons at each exclusion), the coverage matrix and the cost ledger.

### 4.3 Layout and formats

```
library/
  protocol.md                  versioned; amendments at the end
  workflow/harvest.js          saved workflow, phases as in 4.2
  ledger/queries.jsonl         searches exactly as run
  ledger/sources.jsonl         candidates, pinned commits, dedup decisions
  ledger/screening.jsonl       decisions, criterion codes, screener ids
  ledger/sites.jsonl           candidate sites
  entries/<id>/entry.md        YAML front matter + prose
  entries/<id>/files/...       excerpts at original relative paths
  checks/<id>.json             verification record
  reviews/<id>.json            verdicts, owner audit
  notes/<note-id>.md           cross-cutting notes cited by id
  reports/                     flow, coverage, cost
  runs/<run-id>/               script hash, prompts, model ids, tokens
```

Ledgers and checks are JSON, append-only for agents (§1.2); entry prose is Markdown for review.

### 4.4 The entry template

| Field | Must contain |
|---|---|
| `id` | `<prover>-<move>-<source>-<8 hex of content key>`; never reused |
| `kind`, `status` | instance, skill or anti-pattern; draft, verified, accepted, flagged (reason), deprecated |
| `title`, `intent` | one line each; what the move achieves for the goal |
| `move` | vocabulary term; `also_known_as` in other provers |
| `applicability` | the goal shape as a pattern (head constant, quantifier prefix, connective, recursion of defined constants); when not to use |
| `parent`, `children` | parent statement verbatim; each child verbatim with its name |
| `skeleton` | proof text joining the children, each child `sorry` or a named lemma; an Isabelle translation of Lean or Coq is marked unverified until checked |
| `excerpt` | files with original path and line range, plus required context |
| `provenance` | repository URL, full commit hash, path, lines, optional SWHID, retrieval date, authors from history, source type, citation, how found, harvest run id, agent role and model per field |
| `licence` | SPDX identifier, licence file at the commit, any restriction on storing the excerpt |
| `checks` | prover and version (Isabelle and AFP, or Lean toolchain and Mathlib commit); build, fidelity, sufficiency, each child's closing method and size; each pass, fail or not run, with date, checker and log hash |
| `why_good` | numbered claims, each with evidence type (check, author quote with location, measurement with budget, known use), pointer and verifier verdict; `accepted` needs one passing check plus one other kind |
| `metrics` | parent and child statement sizes; proof size before and after if history has both; children closed by automation |
| `consequences` | extra statements and obligations (exhaustiveness, side conditions); known failure modes |
| `known_uses` | other instances in the cluster; "pattern" needs two independent projects |
| `related`, `rule` | related entries and notes; the [F §10] rule supported or contradicted |
| `review` | verdict per lens, owner audit, open issues, erratum |

### 4.5 Deduplication keys

1. *Location*: canonical upstream, commit, path, lines.
2. *Content*: hash of the excerpt without comments and whitespace, local and bound names renamed in
   order of appearance; catches forks, mirrors and vendored copies.
3. *Statement*: the parent's canonical form as printed by the prover with types, as in
   [note §7.3 (ii)].
4. *Move*: move term plus goal-shape signature; a cluster keeps its best verified instance as the
   entry and the rest as known uses.
5. *Skill*: hash of a normalised prompt or skill file, since harnesses copy prompts [F §1].
6. *Source*: the upstream of a fork network, resolved at discovery (peril I).

### 4.6 Quality gates

| Gate | Check | Fails to |
|---|---|---|
| G1 screening | criterion code; second screener; kappa on sample | excluded with reason |
| G2 provenance | commit, path, lines exist; excerpt byte-identical | rejected |
| G3 build | builds at pinned commit and prover version | flagged |
| G4 fidelity | excerpt rebuilds with declared context only | flagged |
| G5 sufficiency, closure | parent with children `sorry` builds; children close as stated | flagged, or anti-pattern |
| G6 claims | each claim verified or labelled opinion; refuted removed | back to specification |
| G7 licence | SPDX recorded; storage allowed | pointer only |
| G8 dedup | keys of §4.5 | merged |
| G9 review | no open objection; owner agreement reported | flagged |

### 4.7 Coverage and stopping

- **Recall against the quasi-gold standard**: do not stop below 0.8 without a written reason.
- **Capture-recapture**: n1 n2 / m over the two discovery strategies, reported as a lower bound,
  since the strategies are not independent.
- **Saturation**: per move and source stratum, stop after two rounds with no new cluster (Wohlin's
  "no new papers"; Claude Code's "stop once two rounds in a row find nothing new").
- **Coverage matrix**: move by prover by domain by source kind; report empty cells rather than
  lowering criteria to fill them.
- **Budget**: a token ceiling per phase; when reached, stop and report the flow so far.

### 4.8 Cost and run discipline

No model run on the owner's key without a go-ahead for that run (README). Pilot about 20 sources
through all phases and measure tokens per source screened, per site extracted and per accepted entry
before the full run; expect a multi-agent run to cost about 15 times one agent's pass (§1.1). Stay
within 16 concurrent and 1 000 agents per run, and treat the 25-agent warning as the moment to check
the pilot's extrapolation. Use a smaller model for screening and site finding, a stronger one for
specification and review, and record model ids per field. Log prover time per entry, as
[note §7.3 (v)] asks of the main pipeline.

### 4.9 What the protocol does not settle

Whether agent screeners reach acceptable recall on proof sources (§4.7 measures it only afterwards);
how to judge a move's generality across provers (a translation is a new artefact and must pass
G3-G5); and whether AFP and seL4 licences allow storing excerpts or only pointers.

---

## 5. Not verified in this survey

RACE and FACT as DeepResearch Bench's method names and its per-system figures [S]; DeepTRACE's
per-system rates and DeepHalluBench [S]; Petersen et al., Zhang et al. and the capture-recapture
literature [S]; otto-SR [S]; Freitas and Whiteside's entry fields [U]; the Isabelle Cookbook and QED
at Large [S]; Mathlib library notes [S]; AFP and Mathlib licences [U]; miniF2F-v2's count of
corrected statements [S]. Anthropic and Claude Code passages come from a fetch tool that returns
extracts, and quotations are limited to the sentences it returned.
