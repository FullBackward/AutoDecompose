# The decomposition library

Real decompositions and formalisation skills from large proving projects and
harnesses, each with its code copied whole and a specification of why it is
good. Start at [INDEX.md](INDEX.md), which lists every entry by move.

The plan behind the library is `docs/library-plan-2026-11-12.md`; the rules
the harvest follows are in [protocol.md](protocol.md).

## Reading an entry

Each entry is a directory `entries/<id>/`:

- `README.md`: the entry itself. The decomposition is shown inline, copied
  verbatim from the source; then the claims for why it is good, when to use it
  and when not, its consequences, and the verification record.
- `code/`: every file the entry draws on, copied whole and unmodified at the
  pinned commit, under its original path. Open these to read the code in full.
- `entry.json`: the same content in machine-readable form (sites with line
  ranges and permalinks, claims, licence, provenance).

Each source has a note, `sources/<id>/SOURCE.md`, with the upstream link, the
pinned commit, the detected licence and the licence text copied from upstream.

An entry id reads `<language>-<move>-<source>-<hash>`, for example
`lean-induction-compfiles-1a2b3c4d`.

## Status

| Status | Meaning |
|---|---|
| draft | extracted; claims not yet checked |
| verified | files re-fetched and byte-identical at the commit; the source's build passes or its CI covers the file; every claim has a verdict and none is refuted |
| accepted | verified, with one claim backed by a check and one by another kind of evidence, and accepted under all three review lenses (correctness, generality, provenance and licence) |
| flagged | a problem was found; the reason is recorded |
| deprecated | kept for the record; superseded or withdrawn |

## Licences

Code is copied from every source whatever its licence (owner's decision,
protocol §2). Each entry and each source note records the licence. The
library therefore mixes licences, including copyleft (GPL, LGPL, CC-BY-SA),
non-commercial (CompCert) and unknown ones. Before the repository is published,
entries whose licence is not permissive must be reviewed; `INDEX.md` shows
the source of each entry and `sources/<id>/SOURCE.md` its licence.

## Layout

```
library/
  INDEX.md            generated list of entries
  protocol.md         the harvest rules
  sources/<id>/       one note and licence copy per source; start-set.json
  entries/<id>/       README.md, entry.json, code/
  checks/<id>.json    verification and review records (append-only)
  ledger/*.jsonl      queries, candidates, sources, screening, sites, verdicts (append-only)
  reports/            flow, coverage, duplicates
  tools/              the scripts every agent uses (Python standard library)
  gold/               hidden gold standards per run (harvest agents must not read)
  cache/              disposable, git-ignored: files fetched only for searching
```

The swarm that fills the library is the saved workflow
`.claude/workflows/harvest-library.js`; the roles it uses are defined in
`.claude/agents/harvest-*.md` and their procedures in
`.claude/skills/harvest-decompositions/`.

## Tools

Run each with `library/tools/py.sh library/tools/<tool>.py ...` (it finds a
Python 3 interpreter). No tool uses an API token or a model.

| Tool | Does |
|---|---|
| `register_source.py` | pins a source's commit with `git ls-remote`, copies its licence, writes its note |
| `list_files.py` | lists a source's files at the pinned commit |
| `fetch_file.py` | fetches files at the pinned commit into the cache, for searching |
| `ledger.py` | appends a checked record to a ledger |
| `new_entry.py` | creates an entry: copies whole files and inserts verbatim excerpts |
| `validate_entry.py` | checks an entry's structure, hashes and that its code blocks are verbatim |
| `check_provenance.py` | re-fetches an entry's files and compares bytes |
| `record_verdict.py` | records a check result, a claim verdict or a review decision |
| `set_status.py` | promotes or flags an entry, refusing when a gate is not met |
| `dedupe.py` | finds duplicate entries |
| `build_index.py` | writes `INDEX.md` and `reports/flow.md` |
| `run_harvest.py` | runs one batch with DeepSeek workers (headless Claude Code on DeepSeek's Anthropic-compatible API); config in `runs/<run>.json`, logs in `reports/<run>/`; `--smoke` checks the routing, `--dry-run` the plumbing |

Two ways to run a batch: the saved workflow `.claude/workflows/harvest-library.js`
(Claude workers, billed to the Claude plan), or `tools/run_harvest.py` (DeepSeek
workers, billed to the DeepSeek key in the git-ignored `.env.deepseek`). Both
use the same roles, skill, tools and gates.
