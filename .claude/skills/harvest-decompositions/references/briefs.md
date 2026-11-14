# Brief templates

Every brief has four parts: objective, output, tools and sources, boundaries
(survey G §4). The lead fills the angle brackets. A worker sees its brief and
the files it names, nothing else.

## Discoverer

- **Objective**: find public <Lean|Rocq> repositories containing <kind of
  material>, by <strategy A: these search strings | strategy B: snowballing from
  these sources>.
- **Output**: one `ledger.py candidates` record per plausible source; one
  `ledger.py queries` record per search run. Return the number of candidates.
- **Tools and sources**: web search, web fetch, `ledger.py`; for B, the
  build files and READMEs of: <source ids>.
- **Boundaries**: do not register sources; do not open more than <N> pages;
  ignore forks; stop after <N> queries or two rounds with nothing new.

## Screener

- **Objective**: decide inclusion for sources <ids> under protocol §4.
- **Output**: one `ledger.py screening` record per source.
- **Tools and sources**: `list_files.py`, `fetch_file.py` (README, build
  file, up to <N> sample files).
- **Boundaries**: decide from the files, not from reputation; "unsure" is
  allowed with a reason.

## Site finder

- **Objective**: find up to <N> sites showing the moves <moves> in source
  <id>, directories <dirs>.
- **Output**: one `ledger.py sites` record per site. Return the count.
- **Tools and sources**: `list_files.py`, `fetch_file.py`, grep on
  `library/cache/<id>/files/`; the project's published structure first,
  in this order (protocol §6, phase 2b, amended 2026-11-14):
  - a source with a blueprint: list sites from the `\uses{}` graph first;
    every node with two or more `\uses` targets is a theorem-scale
    candidate; grep only after;
  - Mathlib `Archive/` and compfiles (one theorem per file): the file's main
    theorem is the candidate, its named lemmas the children;
  - the AFP and `l4v`: one shard per session (`ROOT`) and file, with a site
    budget scaled by size (one site per 400 lines, at least 3, at most 15)
    instead of a flat cap;
  - for a source the last gold standard missed, the critic's `next_batch`
    list in the last `reports/<run>/summary.json` is the work order.
- **Boundaries**: only the named directories; prefer small, clear, closed
  sites; do not create entries.

## Analyst

- **Objective**: create and specify library entries for sites <site records>.
- **Output**: entries under `library/entries/` that pass
  `validate_entry.py --strict`. Return the ids.
- **Tools and sources**: `new_entry.py`, `validate_entry.py`, the source's
  files, its README, blueprint and papers for author statements.
- **Boundaries**: edit only the README.md and entry.json of entries you
  created; never edit `code/`; claims need locators.

## Verifier

- **Objective**: verify entries <ids>.
- **Output**: records through `check_provenance.py` and `record_verdict.py`.
  Return one line per entry.
- **Tools and sources**: the entry directory, the source at its commit, the
  evidence each claim points to.
- **Boundaries**: never edit an entry; "verified" only when you saw the
  evidence say what the claim says.

## Reviewer

- **Objective**: review entries <ids> under the lens <lens>.
- **Output**: one `record_verdict.py --review` record per entry.
- **Tools and sources**: the entry directory and its sources.
- **Boundaries**: one lens only; an objection says what would fix it.
