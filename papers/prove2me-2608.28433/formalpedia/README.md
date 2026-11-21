# Measures of the public Formalpedia export

Formalpedia is the public corpus of Prove2Me: theorem and definition cards in Lean 4, with the
proofs that the platform accepted. This folder measures the dependency arrows of that corpus and
compares them with the 198 declaration graphs of the library in `library/features/`. The findings
are in `../../formalpedia-and-library-splits-2026-11-21.md`.

## The data

| Item | Value |
|---|---|
| Repository | https://github.com/prove2me/formalpedia |
| Commit | `e7f2a230130f7899740f09aaffed4285afe150d4`, message "Snapshot 2026-11-21" |
| Snapshot time in `MANIFEST.json` | 2026-11-21T06:00:10 UTC |
| Environment | `envs/0df444a` (Lean v4.33.1, the default environment) |
| Files read | `graph-000.jsonl` to `graph-036.jsonl` (37 files) and `index-000.jsonl` to `index-023.jsonl` (24 files); 1.1 GB |
| Records | 3,632,901 arrows and 476,697 cards (360,328 theorems and 116,369 definitions), equal to the counts in `MANIFEST.json` |
| Licence | Apache 2.0 (`MANIFEST.json`, field `license`) |

The raw files are not in this repository, because of their size. `SHA256SUMS.txt` gives the hash
of each file. To get the same bytes again, download each file from

```
https://raw.githubusercontent.com/prove2me/formalpedia/e7f2a230130f7899740f09aaffed4285afe150d4/envs/0df444a/<file>
```

The repository makes a new snapshot each day, so the current files are different.

## The record formats

- **An arrow** is one line of a graph file: `{"parent", "child", "via"}`. The parent card imports
  the child card. `via` says where: `statement` when the import is in the statement of the parent,
  `solution` when a proof of the parent has the import, or the two together.
- **A card** is one line of an index file. It has the name, the status (`Definition`, `Proved`,
  `Open` or `Disproved`), the number of lines of the statement file, the time of creation, the
  author, a free-text source, and the list of accepted proofs. Each proof has a status
  (`ACCEPTED` or `SKETCH_ACCEPTED`), a type (`prove` or `disprove`), a number of lines, a time and
  an author.

One limit of the format is important. An arrow does not say which proof has the import. When a
theorem has two accepted proofs, the arrows of the two proofs cannot be separated.

## Files here

- `formalpedia_measures.py`: computes all measures. The module text defines each term.
- `measures.json`: the output for the snapshot above, with the same measures for the library.
- `MANIFEST.json`: the manifest of the snapshot, as downloaded.
- `SHA256SUMS.txt`: the hashes of the 61 raw files.
- `sample.jsonl`: a fixed sample of 300 accepted proof files. It is the first accepted proof of
  each 1,022nd proved theorem in the order of the names. Each line has the path of the file in
  the Formalpedia repository and the theorem cards that the arrows give as its children.
- `sample_proofs.py`: reads the 300 files and counts what the arrows cannot show: the helper
  lemmas that a proof file states for itself, and the imported cards that the proof text does not
  name.
- `sample-measures.json`: its output.

To get the 300 files, download line `i` of `sample.jsonl` (first line: 0) from the address above
with the path of that line in place of `envs/0df444a/<file>`, and save it as `000.lean`,
`001.lean` and so on. Then run:

```
python -I -X utf8 sample_proofs.py sample.jsonl <directory with the 300 files> --out sample-measures.json
```

To compute the measures again:

```
python -I -X utf8 formalpedia_measures.py <directory with the 61 files> \
    --library ../../../library/features/graph-features.jsonl --out measures.json
```

The script uses the Python 3.13 standard library only. It uses no clock, no network and no random
numbers. A sample in the script is "each n-th card in the order of the names". The script counts
authors and never writes a name of an author.
