# Tools of the library

Run a tool with `library/tools/py.sh library/tools/<tool>.py [arguments]`. `py.sh` finds a Python
interpreter and sets UTF-8. Each tool uses the Python standard library only. Each tool prints its
own instructions with `--help`.

## Why the folder has two levels

- **The harvest tools are in this folder and must stay here.** `library/protocol.md`, the agent
  definitions in `.claude/`, the workflow `.claude/workflows/harvest-library.js` and the records in
  `library/checks/` name these files. A check record is permanent, so the name of the tool that
  made it must stay valid. Do not move or rename a harvest tool. A change of that type needs a
  dated amendment of the protocol.
- **The feature tools are in `features/`.** They measure the entries. No protocol text and no
  record names them, so they have their own folder.

## Harvest tools, by task

| Task | Tool | What it does |
|---|---|---|
| Sources | `register_source.py` | Registers a source repository: pins a commit, copies the licence, writes the note |
| | `list_files.py` | Lists the files of a registered source at its pinned commit |
| | `fetch_file.py` | Fetches files of a registered source at its pinned commit into the cache |
| Entries | `new_entry.py` | Creates an entry: copies whole files without a change and makes the record |
| | `statements.py` | Copies the parent and child statements from the code; nobody types them again |
| Checks | `validate_entry.py` | Examines one entry, or all, against the rules of the library. No network |
| | `check_claims.py` | Decides the claims that a machine can check, without a model |
| | `check_provenance.py` | Fetches each copied file again at its pinned commit and compares the bytes |
| | `sorry_scan.py` | Records that no `sorry`, `admit`, `Admitted` or axiom closes a goal in an entry |
| | `dedupe.py` | Finds entries that are equal or almost equal |
| Records | `ledger.py` | Adds one record to a ledger. A ledger only grows |
| | `record_verdict.py` | Records a check result, a verdict on a claim, or a review decision |
| | `set_status.py` | Promotes, flags or deprecates an entry, and applies the gates of the library |
| Reports | `build_index.py` | Builds `library/INDEX.md` and the reports from the entries and the ledgers |
| | `status.py` | Shows the progress of a harvest run. It only reads |
| The run | `run_harvest.py` | Runs one harvest batch with DeepSeek workers. It costs money and needs the owner's approval |
| Shared | `common.py` | Paths and helper functions that the other tools import |
| | `py.sh` | Starts a tool with the correct interpreter |

## Feature tools: `features/`

| Tool | What it does |
|---|---|
| `feature_graph.py` | Writes `library/features/graphs.jsonl` and `graph-features.jsonl`: the declarations of each entry's copied files and the names that each declaration mentions |
| `feature_graph_lex.py` | The lexer and the name resolver that `feature_graph.py` uses, for Lean, Rocq and Isabelle |
| `feature_terms.py` | Writes `library/features/term-features.jsonl`: the form of each statement, the relation of each child to its parent, the proof steps, the move detectors |
| `feature_terms_lex.py` | The statement parser that `feature_terms.py` uses |
| `graph_viewer.py` | Writes `library/features/graph-viewer.html`, a page that shows the graph of each entry |
| `graph_viewer_template.html` | The page layout and script that `graph_viewer.py` fills |

`graph_viewer.py` imports `common.py` and `record_verdict.py` from this folder; the other feature tools
import only each other. `library/features/README.md` describes their outputs.
