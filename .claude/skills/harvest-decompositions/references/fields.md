# entry.json fields

`new_entry.py` fills the fields marked *tool*; the analyst fills the rest.
`validate_entry.py --strict` refuses any `TODO` left behind.

| Field | Filled by | Must hold |
|---|---|---|
| `id` | tool | `<language>-<move>-<source>-<8 hex>`; never reused |
| `kind` | tool (from flag) | `instance`, `skill` or `anti-pattern` |
| `status` | `set_status.py` only | `draft` until promoted |
| `title` | tool (from flag) | one line naming the move and the goal, e.g. "Strong induction on the gap for IMO 2024 P1" |
| `intent` | analyst | one or two sentences: what the decomposition achieves for the goal |
| `move`, `also_known_as` | tool; analyst | move from protocol §3; other names in other provers or papers |
| `language` | tool | from the file extension |
| `source` | tool | source id, URL, full commit, licence |
| `files` | tool | every copied file with size, SHA-256 and permalink |
| `sites` | tool | path, line range, role (parent, child, skeleton, skill-text, context), name, excerpt hash, permalink |
| `parent` | analyst | `{name, statement}`; the statement verbatim from the code, copied with `statements.py`, never retyped; `statement: null` with a `note` when the parent is a goal inside a larger proof rather than a declaration; `null` for skills |
| `children` | analyst | list of `{name, statement, closed_by}`; `name` is the declaration's identifier (a gloss goes in `note`, not in the name); `statement` verbatim from a copied file (copy it with `statements.py`), or `null` with a `note` when the lemma is declared outside the copied files; a subgoal made by a tactic (a case of a split, a direction of an iff, a link of a calc) carries `"subgoal": true` and a `note`, since it has no name the glue could cite; `closed_by` names the tactic, lemma or sub-proof that closes it, verbatim where short. `validate_entry.py --strict` checks, for instances in lean, rocq or isabelle, that each statement is verbatim (or null with a note) and that the parent or a `skeleton` site cites every child that is not a subgoal; skills and entries in markdown, latex or python are exempt, their statements being prose or node labels |
| `applicability` | analyst | `goal_shape`: the shape of goal the move applies to (head symbol, quantifiers, recursion of the defined constants); `use_when`; `avoid_when` |
| `claims` | analyst | list of `{n, claim, evidence_kind, evidence}`; kinds per protocol §7; `evidence` is a locator (permalink with lines, URL with section and quoted sentence, or a tool output). From the run after 2026-11-14, a `check` claim is one of the forms `declared(NAME, PATH, A-B)`, `cites(PARENT_SITE, NAME)`, `no_sorry(PATH, A-B)`, `count(NAME, N, PATH_GLOB)` or `lines(SITE, N)`, which `check_claims.py` decides without a model (protocol §7) |
| `shape` | analyst, theorem scale only | `{"scale": "theorem", "direct_lemmas": N, "depth": D, "glue_lines": G, "child_lines": [..]}`: the count of all lemmas the main proof uses directly (at least 2), the longest chain of project lemmas below the main theorem that you checked (at least 1), and the line counts of the sites: `glue_lines` is the number of lines of the parent site and `child_lines` those of the child sites in order, declaration included in each. `validate_entry.py --strict` recomputes both from the sites and refuses a mismatch, so give each child site its whole declaration and proof if the count is to measure the proof. Absent means tactic scale (protocol §3, "Scale") |
| `metrics` | analyst, when measurable | e.g. `{"parent_lines": .., "children": .., "children_closed_by_automation": ..}`; say how each was counted |
| `consequences` | analyst | obligations the move creates (exhaustiveness, side conditions, generalised hypotheses) and known failure modes |
| `known_uses` | analyst, reviewer | other places with the same move: permalinks or entry ids |
| `related` | analyst | related entry ids |
| `rule` | analyst | `{"f10_rule": N or null, "relation": "supports" | "contradicts" | "none"}`, against survey F §10 |
| `content_key` | tool | normalised hash of the site excerpts, for deduplication |
| `provenance_log` | tool, analyst | append `{field, agent_role, model, run, at}` for each field you wrote |

## Good claims and bad claims

- Good: "The parent `foo` is closed from the two children in four lines
  (lines 120-123)" (`check`, permalink).
- Good: "The authors split the lemma so that each part has a short proof:
  'we break this into two steps, each of which is routine' (blueprint, §3.2)"
  (`author-statement`, URL and quote).
- Good: "`bar_aux` is reused by 7 other lemmas in the repository (grep for
  `bar_aux` at the pinned commit)" (`measurement`, the search stated).
- Bad: "This is an elegant decomposition." (taste: put it in prose, labelled
  as opinion).
- Bad: "This technique is widely used." (no locator).
