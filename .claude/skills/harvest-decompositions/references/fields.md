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
| `parent` | analyst | `{name, statement}`; the statement verbatim from the code; `null` for skills |
| `children` | analyst | list of `{name, statement, closed_by}`; `closed_by` names the tactic, lemma or sub-proof that closes it, verbatim where short |
| `applicability` | analyst | `goal_shape`: the shape of goal the move applies to (head symbol, quantifiers, recursion of the defined constants); `use_when`; `avoid_when` |
| `claims` | analyst | list of `{n, claim, evidence_kind, evidence}`; kinds per protocol §7; `evidence` is a locator (permalink with lines, URL with section and quoted sentence, or a tool output) |
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
