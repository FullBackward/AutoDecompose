# Declaration graph of each entry

`library/tools/features/feature_graph.py` reads every entry of the library and writes two files:

- `graphs.jsonl`: one line per entry, the declarations the entry names and the `uses` edges between them;
- `graph-features.jsonl`: one line per entry, 94 flat features computed from that graph and from `entry.json`.

All 229 entries appear in both files. 199 are in a prover language (lean 118, rocq 54, isabelle 27) and get a graph. The 30 entries in latex, markdown or python get the features read from `entry.json`; their code-derived features are null and `code_null_reason` is `not-prover-language`.

## What is measured and what is not

Everything here is syntactic. Two tiers of evidence are used.

- **T0**: read from `entry.json` (children, sites, shape). Some T0 fields were written by an analyst model during the harvest (`sites`, `shape`, the choice of children); they are data here, not judgements made by this tool.
- **T1**: computed from the copied source text by the lexer in `feature_graph_lex.py`.

A T1 edge `A uses B` says: an identifier token in the text of declaration A matches the declared name B under the rules of section "How a token is matched". It is a token-level mention. It is not a dependency recorded by the prover. A mention can be missed (the declaration is used through a notation, an instance, a hint database or `simp`) and a mention can be wrong (a local name or an unrelated library name has the same spelling). Section "Validation" gives measured rates.

**T2** would be the dependency graph of the elaborated terms. No prover toolchain is installed on this machine, so no T2 value is computed. Section "T2 design" says what it would take.

Each feature has a class:

- **goal**: computable from the parent's statement and the declarations it mentions, before any decomposition exists;
- **decomposition**: needs the children, the parent's proof or the sites;
- **meta**: bookkeeping, layout and quality flags.

One caveat applies to every goal feature. The copied files were chosen after the decomposition was known, and a declaration outside the copied files is invisible. A goal feature therefore counts mentions of declarations in the copied files only.

## Running it

```
PYTHONUTF8=1 python library/tools/features/feature_graph.py --all          # write both output files
PYTHONUTF8=1 python library/tools/features/feature_graph.py --check        # recompute, exit 1 if a file differs
PYTHONUTF8=1 python library/tools/features/feature_graph.py --self-test    # built-in cases of the lexer and resolver
PYTHONUTF8=1 python library/tools/features/feature_graph.py ENTRY_ID       # print the two records of one entry
PYTHONUTF8=1 python library/tools/features/feature_graph.py --decls ENTRY_ID    # declaration table of its copied files
PYTHONUTF8=1 python library/tools/features/feature_graph.py --explain ENTRY_ID  # the graph in readable form
PYTHONUTF8=1 python library/tools/features/feature_graph.py --report NAME  # coverage | glue | shape | sizes | audit-ids
```

`library/tools/py.sh` may replace `python`. The tool uses the Python standard library only, no network, no model, no random number and no clock. A full run takes about 15 seconds.

The output is a function of the entry directories. Records are sorted by entry id, keys are sorted, numbers are integers or ratios rounded to six decimals, the files are UTF-8 with `\n` line ends, and no absolute path or time is written. Two runs give identical bytes; `--all` and `--check` print the SHA-256 of each file.

Each record carries `extractor_version` and `input_digest`. The digest is the SHA-256 of: the bytes of `entry.json` with `\r\n` replaced by `\n`, one `\n`, and the SHA-256 values recorded in `entry.json` for the copied files, sorted and joined by `\n`. The line-end replacement makes the digest the same on a checkout that converts line ends (`.gitattributes` protects `code/` but not `entry.json`). A record whose digest no longer matches its entry is stale. `--check` also replaces `\r\n` in the committed output before comparing.

The full declaration table of the copied files is not committed (21,105 rows over the 199 entries). `--decls ENTRY_ID` prints it; it is as reproducible as the graph.

## `graphs.jsonl`

One record per entry:

| Key | Content |
|---|---|
| `id`, `extractor_version`, `input_digest`, `language` | as above |
| `graph_status` | `ok`, or `not-prover-language` (no graph). `no-prover-file` and `no-parent` are defined and do not occur in the present library |
| `files` | one row per copied file: `path`, `lang` (by extension, null if not a prover file), `used` (true when its language is the entry's), `dialect` (`lean4`, `lean3`, `rocq`, `isabelle`), `lines`, `decls`, `anomalies`, `bytes_match_recorded` (the file's SHA-256 equals the one in `entry.json`) |
| `nodes` | see below |
| `edges` | see below |
| `stats` | numbers about all declarations of the used files: `decls_total`, `decls_by_class`, `decls_anonymous`, `edges_total`, `edges_by_match`, `edges_ambiguous`, `parent_file` (`decls`, `index` of the parent among them) |
| `notes` | remarks, e.g. a child name that matches two declarations |

### Nodes

A node is one of five types.

| `type` | What it is |
|---|---|
| `decl` | a declaration found by the lexer in a copied file |
| `local` | a line range inside one declaration that the entry names: a `have`, `obtain` or `assert` step, or a parent that is a goal inside a larger proof |
| `region` | a line range the entry names that is not inside one declaration: several declarations, a module doc comment, a command such as `Hint Resolve`, or a site in a file that is not a prover file |
| `external` | a name given by `entry.json` that no copied file declares |
| `subgoal` | a child with `"subgoal": true`; it has no name and is not a declaration |

Which nodes are in the graph of an entry:

1. the parent: the declaration whose name is `parent.name` and that overlaps the parent site (any declaration of that name when the entry has no parent site); failing that, the one declaration that starts inside the parent site (when several start there the site is a `region` node, `region-of-declarations`); failing that, the parent site as a `local` node when it lies inside one declaration, else as a `region` node; with no parent site and no declaration of that name, an `external` node;
2. every named child of `entry.json`: a declaration of that name that overlaps a child site of the same name, or, when no child site has that name, the best-matching declaration of that name. Failing that, when a site has the name: a `local` node if the site lies inside one declaration and its first three lines hold the name, otherwise an `external` node. Failing that, a `local` node at the first token of the name in the parent, when the parent binds the name (flag `extent-unknown`), else an `external` node. A subgoal child is a `subgoal` node; it takes the line range of a child site when the number of child sites no named child claims equals the number of subgoal children (they are paired in order, `resolution` says `subgoal+site-by-order`);
3. the declarations named by each skeleton and context site: those of the site's name that overlap it, else those that start inside it, else the site as a `local` or `region` node;
4. every declaration that starts inside a parent site and is neither the parent nor a child (role `skeleton`: it is part of the glue the entry shows);
5. every declaration of the copied files that one of the above uses directly;
6. every declaration that is reachable from one of the above and from which one of the above is reachable (it lies on a path between them).

Node keys:

| Key | Content |
|---|---|
| `n` | index of the node in `nodes`; edges refer to it |
| `type` | as above |
| `role` | `parent`, `child`, `skeleton`, `context` or `other`, the first that applies; `roles` lists all |
| `name` | full name: the written name prefixed by the enclosing Lean namespaces, Rocq modules or Isabelle locale; null for an anonymous declaration; for a `subgoal` the description from `entry.json` |
| `short` | the name as written |
| `kind` | the declaring keyword (`theorem`, `Lemma`, `definition`, `locale`, ...); null unless `decl` |
| `cls` | `theorem`, `definition`, `type`, `instance`, `assumption` or `other`; null unless `decl` |
| `defined` | false for `external` nodes and for sites outside the prover files |
| `path`, `lines` | copied file and first and last line |
| `stmt_lines`, `body_lines` | first and last line of the statement and of the body; the body of a theorem is its proof, the body of a definition is its right-hand side; the two ranges share a line when `:= by` ends the statement line; `body_lines` is null for a declaration without a body |
| `doc_lines` | lines of a Lean doc comment `/-- -/` or coqdoc comment `(** *)` directly above the declaration, else null; these lines are not part of `lines` |
| `site` | line range of the first site attached to the node |
| `resolution` | how the node was found: `name-exact`, `name-suffix` (the declared name is longer), `name-prefix` (the entry's name is longer), `name-last` (only the last component agrees), each with `+site` when the declaration overlaps the site; `site`; `in-parent-site`; `local`; `local-binding`; `region`; `region-of-declarations`; `site-not-in-prover-file`; `external`; `subgoal`; `subgoal+site-by-order`; null for role `other` |
| `child_index`, `child_indices` | positions in `entry.json` `children`; a node with role `child` and no index comes from a child site that no child names (flag `site-without-child`) |
| `container` | for a `local` node, the node of the enclosing declaration |
| `flags` | modifiers (`private`, `noncomputable`, `Local`, `Program`, `attr`), `aborted`, `unterminated`, `extent-unknown`, `site-without-child` |
| `scope` | the enclosing namespaces, modules or locale |
| `depth` | number of edges of the longest `uses` chain below the node among all declarations of the used files, cycles contracted |
| `depth_theorems` | the same, where every edge is a mention in a body and every node after the first is of class `theorem` |
| `n_desc` | number of declarations of the used files reachable from the node |
| `n_users` | number of declaring commands of the used files that use the node |
| `n_deps` | number of declarations of the used files the node uses |
| `recursive` | the declaration's text mentions its own name |
| `on_cycle` | the node lies on a cycle of `uses` edges: mutual recursion, or an artefact of name matching across files |

`depth`, `n_desc`, `n_users`, `n_deps` are computed on all declarations of the used files, not only on the nodes shown. They are stored on the node so that every feature can be computed from the record alone.

### Edges

| Key | Content |
|---|---|
| `s`, `t` | source and target node |
| `kind` | `uses`; `contains` (a declaration or region holds a `local` step or a declaration); `subgoal` (parent to subgoal child). Only `uses` edges carry the keys below |
| `where` | `statement`, `body` or `both`: where in the source the mentions stand |
| `n_stmt`, `n_body` | number of mentioning tokens in the statement and in the body |
| `line`, `col` | line and column of the first mention |
| `body_line`, `body_col` | line and column of the first mention in the body, else null |
| `match` | how the token matched: `exact`, `scoped`, `opened`, `file-qualified`, `suffix`, `field`, `last`, `local`, `external` (next section) |
| `via` | null, or what the token named: `head` (the token is `name.projection`), `def` (Isabelle `name_def`), `qualified` (Isabelle `name.simps`, `locale.fact`), `interpretation`, `constructor`, `field`, `mutual`, `assumption`, `intro-rule`, `shows-name`, `module-alias`, `token-suffix`, `axioms` |
| `amb` | number of candidate declarations at the level used |

How the edges of `local`, `region` and `external` nodes are made. A `local` or `region` node uses a declaration when a token of its line range matches it, by the rules of the next section applied inside the enclosing declaration; all such mentions count as `body`. The enclosing declaration keeps its own edges, which are computed from its whole text, local steps included. A mention of a `local` node's name counts for the innermost named step that holds the token and for the enclosing declaration, except that a mention inside another child's step counts for that step only; the tokens of the step's own range, its `have` line included, are not mentions of it. A node uses an `external` node when one of its tokens equals the external name, or one is a dotted suffix of the other, or the token starts with the name and goes on with projections.

Sizes: 4,360 nodes and 10,738 edges over the 199 graphs (10,665 `uses`, 36 `contains`, 37 `subgoal`). Median 13 nodes for lean, 31 for rocq, 15 for isabelle; the largest graph has 183 nodes.

## The lexer

### Masking

Comments and strings are blanked before anything else; offsets and line numbers do not change.

- Lean: `--` comments, nested `/- -/` comments (doc comments included), string and character literals.
- Rocq: nested `(* *)` comments, where a string inside a comment hides `*)` as it does for Rocq; string literals.
- Isabelle: nested `(* *)` comments. Each inner string `"…"` and cartouche `\<open>…\<close>` is classified by the word before it: after `text`, `section`, `\<comment>` and the like it is document text and is blanked; after `ML`, `setup` and the like it is ML text and is blanked; any other is inner syntax (terms and types). The outer syntax and the inner syntax are then two separate channels. An inner string that follows `::` is read as a type.

An Isabelle symbol `\<name>` is one opaque token. No symbol table is used. The symbol names given a meaning are: `open` and `close` (the cartouche delimiters); `comment`, `^marker`, `^cancel` (document markers); `subseteq` in `sublocale`; `proof`; nine binders, `forall exists nexists lambda And Sum Prod Union Inter`; and `in`, `le` as the end of a binder list. A declared name that contains a symbol (`\<theta>_upper_bound`) is matched as one run of symbols and identifier characters.

### Declarations

| Language | A declaration starts at | It ends |
|---|---|---|
| Lean 4 | a declaration keyword that is the first word of a line after attributes `@[…]` and modifiers: `theorem lemma def abbrev instance example structure class inductive opaque axiom`, and, when not indented deeper than the running declaration, `alias problem determine irreducible_def proof_wanted` | before the next declaration, or before the next command (`namespace section end variable open …`) that is not indented deeper |
| Lean 3 | the same keywords; a file is Lean 3 when it has a line `begin` or `:= begin` | the same; `end` closes a `begin` or `match` before it can close a scope |
| Rocq | a sentence (text up to `.` and white space) whose first word after attributes and `Local Global Program …` is `Theorem Lemma Corollary Proposition Fact Remark Property Goal Definition Example Fixpoint CoFixpoint Let Instance Function Equations Inductive CoInductive Variant Record Structure Class Axiom Parameter Conjecture Hypothesis Variable Context`, or `Notation`/`Abbreviation`/`Ltac` with an identifier, or `Canonical`/`Coercion` with `:=` | at the end of that sentence when it holds `:=` or declares a type or an assumption; else at `Qed`, `Defined`, `Admitted`, `Abort` or `Proof term.`; `Next Obligation` and a late `Proof.` extend the previous declaration |
| Isabelle | a theory-level command at the start of a line of the outer syntax: `lemma theorem corollary proposition schematic_goal lemmas definition abbreviation fun function primrec primcorec partial_function lift_definition inductive datatype codatatype type_synonym typedef record locale class instantiation instance interpretation sublocale consts axiomatization named_theorems method termination crunch declare …` | before the next theory-level command |

The span of a Lean declaration includes its attribute lines and a one-line prefix `set_option … in`, `open … in`, `omit … in`, `include … in`. It does not include the doc comment.

Statement and body are split as follows. Lean: at the first `:=` outside brackets, or `where`, or the first pattern-matching alternative `| … =>` at the start of a line; `structure`, `class`, `inductive` and `axiom` have no body. Rocq: at `:=` outside brackets for definitions, at the end of the first sentence for anything proved interactively. Isabelle: at the first of `proof by apply using unfolding supply including sorry oops done . ..` for proved statements, at `where` for definitions and functions, at `=` for `lemmas`.

Names. `namespace`/`end` (Lean), `Module`/`End` (Rocq) and `locale`/`context … begin`/`(in loc)` (Isabelle) prefix the name. `section` does not. `_root_.` is honoured. An anonymous `instance`, `example`, `Goal` or unnamed Isabelle `lemma` has `name` null and can only be the source of an edge. A command that declares several names (`Variables a b`, `alias ⟨a, b⟩`, `fun f and g`) gives one row per name with the same span. A Rocq inductive provides its constructors, a record its fields and constructor, a fixpoint its `with` partners; an Isabelle datatype provides its constructors, a record its fields, an inductive predicate its rule names, a locale its assumption names, a statement its `shows name:` names. A token that matches a provided name gives an edge to the providing declaration, with `via` saying which.

What could not be resolved is recorded, not guessed: `files[].anomalies` lists `end-without-scope`, `end-name-mismatch`, `proof-not-closed`, `proof-open-at-eof`, `proof-without-declaration`, `scope-open-at-eof`. The 487 file instances used have no anomaly.

### How a token is matched

A token is a maximal dotted identifier of the masked text of a declaration, the declared name's own occurrence excepted. Let the token have components `c1.….ck`. A declaration is a candidate when its full name ends with `c1.….ck`. The part of the full name the token leaves out decides the level.

| `match` | Rule | Languages |
|---|---|---|
| `exact` | nothing is left out | all |
| `scoped` | what is left out is a prefix of the using declaration's own namespace path; for Isabelle its locale or a locale that locale imports (`locale a = b + …`, `sublocale`) | all |
| `opened` | what is left out is named by an `open` (Lean) or `Import` (Rocq) of the using file; the extent of the `open` is not tracked. A macro `x_open "A B"` is read as `open A B` | lean, rocq |
| `file-qualified` | the token carries the file name before the full name | rocq, isabelle |
| `suffix` | anything else: the name lives in a module or locale the text does not show to be open | rocq, isabelle |
| `field` | `x.f` or `(e).f` where `x` is bound or lower-case: `f` is the last component of a declaration in some namespace. The written type of `x` in the header or in a `variable` command selects among candidates | lean |
| `last` | a qualified fact `p.f` whose prefix names nothing known or is bound in the proof (`interpret p: loc`): `f` is the last component of a fact in a locale | isabelle |
| `local` | the token is the name of a `local` node of the same declaration | all |
| `external` | the token agrees with a name of `entry.json` that no copied file declares | all |

Only the best level found is used. `exact`, `scoped`, `opened` and `file-qualified` are the strong levels: among several candidates the nearest one declared before the user in the same file wins, else the last one of the first other file in path order. `suffix`, `field` and `last` are the weak levels: every candidate gets an edge and `amb` counts them. A declaration made later in the same file is never a candidate. A `Variable`, `Hypothesis`, `Context`, `Let` or `Notation` of a Rocq section is a candidate only up to the end of that section; a declaration ended by `Abort` is never one.

Further rules:

- Lean: `a.b.c` is tried whole, then `a.b` and `a` with the rest read as projections (`via: head`). A one-component token in a fixed list of tactic words (`ext`, `symm`, `rfl`, …) is not matched when every occurrence opens a line or follows `by`, `;`, `<;>`, `·`, `|`, `(`.
- Rocq: a token whose head is a module alias (`Module M := N.`) is matched under `N`. A one-component token in a fixed list of tactic words (`set`, `case`, `split`, …) is not matched when every occurrence opens a sentence.
- Isabelle: outer tokens name facts, inner tokens name terms and types. `foo_def` names the definition `foo`; `t.simps`, `loc.fact` name the declaration `t` or `loc`; `p.fact` with `p` an interpretation of a locale in the copied files names that locale's fact. The name after `case` names a constructor or rule. In a type string a type's own name is preferred, in a term string a field or constructor of that name.

### Bound names

A one-component token that the using declaration binds is not a mention. The set of bound names is flat; it has no scopes.

- Lean, hard: the binder groups `(x y : T)` of the header, section `variable`s in scope, binders after `fun ∀ ∃ ∑ …`, names introduced by `intro rintro obtain with case by_cases`, the patterns of match arms. Soft: the first `have`, `let`, `set`, `suffices`, `replace` of a name binds it only after its own definition (the lines indented deeper than the keyword), so in `have foo := foo x` the second `foo` is the global one.
- Rocq, hard: bare names and groups of the header, binders after `forall exists fun` when a comma or `=>` closes them, names after `intros`, SSReflect intro patterns after a tactic's `=>` (a name after `/` is a view, not a binder), variables of match branches. Soft: `have x`, `set (x := …)`, `pose x := …`, `assert (H : …)`, `… as x`, each until the end of its sentence.
- Isabelle: fact names `name:` and names after `note`, `interpret p:`; term names after `fixes fix for obtain define` and after a binder symbol.

## Features

`graph-features.jsonl` has one record per entry with the keys `id`, `extractor_version`, `input_digest`, `code_null_reason` and the 94 features below. Notation: P is the parent node; a *named child* is a child without `"subgoal": true`; a *declaration child* is a named child whose node has type `decl`; "uses" means a `uses` edge of the graph record. Coverage is the share of entries of that language with a non-null value; it is 0% for latex, markdown and python on every T1 feature and is given for all 229 entries in the last column.

`code_null_reason` is null, `not-prover-language` (30 entries), or `parent-not-in-copied-prover-files` (1 entry, a deprecated one whose parent is `TODO`).

| Feature | Type | Class | Tier | lean | rocq | isab. | all | Definition |
|---|---|---|---|---|---|---|---|---|
| `language` | cat | meta | T0 | 100 | 100 | 100 | 100 | `entry.json` `language` |
| `kind` | cat | meta | T0 | 100 | 100 | 100 | 100 | `instance`, `skill` or `anti-pattern` |
| `status` | cat | meta | T0 | 100 | 100 | 100 | 100 | `entry.json` `status` |
| `move` | cat | meta | T0 | 100 | 100 | 100 | 100 | `entry.json` `move`: the label, not a feature to predict it from |
| `scale` | cat | meta | T0 | 77 | 100 | 100 | 82 | `shape.scale`; null when the entry has no `shape` |
| `n_files` | int | meta | T0 | 100 | 100 | 100 | 100 | number of copied files |
| `n_prover_files` | int | meta | T0 | 100 | 100 | 100 | 100 | copied files with the extension of the entry's language |
| `n_sites` | int | meta | T0 | 100 | 100 | 100 | 100 | number of sites |
| `parent_statement_given` | bool | meta | T0 | 100 | 100 | 100 | 94 | `parent.statement` is not null; null when the entry has no parent |
| `n_children` | int | decomp. | T0 | 100 | 100 | 100 | 100 | number of children |
| `n_children_named` | int | decomp. | T0 | 100 | 100 | 100 | 100 | children without `subgoal` |
| `n_children_subgoal` | int | decomp. | T0 | 100 | 100 | 100 | 100 | children with `subgoal` |
| `n_children_stmt_null` | int | decomp. | T0 | 100 | 100 | 100 | 100 | named children whose `statement` is null (declared outside the copied files, by the analyst's account) |
| `n_sites_child`, `n_sites_context`, `n_sites_skeleton` | int | decomp. | T0 | 100 | 100 | 100 | 100 | sites of that role |
| `site_parent_lines` | int | decomp. | T0 | 99 | 100 | 100 | 95 | lines of the first parent site |
| `site_child_lines` | int list | decomp. | T0 | 100 | 100 | 100 | 100 | lines of each child site, in site order |
| `site_glue_share` | ratio | decomp. | T0 | 89 | 100 | 100 | 89 | `site_parent_lines / (site_parent_lines + sum(site_child_lines))`; null without a parent site or a child site |
| `site_children_same_file` | int | decomp. | T0 | 99 | 100 | 100 | 95 | child sites in the parent site's file |
| `site_children_before_parent` | int | decomp. | T0 | 99 | 100 | 100 | 95 | child sites in that file that end before the parent site starts |
| `site_children_inside_parent` | int | decomp. | T0 | 99 | 100 | 100 | 95 | child sites inside the parent site's line range |
| `shape_direct_lemmas` | int | decomp. | T0 | 77 | 100 | 100 | 82 | `shape.direct_lemmas`, as the analyst wrote it |
| `shape_depth` | int | decomp. | T0 | 77 | 100 | 100 | 82 | `shape.depth`, as the analyst wrote it |
| `parent_node_type` | cat | meta | T1 | 100 | 100 | 100 | 87 | type of the parent node |
| `parent_resolution` | cat | meta | T1 | 100 | 100 | 100 | 87 | `resolution` of the parent node |
| `parent_kind` | cat | goal | T1 | 97 | 100 | 100 | 86 | declaring keyword of P; null unless P is a declaration |
| `parent_class` | cat | goal | T1 | 97 | 100 | 100 | 86 | class of P |
| `parent_stmt_lines` | int | goal | T1 | 97 | 100 | 100 | 86 | lines of the statement of P |
| `parent_doc_lines` | int | goal | T1 | 97 | 100 | 100 | 86 | lines of the doc comment directly above P, 0 if none (Isabelle: always 0) |
| `parent_stmt_deps` | int | goal | T1 | 97 | 100 | 100 | 86 | declarations of the copied files mentioned in the statement of P |
| `parent_stmt_deps_definition` | int | goal | T1 | 97 | 100 | 100 | 86 | those of class `definition` |
| `parent_stmt_deps_type` | int | goal | T1 | 97 | 100 | 100 | 86 | those of class `type` |
| `parent_stmt_dep_depth` | int | goal | T1 | 97 | 100 | 100 | 86 | max over those declarations d of `1 + depth(d)`; 0 if there is none |
| `parent_lines` | int | decomp. | T1 | 99 | 100 | 100 | 86 | lines of P (declaration, local step or region) |
| `parent_body_lines` | int | decomp. | T1 | 97 | 100 | 100 | 86 | lines of the body of P; 0 without a body |
| `parent_users` | int | meta | T1 | 97 | 100 | 100 | 86 | `n_users` of P |
| `parent_deps` | int | decomp. | T1 | 97 | 100 | 100 | 86 | `n_deps` of P: declarations of the copied files P uses, in statement or body |
| `parent_body_deps_theorem` | int | decomp. | T1 | 97 | 100 | 100 | 86 | declarations of class `theorem` mentioned in the body of P |
| `parent_body_deps_definition` | int | decomp. | T1 | 97 | 100 | 100 | 86 | declarations of class `definition` mentioned in the body of P |
| `parent_body_deps_other` | int | decomp. | T1 | 97 | 100 | 100 | 86 | declarations of any other class mentioned in the body of P |
| `parent_body_theorems_unlisted` | int | decomp. | T1 | 97 | 100 | 100 | 86 | of `parent_body_deps_theorem`, those with role `other`: lemmas the proof cites that the entry lists neither as child nor in a site |
| `children_share_of_body_theorems` | ratio | decomp. | T1 | 89 | 98 | 96 | 80 | of `parent_body_deps_theorem`, the share with role `child`; null when the count is 0 |
| `parent_desc` | int | decomp. | T1 | 97 | 100 | 100 | 86 | `n_desc` of P |
| `depth_below_parent` | int | decomp. | T1 | 97 | 100 | 100 | 86 | `depth` of P: longest chain of mentions below P in the copied files, through declarations of any class |
| `depth_below_parent_theorems` | int | decomp. | T1 | 97 | 100 | 100 | 86 | `depth_theorems` of P: longest chain P, lemma, lemma, … where each is mentioned in the body of the one before |
| `n_children_decl`, `n_children_local`, `n_children_external` | int | decomp. | T1 | 100 | 100 | 100 | 87 | named children by node type |
| `children_class_theorem`, `children_class_definition`, `children_class_other` | int | decomp. | T1 | 100 | 100 | 100 | 87 | declaration children by class |
| `children_contained` | int | decomp. | T1 | 99 | 100 | 100 | 86 | named children P holds (`contains` edge): local steps of P, or declarations inside a region parent |
| `fanout_cited` | int | decomp. | T1 | 99 | 100 | 100 | 86 | named children P uses |
| `fanout_cited_with_skeleton` | int | decomp. | T1 | 99 | 100 | 100 | 86 | named children that P or a node of role `skeleton` uses |
| `fanout_cited_share` | ratio | decomp. | T1 | 86 | 100 | 100 | 79 | `fanout_cited / n_children_named`; null without a named child |
| `child_cite_counts` | int list | decomp. | T1 | 99 | 100 | 100 | 86 | per child, in `entry.json` order: number of tokens of P that mention it (statement and body); null for a subgoal child |
| `child_cite_total` | int | decomp. | T1 | 99 | 100 | 100 | 86 | sum of `child_cite_counts` |
| `child_cite_where` | cat list | decomp. | T1 | 99 | 100 | 100 | 86 | per child: `statement`, `body`, `both`, `none`; null for a subgoal child |
| `child_cite_order` | int list | decomp. | T1 | 99 | 100 | 100 | 86 | indices of the cited children ordered by line and column of the first mention in P |
| `cite_order_matches_listing` | bool | decomp. | T1 | 79 | 98 | 100 | 76 | `child_cite_order` is increasing; null with fewer than two cited children |
| `cite_order_matches_source` | bool | decomp. | T1 | 50 | 59 | 70 | 48 | the cited children, in citation order, have increasing first lines; null unless at least two are cited and all are declarations or local steps of one file |
| `children_in_parent_statement` | int | decomp. | T1 | 99 | 100 | 100 | 86 | named children mentioned in the statement of P |
| `child_child_edges` | int | decomp. | T1 | 99 | 100 | 100 | 86 | `uses` edges between two different named children |
| `child_chain_depth` | int | decomp. | T1 | 99 | 100 | 100 | 86 | longest chain of such edges, cycles contracted |
| `child_other_users` | int list | decomp. | T1 | 99 | 100 | 100 | 86 | per declaration child: `n_users` minus one if P (or the declaration containing a local P) uses it; null for any other child |
| `children_reused` | int | decomp. | T1 | 81 | 100 | 96 | 76 | declaration children with `child_other_users > 0`; null without a declaration child |
| `child_other_users_max` | int | decomp. | T1 | 81 | 100 | 96 | 76 | maximum of `child_other_users` |
| `children_same_file`, `children_cross_file` | int | decomp. | T1 | 99 | 100 | 100 | 86 | declaration children in the file of P, and in another file |
| `children_before_parent`, `children_after_parent` | int | decomp. | T1 | 99 | 100 | 100 | 86 | declaration children in the file of P that end before P starts, and that start after P ends |
| `child_gap_lines` | int list | decomp. | T1 | 99 | 100 | 100 | 86 | per declaration child before P in its file: lines strictly between the child's end and P's start; null otherwise |
| `child_gap_min`, `child_gap_max` | int | decomp. | T1 | 65 | 91 | 93 | 66 | extremes of `child_gap_lines` |
| `child_lines` | int list | decomp. | T1 | 99 | 100 | 100 | 86 | per child: lines of its declaration or local step; null for external and subgoal children |
| `child_body_lines` | int list | decomp. | T1 | 99 | 100 | 100 | 86 | per declaration child: lines of its body, 0 without one; null otherwise |
| `glue_lines` | int | decomp. | T1 | 86 | 100 | 96 | 79 | lines of P that are in no named child's span (a local child lies inside P) |
| `glue_share_lines` | ratio | decomp. | T1 | 86 | 100 | 96 | 79 | `glue_lines / (glue_lines + C)`, C the number of distinct lines in the spans of the named children that are declarations or local steps; null without such a child |
| `glue_body_lines`, `glue_share_body` | int, ratio | decomp. | T1 | 86 | 100 | 96 | 79 | the same with the body of P and the bodies of the declaration children; a local step or region counts whole |
| `children_shared_deps` | int | decomp. | T1 | 81 | 100 | 96 | 76 | declarations, other than P and the children, used by at least two declaration children |
| `stmt_shared_deps` | int | decomp. | T1 | 80 | 100 | 96 | 76 | declarations mentioned in the statement of P and in the statement of a declaration child |
| `stmt_new_deps` | int | decomp. | T1 | 80 | 100 | 96 | 76 | declarations mentioned in the statement of a declaration child and not in the statement of P |
| `stmt_dep_jaccard` | ratio | decomp. | T1 | 61 | 100 | 81 | 65 | `stmt_shared_deps` over the size of the union of the two sets; null when the union is empty |
| `graph_nodes`, `graph_edges` | int | meta | T1 | 100 | 100 | 100 | 87 | size of the entry's graph record |
| `files_decls`, `files_decl_edges` | int | meta | T1 | 100 | 100 | 100 | 87 | declarations of the used files and `uses` edges between them |
| `parent_file_decls`, `parent_file_index` | int | meta | T1 | 97 | 100 | 100 | 86 | declarations in the file of P and the position of P among them |
| `parent_edges_ambiguous` | int | meta | T1 | 99 | 100 | 100 | 86 | `uses` edges leaving P with `amb > 1` |
| `parent_edges_weak` | int | meta | T1 | 99 | 100 | 100 | 86 | `uses` edges leaving P at level `suffix`, `field` or `last` |
| `files_anomalies` | int | meta | T1 | 100 | 100 | 100 | 87 | anomalies recorded for the used files |

A row that names several features gives the lowest coverage among them. The exact per-feature table is printed by `--report coverage`.

Why a T1 feature is null on a prover entry. `parent_kind` and the other features of a declaration parent are null for the three Lean entries whose parent is a local step, a region or `TODO`. Features of declaration children are null when no named child is a declaration (tactic-scale entries whose children are local steps or subgoals). `child_gap_*` is null when no declaration child precedes the parent in its file. `cite_order_matches_source` needs two cited children in one file.

## Validation

Each number below is printed by `--report glue`, `--report shape` or `--report sizes`, except the hand audit.

### Against the Lean compiler

`gold-lean.md` reports a comparison of the Lean graph with dependency data that the Lean compiler
produced for all of Mathlib (7,189 files); `tools/features/feature_gold.py` makes it. With lexer 1.1.0,
89.6% of the arrows are also in the compiler data (91.6% when the source is a theorem), and the
graph has 84.8% of the arrows that a person wrote by name. By level: `exact` 94.8%, `scoped`
91.8%, `opened` 85.6%, `field` 80.1%. No such data was found for Rocq or Isabelle.

Lexer 1.1.0 changed four Lean rules after this comparison: fields, parent projections and
constructors are names of their type's row; a parent written in notation gives no projection; a
word is a tactic only after the first `by` of a body; for `x.f`, a named type of `x` that holds no
candidate removes the arrow. The tables below this subsection were made with lexer 1.0.0, except
where a line says otherwise. For Rocq and Isabelle the two versions give the same output.

### Against the library's glue check

`validate_entry.py --strict` requires that the text of the parent and skeleton sites cites every named child: the last dotted component of the child's name occurs as a whole word in a line of those sites, comments included. The graph was compared with that rule on the 753 named children of prover instances.

| | Count |
|---|---|
| Both say cited | 740 |
| Glue check says cited, graph has no `uses` edge from the parent or a skeleton node | 13 |
| Graph has such an edge, glue check does not | 0 |
| Agreement | 740 of 753 (98.3%) |

The 13 disagreements:

- 11 (one entry, `lean-interface-lemma-carleson-50fa619f`): the parent site is a block of API lemmas and the children are those lemmas. The glue check finds each child's name in the child's own declaration. The graph has a region parent with `contains` edges and no `uses` edge.
- 2 (`e3` in `lean-key-invariant-compfiles-f9a0ece2`, `h12` in `lean-key-invariant-seed-prover-ccd41e1d`): the child is a `have` step inside the parent. The glue check finds the name on the `have` line itself. No later token of the parent mentions the name.

Of the 740 children both cite, the first citing line is the same for 706. The 34 differences:

| Count | Reason |
|---|---|
| 13 | the glue check's first line is a comment, a doc comment or a string |
| 9 | the glue check's first line is the child's own declaration or `have` line |
| 7 | the glue check's first line is the parent's header: the parent's own name ends with the child's name (`Matroid.IsGood.isRegular` and five children `….isRegular`) |
| 4 | the glue check's first line is a `have name` that rebinds the child's name one line before the use (`have mem_extends … := mem_extends …`) |
| 1 | Isabelle: the earlier line holds a constant `ccbrt` in a term; the child is the lemma `ccbrt`, cited later as a fact |

### Against `shape`

For the 172 theorem-scale prover entries whose parent is a declaration:

| `shape` field | Compared with | Equal | Differences |
|---|---|---|---|
| `glue_lines` | lines of the parent declaration | 147 of 172 | 16: the site starts after the attribute or prefix lines; 8: the site starts at the doc comment; 1: the site also covers a helper declaration |
| `child_lines` | lines of each child declaration | 640 of 703 | 38: the site starts after the attribute or prefix lines; 10: the site starts at the doc comment; 13: the site shows only the statement; 1: the site covers one part of a locale; 1: the site includes a trailing blank line |
| `direct_lemmas` | `parent_body_deps_theorem` | 124 of 172 | T1 larger in 37, smaller in 11 |
| `depth` | `depth_below_parent_theorems` | 56 of 172 | T1 larger in 105, smaller in 11 |

The line counts differ only where a site and a declaration have different boundaries. `shape.glue_lines` and `shape.child_lines` are site lengths by definition (the validator checks exactly that), so these rows measure how often a site is exactly one declaration: 85% of parents, 91% of children.

`direct_lemmas` and `depth` do not measure the same thing as the T1 features. `direct_lemmas` counts the lemmas the analyst saw the proof use, including lemmas outside the copied files; `parent_body_deps_theorem` counts declarations of class `theorem` in the copied files that the body mentions, so it misses external children (3 of the 11 smaller cases), children that are definitions or locale assumptions (5), children cited by a helper or through `Hint Resolve` (2), and, in the last case, two lemmas the analyst counted that the copied files do not hold. It also counts lemmas the entry does not list (the 37 larger cases). `shape.depth` is "the longest chain you checked", a lower bound chosen by the analyst; the T1 depth is the longest chain the text shows. No entry was edited.

### Hand audit of edges

Two fixed samples were read by eye: per prover language, of the n sorted entry ids, the entries at positions ⌊n(2k+1)/8⌋ (sample *dev*) and ⌊n(4k+1)/16⌋ (sample *test*), k = 0..3. `--report audit-ids` prints both. In each entry the audited declarations are the parent and the first three named children that are declarations. For each, every `uses` edge the extractor gives was judged against the source line of its first mention, and missed edges were looked for in two ways. First, every token whose last component equals the last component of any name declared in the copied files and that has no edge was judged. Second, uses through notation were looked for: the statements and the shorter proofs were read, and the copied files were searched for notation declarations that stand for a copied-file declaration and the audited declarations for their symbols, each hit being checked by eye. A proof longer than about sixty lines was not read line by line, so a missed edge that leaves neither a matching token nor a declared notation symbol would not have been seen.

The dev sample was read while the resolver was still being corrected. The test sample was read once, with the resolver frozen. That frozen version is not the committed one: the committed `feature_graph_lex.py` differs from it by the two fixes listed below, a tie-break that changes no output, and comments. The test numbers of the frozen version are the estimate; the dev numbers show what was found and fixed.

| Sample, extractor | Declarations | Edges given | Correct | Wrong | Missed | Precision | Recall |
|---|---|---|---|---|---|---|---|
| dev, before fixes | 38 | 198 | 189 | 9 | 9 | 95.5% | 95.5% |
| dev, final | 38 | 197 | 191 | 6 | 7 | 97.0% | 96.5% |
| **test, frozen** | 41 | 265 | 265 | 0 | 10 | 100% | 96.4% |
| test, final | 41 | 269 | 269 | 0 | 6 | 100% | 97.8% |

By language:

| Sample, extractor | lean (given / wrong / missed) | rocq | isabelle |
|---|---|---|---|
| dev, before fixes | 58 / 6 / 1 | 70 / 2 / 5 | 70 / 1 / 3 |
| dev, final | 58 / 6 / 1 | 68 / 0 / 5 | 71 / 0 / 1 |
| test, frozen | 26 / 0 / 0 | 157 / 0 / 8 | 82 / 0 / 2 |
| test, final | 26 / 0 / 0 | 160 / 0 / 5 | 83 / 0 / 1 |

What the errors were:

- Wrong, dev: 6 Lean `field` edges in one Lean 3 entry: a token `x.f` with two to four candidate declarations `N.f` gets an edge to each and one is meant (these remain); 2 Rocq (a section variable declared later in the file; a section-local notation `H` against a local `pose H i`; both fixed); 1 Isabelle (`cl_state.simps` sent to the record field `cl_state` instead of the datatype; fixed).
- Missed, both samples: 13 of the 19 are uses through a notation whose definition is in the copied files (`I[X : Y | Z ; μ]`, `G / N`, `'Alt_T`, `≼`, `⋃`, `<-T->`, `\<theta>`, `\<T>`). These are not fixable at T1. The other 6 were fixed: an Isabelle datatype named only through `t.simps` or `case (C …)` (2, dev), a Rocq section variable hidden because `'M[R]_n` was read as a binder group (3, test), an Isabelle `interpret loc` without prefix read as a binding (1, test).

After the two fixes made after the test reading, the audited edges of the test sample changed in exactly four places (the four misses became edges) and those of the dev sample not at all.

Limits of the audit. The test sample has no wrong edge, but it holds only 26 Lean edges and few weak ones; the dev sample shows that weak edges are where the errors are. Edges were also sampled by level, 20 to 40 at regular intervals over all distinct edges of that level, with the final extractor:

| Level | Sampled | Correct |
|---|---|---|
| lean `exact` | 20 | 20 |
| rocq `exact` | 30 | 30 |
| lean `field` | 40 | 35 |
| rocq `suffix` | 20 | 20 |
| isabelle `suffix` | 20 | 17 |

Lean `scoped` (25 of 25), `opened` (12 of 12), rocq `scoped` (14 of 14), isabelle `exact` (30 of 30) and `last` (18 of 18) were sampled with an earlier version of the resolver. Weak levels are 14% of the edges between all Lean declarations of the copied files (2,493 of 17,817 with lexer 1.1.0), 0.7% for Rocq and 1.2% for Isabelle; among parent-to-child edges they are 30 of 380 for Lean, 1 of 262 for Rocq, 8 of 95 for Isabelle.

Recall is measured against what a reader can see in the text. Dependencies that leave no token (instances, coercions, `simp` sets, `auto` with hint databases, canonical structures) are outside it.

### Declaration table

All 79 audited declarations had the right name, kind, first line, last line and statement/body split.

For the files of the 24 audited entries an independent scan was run: every raw line whose first word, after attributes and modifiers, is one of the common declaration keywords. The scan found 3,774 lines. 3,764 have a row in the table. The other 10 are inside comments, which the table rightly skips. The table has 141 further rows of kinds the scan does not look for (`Notation`, `Canonical`, `Coercion`, `HB.instance`, `defs`). The scan checks starting lines only.

## Known failure modes

Misses (a real dependency with no edge):

- a use through a notation, an infix, a coercion, an instance, a canonical structure, `simp`, `auto`/`eauto` with hints, `omega`-like automation, `to_additive`, or any generated name (`foo.induct` when `foo` is not in the copied files, `crunch` lemmas, `Build_` constructors apart);
- a declaration outside the copied files: it cannot be a node unless `entry.json` names it;
- a local name that shadows a global one before the global one is used: the bound-name set is flat, so the global use is dropped too;
- Lean field notation on a receiver that is upper-case and not bound in the header or by a `variable` in scope;
- an Isabelle fact made available by an interpretation or sublocale declared outside the copied files, when several locales declare a fact of that name.

False edges:

- a local name that the binding rules do not see (a pattern variable of a form not listed, an implicit free variable of an Isabelle statement, the parameter on the left of an Isabelle `definition`) and that equals a declared name;
- Lean `field` edges: `x.f` gets an edge to every `N.f` of the copied files when the header gives `x` no named type (a type in notation, or a type that is a variable); `h.symm` then matches a project lemma `Foo.symm`. Measured on Mathlib, 1 `field` edge in 5 is not in the compiler data (`gold-lean.md`);
- `suffix` edges of Rocq and Isabelle: the name is in a module or locale the text does not show to be open;
- names that occur in two copied files: the first file in path order wins, the import relation between the copied files is not read, and this can create a cycle (`on_cycle`);
- an `open` or `Import` is applied to the whole file, whatever its extent.

Structure:

- a declaration keyword of a kind not in the tables is not a row, and its text is attached to the previous declaration when it is not a known command. `LEAN_OTHER` and `ISA_OTHER_CMDS` list the commands that end a declaration; project commands met in the corpus were added (`blueprint_comment`, `p2m_open`, `snip`, `alphabet`, `crunch`);
- identifiers inside comments and strings are never read; Isabelle document antiquotations (`@{thm foo}`) are therefore not mentions;
- a `local` node has the line range the entry's site gives it; the extent of a `have` is not parsed;
- Lean 3 files (9 file instances, 2 entries) are read with the Lean 4 rules plus `begin … end`.

## T2 design

T2 is the graph of constants that occur in the elaborated statement and proof term of each declaration. It needs each source built at its pinned commit with its own toolchain. Statements about tools in this section come from memory and are **unverified**; none was run.

| | Lean 4 | Rocq | Isabelle |
|---|---|---|---|
| Tool | a metaprogram over the environment: for each `ConstantInfo` of a module, `type.getUsedConstants` for the statement and `value?.getUsedConstants` for the body; existing extractors that do this: `lean-training-data` (`lake exe premises`), LeanDojo's `ExtractData.lean`, `jixia` | `coq-dpdgraph` on compiled `.vo` files; MetaRocq `tmQuoteConstant` when statement and body must be separated | `Thm_Deps.thm_deps` (Isar command `thm_deps`) for facts, `Term.add_consts` on `Thm.prop_of` for statements; `isabelle build -o export_theory` exports theorems with their dependencies |
| Commands (unverified) | `elan` installs the toolchain named in `lean-toolchain`; `lake exe cache get` when Mathlib is a dependency; `lake build`; `lake env lean --run Deps.lean Module` | `opam switch create` with the Rocq version of the source; `opam install coq-dpdgraph` and the source's dependencies; `make`; in a `.v` file: `From dpdgraph Require Import dpdgraph. Set DependGraph File "m.dpd". Print FileDependGraph M.` | the Isabelle release of the source; `isabelle build -d . -b Session`; then a theory with `ML ‹Thm_Deps.thm_deps …›` run through `isabelle server` (`session_start`, `use_theories`), or `isabelle export -x "*:theory/**"` after `-o export_theory` |
| Adds over T1 | names behind notation, field notation and `open`; instances and coercions; lemmas used by `simp`, `aesop`, `omega`; exact split of statement and proof; no shadowing errors | names behind notations, coercions and canonical structures; lemmas used by `auto` with hint databases; section variables after discharge; module functor instances | facts used by `simp`, `auto`, `metis`; locale and interpretation facts under their real names; constants behind syntax and abbreviations |
| Needs care | auxiliary constants (`_proof_1`, `match_1`, `eq_1`, `._simp_1`) must be folded into their parent; `private` names are mangled; the two Lean 3 sources need the Lean 3 toolchain and its export format | whether `dpdgraph` separates statement from body edges is not known to me; opaque proofs must be loaded; one opam switch per Rocq version | `thm_deps` reports named theorems of the derivation, at whatever proof-term level the session was built with; the l4v and AFP sessions need their own Isabelle versions |
| Cost | one build per source at its commit; with Mathlib a cache download of several GB per toolchain version | one switch and one full build per source; CompCert, VST, MetaRocq and mathcomp-based sources take from minutes to hours | one heap per session; l4v and large AFP sessions take hours |

The task named "the Isabelle Pool Server"; that tool was not examined here, `isabelle server` is what the row above assumes.

A T2 run would keep the node and edge schema of `graphs.jsonl`, add `tier: T2` to edges, and keep the T1 edge beside it so that the two can be compared: T1 precision and recall could then be measured on every entry, not on a sample.

## Not built

- The elaborated dependency graph (T2): no toolchain.
- The import relation between copied files. It would order the files and remove the cross-file artefacts counted under `on_cycle`.
- Scopes for bound names and for `open`. They would need a parser of the proof languages, not a lexer.
- A graph for latex, markdown and python entries. Their parents and children are prose or node labels; the eight latex entries that also copy `.lean` files have no declaration that `entry.json` names as parent.
- Statement-level structure, tactic histograms and move detectors: the sibling tool `feature_terms.py` owns those.
