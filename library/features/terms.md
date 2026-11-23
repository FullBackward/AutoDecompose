# Statement and proof-text features

`term-features.jsonl` holds, for each of the library's entries, what a program can read from the
inside of a statement and the inside of a proof: a skeleton of the parent and child statements,
how each child relates to its parent, the sequence of proof steps at each site, and the output of
fourteen move detectors. `library/tools/features/feature_terms.py` writes it from the entry directories
alone. No model, network, clock or random number takes part, so a second run gives the same bytes.

*Everything here is syntactic.* A "head", a "class" or a "detector" is a pattern over tokens. No
term is elaborated, no notation is resolved and no type is known. Section 1 says what that rules
out, Section 11 lists where it goes wrong, and Section 12 says what a prover would add.

The declaration-level dependency graph (which declaration uses which) is not in this file; it is
the sibling extractor's (`graph.md`).

## Contents

1. Tiers and feature classes
2. Running and reproducing
3. The record
4. How a statement is read
5. Statement features (the goal features)
6. Parent-to-child relation features
7. Proof-text features
8. Move detectors
9. The flat vector
10. What the results show
11. Failure modes
12. T2: what an elaborated-term export would add
13. Not built
14. Appendix: generated tables G1 to G12

Sections 4 to 9 define; Section 10 reads the tables of the appendix and reports the hand audit.
The appendix is printed by the tool (`--write-report`) and checked by `--check`, so its numbers
cannot drift from the data. Numbers quoted in the prose are those of extractor 1.0.1 on the 229
entries present on 2026-11-15; if they disagree with the appendix, the appendix is right.

## 1. Tiers and feature classes

A feature has a tier, which says where its evidence comes from.

- **T0**: read from `entry.json` (language, status, counts of children and sites, the `shape`
  numbers, lengths of prose fields).
- **T1**: computed from source text by the lexer and parser of `feature_terms_lex.py`.
- **T2**: would need the prover: elaborated terms, resolved notation, implicit arguments, types.
  No prover is installed on the extraction machine, and nothing in the output is T2.

A feature also has a class, which says when it is available.

- **goal**: computable from the parent statement and the file around it before any decomposition
  exists. These are the predictors. Flat names start with `g_`.
- **decomposition**: needs the children, the proof or the sites. These are outcomes. Flat names
  start with `d_`.
- **meta**: about the record or the extraction. Flat names start with `m_`.

Three consequences of working at T1 should be held in mind throughout.

(i) Lean's `→` is one token for implication and for the function arrow. The parser calls both
`arrow`; whether an `arrow` is a hypothesis is decided by position, not by type (Section 5).

(ii) Which binders are hypotheses is not known, since that is the question whether a type lives in
`Prop`. Two syntactic counts stand in for it, and neither is the true count.

(iii) Identifiers that no binder binds are called `consts`, but in Isabelle they include every free
variable, and in Lean and Rocq they include any variable whose binder is not in the statement or
in a `variable`-like command of the same file.

The prose fields of an entry (`intent`, `goal_shape`, `use_when`, `avoid_when`, `consequences`)
were written by a model. No feature is derived from their content; only their lengths are
recorded, as meta features.

## 2. Running and reproducing

```
PYTHONUTF8=1 python library/tools/features/feature_terms.py --all            # write term-features.jsonl
PYTHONUTF8=1 python library/tools/features/feature_terms.py ENTRY_ID         # print one record, indented
PYTHONUTF8=1 python library/tools/features/feature_terms.py --check          # exit 1 if a committed output differs
PYTHONUTF8=1 python library/tools/features/feature_terms.py --report         # print the appendix tables
PYTHONUTF8=1 python library/tools/features/feature_terms.py --write-report   # refresh the appendix in this file
PYTHONUTF8=1 python library/tools/features/feature_terms.py --self-test      # 97 built-in cases
```

`library/tools/py.sh library/tools/features/feature_terms.py ...` does the same. The tool needs Python 3.13
and the standard library; it imports only `feature_terms_lex.py`. It takes about 15 seconds.

The output is a function of the entry directories. Records are sorted by id, keys are sorted,
floats are rounded to six places, the encoding is UTF-8 and line ends are LF. No path outside the
entry, no time and no machine name is written. The run does not depend on directory order or on
`PYTHONHASHSEED` (checked with seeds 0, 1 and 12345).

Each record carries four version strings (`extractor_version`, `lex_version`,
`class_table_version`, `detector_version`) and an `input_digest`: SHA-256 over the bytes of
`entry.json`, then the recorded SHA-256 of each copied file, sorted, one per line. A row whose
digest no longer matches its entry is stale. Two points about the digest need saying.

- `entry.json` is checked out with CRLF line ends on a machine where git converts them (the
  extraction machine has `core.autocrlf=true`). The digest reads CRLF as LF, so it equals the
  digest of the committed blob on every checkout. The copied code files are exempt from conversion
  by `.gitattributes` and are hashed as they are.
- `files_ok` is true when every recorded file is present with its recorded hash. It is true for
  all 229 entries.

`--check` recomputes the JSONL and the appendix and compares. It compares the JSONL after reading
CRLF as LF, and says so when the two differ only in that; a checkout that converts line ends would
otherwise fail the check for no reason. I recommend adding `library/features/*.jsonl -text` to
`.gitattributes`; I have not edited that file.

Identifier characters are decided by Python's Unicode tables (`str.isalpha`), which belong to the
interpreter version. A different Python version could split an unusual character differently.

## 3. The record

One JSON object per line. Top-level keys:

| Key | Content |
|---|---|
| `id`, the four versions, `input_digest`, `files_ok` | identity and staleness |
| `t0` | fields read from `entry.json` (Section 9.3) |
| `parent` | `name`, and `statement`: the analysed parent statement (Section 5) |
| `children` | one object per child of `entry.json`, in order: `name`, `subgoal`, `site` (index of its child site, matched by equal names, or null), `statement`, `rel` (Section 6) |
| `relations` | entry-level aggregates of the `rel` objects (Section 6) |
| `sites` | one object per site, in order: `role`, `name`, `path`, `lines`, `n_lines`, `proof` (Section 7) |
| `glue` | the proof text the code detectors read (Section 8.1) |
| `detectors` | one object per detector: `fires`, `null_reason`, `signals` (Section 8) |
| `flat` | the flat vector (Section 9) |

Nothing is dropped silently. Every analysed object has `ok` and `null_reason`; when `ok` is false
the values are absent and the reason code says why. The codes:

| Object | Code | Meaning |
|---|---|---|
| statement | `no-parent` | `parent` is null in `entry.json` (skills) |
| statement | `statement-null` | the statement is null (a goal inside a proof, a lemma outside the copied files, a subgoal) |
| statement | `not-prover-language` | the entry is latex, markdown or python |
| statement | `not-verbatim` | the statement does not occur, whitespace aside, in any copied file; it is prose or a placeholder and is not parsed |
| statement | `empty-statement`, `unbalanced-brackets`, `binder-parse`, `empty-type`, `no-proposition` | the parser gave up: nothing to read, brackets do not match, the text between name and colon is not a binder list, nothing after the colon, an Isabelle statement with no quoted proposition |
| relation | `parent-statement-null`, `child-statement-null` | one side has no skeleton |
| site proof | `role-not-read` | context and skill-text sites are not read |
| site proof | `not-prover-text` | the file is not in the entry's prover language |
| site proof | `file-missing` | the recorded file is absent |
| site proof | `no-proof-text` | the site holds a statement but no proof step |
| glue, code detectors | `not-prover-language`, `no-glue-proof` | no proof step is available to read |
| other detectors | `no-site-read`, `not-lean`, `no-parent-site`, `no-child-statement`, `no-parent-statement` | the detector's input is missing |

Table G3 gives the rate of each code. On this corpus the five parser codes do not occur: every
statement that passed the verbatim filter was parsed. That is a statement about coverage, not
about correctness; Section 10.3 is about correctness.

## 4. How a statement is read

### 4.1 Tokens

Comments are blanked first, keeping offsets: Lean `--` and nested `/- -/`; Rocq and Isabelle nested
`(* *)` outside strings; in Isabelle also `\<comment> \<open>..\<close>`, the argument of the
document commands (`text`, `section` and the like), and `(* *)` inside a term. Isabelle's `(*)` is
the multiplication operator and is kept.

A token is an identifier, a numeral, a string, a symbol, or an opening or closing bracket, with
its line, column and bracket depth. The points where the three lexers take a decision:

- **Lean.** A dotted name is one identifier (`Nat.succ_le`, `h.1.le`, `.inl`, `Foo.{u}`).
  Subscript digits and combining marks continue an identifier. `ℕ+`, `ℝ≥0` and `ℝ≥0∞` are single
  identifiers. A non-ASCII operator absorbs subscript letters that follow it (`∈ᵢ`, `‖ₑ`), and an
  arrow absorbs `*` or `+` (`→*`, `≃+*`), so a bundled-map arrow is not read as an implication.
- **Rocq.** A qualified name is one identifier; a `.` followed by white space ends a sentence.
  `'X`, `'M`, `'Sym_T` are identifiers. `%nat`, `%:R` are scope tokens and are ignored. `\in`,
  `\sum_` are symbols. `[<=]` (CoRN) is one symbol. `<-T->` is one symbol.
- **Isabelle.** Outer syntax: a string or cartouche is one token whose content is lexed again as
  inner syntax. `\<name>` is one opaque token named by its name. A symbol joined to an identifier
  by an underscore belongs to it (`inv_\<alpha>_ostore`); `\<^sub>` and what follows it belong to
  the token before. No symbol table is used: a Greek letter and an unknown operator are both
  opaque symbols. The names given a meaning are the connectives, binders, relations and bracket
  pairs listed in `TERM["isabelle"]` and `ISA_OPEN`/`ISA_CLOSE`.

### 4.2 Declaration shape

The statement is cut into binders, hypotheses and conclusion.

- **Lean**: attributes and modifiers, a declaration word, a name, binder groups up to the first
  `:` at depth 0, then the type up to the first `:=` at depth 0 that does not belong to a `let`.
  Binder kinds: `(..)` explicit, `{..}` implicit, `⦃..⦄` strict-implicit, `[..]` instance.
  A statement with no declaration word is read as `name binders : type` or `binders : type` when
  the text before the colon is a binder list (`form` = `signature`), else as a bare term (`bare`).
- **Rocq**: the same, to the sentence-ending `.`. Kinds: `(..)` explicit, `{..}` and `[..]`
  implicit, `` `{..} `` instance, `(x := v)` let.
- **Isabelle**: `fixes` and `for` give binders (kind `fixes`); `assumes`, `if` and `when` give
  hypotheses; `shows`, or the propositions after the name, give the conclusion; `obtains x where P`
  gives an existential conclusion; `notes`, `defines`, `(is ..)` are skipped. Several `shows`
  propositions give a `multi` node.

When several declarations were recorded as one statement, only the first is parsed and `n_decls`
counts them (one entry: `lean-interface-lemma-carleson-50fa619f`, 11).

### 4.3 The skeleton

A term is parsed only as far as its logical layer. The result is a tree; `skeleton` in the record
is the node `stmt` with `binders` (kind `b`, slots `n`, class of the type `t`, head `h` when the
type is an application), `hyps` (trees) and `c` (the conclusion tree). Node kinds:

| Kind | Meaning | Fields |
|---|---|---|
| `forall`, `exists`, `exists-unique`, `lambda`, `bigop` | a binder and its body | `n` slots bound; `bounded` for `∀ x ∈ S`; `meta` for Isabelle `\<And>` |
| `arrow` | implication or function arrow, flattened: premises then conclusion | `meta` for Isabelle `\<Longrightarrow>`, with `\<lbrakk>A; B\<rbrakk>` split |
| `iff`, `and`, `or`, `not` | connectives, flattened when repeated | |
| `let`, `ite` | `let` binding and its body; the two branches of `if` | `n` |
| `rel` | the first relation at the top of what is left | `op`: eq ne le lt ge gt mem notmem subset dvd equiv modeq asymp entails other; `sym`; `chain` |
| `multi` | several Isabelle `shows` propositions | |
| `app`, `const` | an application of a head identifier, or one identifier | `h` head, `a` arguments |
| `var` | a bound name | |
| `expr` | a leaf with an infix symbol at its top | `h`: the loosest arithmetic operator, or the first symbol not in the arithmetic table with `u` = 1; `f`: the first identifier |
| `bracket` | a leaf that is one bracket group | `h` the bracket; `sb` = 1 for a comprehension |
| `triple` | Isabelle `\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>` | `h` the identifier between |
| `num`, `str`, `atom`, `prefix`, `empty`, `cut` | numeral, string, one symbol, a `match`/`case`/`by` form left unparsed, nothing, node budget exhausted | |

A head that is a bound name is not printed: the leaf gets `v` = 1, and `p.Prime` with `p` bound
becomes the head `.Prime`, since resolving it to `Nat.Prime` needs the type of `p`.

Precedence is fixed per language, loosest first:

- Lean: `↔`, `→`, `∨`, `∧`, then `¬`, then the first relation.
- Rocq: `->`, `<->`, `\/`, `/\`, then `~`, then the first relation.
- Isabelle: `\<Longrightarrow>`, `\<longrightarrow>`, `\<longleftrightarrow>`, `\<or>`, `\<and>`,
  then `\<not>`, then the first relation.

A binder, `let`, `if` or `match` takes everything to its right. A Lean or Rocq big operator does
not take a following relation (`∑ i ∈ s, f i = 1` is an equation); an Isabelle one does. A pair of
`‖` or `∥` bars encloses its content. Notations declared by a project are not known: a leaf that
contains one is an `expr` with `u` = 1, and its boundaries are right only if the notation does not
reuse a connective's token.

**Spine and core.** The *spine* of a conclusion is what is peeled from its top: universal binders,
premises of arrows, and `let`s, repeatedly. What remains is the *core*. `∀ n, P n → ∃ m, Q n m` has
one spine binder, one premise and the core `∃ m, Q n m`.

**Classes.** `node_class` of a node is its kind, with `rel:<op>` for a relation, `app` for `app`
and `const`, `false`/`true` for those constants, `set-builder` for a comprehension bracket.
`core_class10` folds the class of the core into ten values: `iff`; `and` (and `multi`); `or`;
`exists` (and `exists-unique`); `eq` (`rel:eq`, `rel:modeq`); `order` (le, lt, ge, gt); `mem` (mem,
subset); `neg` (`not`, `rel:ne`, `rel:notmem`, `false`); `app`; `other`.

## 5. Statement features (the goal features)

Each analysed statement has `skeleton`, `f` (the features below), `consts` (identifier to count),
`ctx_vars_used`, `fields`, `numerals`. The same analysis is applied to the parent and to every
child. Applied to the parent, the features are goal features, tier T1. Table G4 gives coverage:
192 of the 199 prover-language entries have them; the seven others have a null or prose statement.

| Feature in `f` | Type | Definition |
|---|---|---|
| `decl_kind` | string or null | the declaration word as written (`theorem`, `Lemma`, `problem`, `have`); null when there is none |
| `form` | string | `decl`, `signature`, `bare` or `labelled` (Section 4.2) |
| `n_decls` | int | declaration words at declaration position in the recorded text |
| `n_binder_groups` | int | binder groups before the colon; Isabelle: names after `fixes` and `for` |
| `n_bound_names` | int | slots those groups bind (`(a b : T)` is 2; `_` is a slot) |
| `n_explicit`, `n_implicit`, `n_strict_implicit`, `n_instance`, `n_let_binders` | int | slots by binder kind; Isabelle `fixes` count as explicit |
| `n_binders_prop_form` | int | binder groups whose type has class `rel:*`, `iff`, `and`, `or`, `not`, `forall`, `exists`, `exists-unique`, `false` or `true`. These are propositions by form. A hypothesis whose type is an application (`hA : A.Finite`) is not counted; a dependent function `f : ∀ i, α i` is |
| `n_binders_hyp_named` | int | explicit typed binder groups not counted above whose names all start with `h` or `H`, or that have no name. A naming convention, not a fact about types; not applied to Isabelle |
| `n_assumes` | int | Isabelle propositions under `assumes`, `if`, `when`; 0 elsewhere |
| `n_premises` | int | premises of arrows on the spine |
| `n_hyps` | int | `n_binders_prop_form` + `n_binders_hyp_named` + `n_assumes` + `n_premises`. The syntactic stand-in for the number of hypotheses |
| `n_spine_forall` | int | slots bound by universal binders on the spine |
| `n_bound_all` | int | `n_bound_names` + `n_spine_forall` |
| `concl_class` | string | class of the conclusion's root |
| `core_class`, `core_class10` | string | class of the core, and its ten-value fold |
| `core_head` | string | head of the core: the head identifier of an application, `rel:<op>` for a relation, else the class |
| `core_rel_sides` | [string, string] | when the core is a relation, the heads of its two sides |
| `family_key` | string or null | what two statements must share to count as the same conclusion form: `app:<head>` for an application whose head is not a bound name; `rel:<op>:<left head>:<right head>` for a relation unless both sides are a bound name, a numeral or an `expr` leaf; `triple`; null otherwise |
| `quant_prefix` | string | quantifier blocks met walking down the conclusion through binders and the right side of arrows, repeats merged: `A`, `E`, `AE`, `AEA`; empty when the conclusion starts with none |
| `quant_alternations` | int | largest number of changes between universal and existential binders along any path from the root, a binder under a negation or on the left of an arrow counted with the opposite kind. Under `iff` no flip is made |
| `n_forall`, `n_exists`, `n_exists_unique`, `n_lambda`, `n_let`, `n_ite`, `n_and`, `n_or`, `n_iff`, `n_not`, `n_arrow`, `n_rel` | int | nodes of each kind in the conclusion tree |
| `tree_size`, `tree_depth` | int | nodes and depth of the conclusion tree |
| `n_tokens`, `n_tokens_concl` | int | tokens of the statement after its name, and of the conclusion |
| `max_bracket_depth` | int | deepest bracket nesting |
| `n_set_builder` | int | comprehension forms: Lean `{x \| P}`, `{x : T \| P}`, `{x // P}`; Rocq `{x \| P}`, `{x & P}`, `[set x \| P]`; Isabelle `{x. P}`. A token pattern: a Rocq sigma type has the same form |
| `n_bigop` | int | big-operator tokens: Lean `∑ ∏ ∑' ∏' ∫ ∫⁻ ⨆ ⨅ ⋃ ⋂ ⨁ ⨂ ⨍ ∮ ∐`; Rocq `\sum_`, `\prod_`, `\big..`, `\int`; Isabelle `\<Sum> \<Prod> \<Union> \<Inter> \<Squnion> \<Sqinter> \<integral>` and `SUM PROD UN INT INF SUP` |
| `n_shows` | int | propositions in the conclusion (above 1 only for Isabelle) |
| `n_free_idents`, `n_free_ident_occurrences` | int | distinct identifiers, and occurrences, that are not keywords, sorts, or names bound anywhere in the statement. Binding is statement-wide: a name bound in one sub-term counts as bound in all |
| `n_ctx_vars` | int or null | of those, the ones bound by a section-level variable command in force at the statement's site: Lean `variable` under the `section`/`namespace` lines open there; Rocq `Variable(s)`, `Context`, `Hypothesis`/`Hypotheses` under the open `Section`/`Module`. Null for Isabelle and when the statement has no site |
| `n_consts` | int | `n_free_idents` minus the context variables. `consts` lists them with counts |
| `n_numerals`, `n_distinct_numerals` | int | numeral tokens |
| `n_sorts` | int | `Type`, `Prop`, `Sort`, `Set` tokens |
| `n_field_uses` | int | dotted suffixes on bound names (`x.re`, `p.Prime`), numeric projections excluded; `fields` lists them |
| `share_unknown_leaves` | float | share of leaves of the conclusion tree that carry unknown notation (`u`), a note, or are `cut`/`empty`/`prefix`. Meta |
| `truncated` | bool | the tree hit the budget of 400 nodes. Meta; false for every statement here |

## 6. Parent-to-child relation features

`children[i].rel` compares child `i` with the parent when both have a skeleton. All are
decomposition features, tier T1. 746 of 891 children have them (G2, G3).

| Feature | Type | Definition |
|---|---|---|
| `n_shared_consts`, `n_parent_only_consts`, `n_child_only_consts` | int | sizes of the intersection and the two differences of the `consts` sets |
| `jaccard_consts` | float or null | intersection over union of the `consts` sets |
| `introduces_consts` | bool | the child has a constant absent from the parent |
| `same_core_class`, `same_core_head`, `same_family_key` | bool | equality of those statement features, both non-null |
| `child_is_conjunct` | bool or null | the parent's core is a conjunction (or `multi`) and the child's core or whole conclusion equals one conjunct. Null when the parent's core is not a conjunction |
| `child_core_is_iff_side` | `lhs`, `rhs` or null | the parent's core is `A ↔ B` and the child's core equals `A` or `B` |
| `child_is_iff_direction` | `mp`, `mpr` or null | the parent's core is `A ↔ B`, the child's core equals `B` and `A` is among the child's hypotheses (`mp`), or the reverse (`mpr`). Hypotheses are binder types, Isabelle assumptions and spine premises |
| `child_core_in_parent` | bool | the child's core occurs token for token inside the parent's conclusion |
| `d_bound_all`, `d_hyps`, `d_tokens` | int | child minus parent |
| `more_bound`, `fewer_bound`, `more_hyps`, `fewer_hyps` | bool | signs of the first two differences. More binders in the child is the syntactic trace of generalisation; it is not a proof that the child is more general |
| `parent_numerals_absent` | int | distinct numerals of the parent that the child lacks |

"Equals" means equal token text after outer round brackets are dropped and each bound name is
replaced by `#0`, `#1`, .. in order of first occurrence. This sees through a renaming of bound
variables and nothing else: a reordered conjunction, an unfolded definition or a changed coercion
is a mismatch. The three exact-match features are therefore of low recall: across the corpus
`child_is_conjunct` holds in 3 entries and `child_is_iff_direction` in 2.

`relations` aggregates over the children: `n_children`, `n_children_stated` (with a skeleton),
`n_relations`; mean, minimum and maximum of `jaccard_consts`; the counts `n_same_core_head`,
`n_same_core_class`, `n_same_family_key`, `n_conjunct`, `n_iff_direction`, `n_iff_side`,
`n_core_in_parent`, `n_more_bound`, `n_fewer_bound`, `n_more_hyps`, `n_fewer_hyps`,
`n_introduce_consts`; `family_size`, the largest number of children that share one non-null
`family_key`, with `family_share` (that number over `n_children_stated`) and `n_family_keys`;
`name_common_prefix` and `name_common_suffix`, the longest common prefix and suffix of the
children's names in characters as a share of the shortest name (subgoals and names with spaces
excluded; T0, since it reads names only). When no child has relation features the counts and the
Jaccard values are null, not 0, and `relations.null_reason` is `not-prover-language` or
`no-relation`.

## 7. Proof-text features

`sites[i].proof` is computed for parent, child and skeleton sites in the entry's prover language.
All are decomposition features, tier T1. 919 of 1009 such sites have proof steps (G3); 20 hold a
statement only.

### 7.1 How heads are found

A *head* is the leading word of one proof step.

- **Lean 4.** Tactic blocks are found by layout. A head is the first token after `by`, after a
  bullet (`·`), after `;` or `<;>`, after a combinator (`try`, `all_goals`, `first`, ..), after the
  `=>` of a `case`, `next` or `|` arm, after `(` or `{` in head position, or the first token of a
  line that starts in the column of its block at the block's bracket depth. A line indented
  further is a continuation and has no head. `simp only` is one head. `rcases`, `obtain` and
  `rintro` whose pattern has a `|` become `rcases_alt`, `obtain_alt`, `rintro_alt`. A proof that
  does not start with `by` gets the pseudo-head `«term»`; `by` blocks nested in it are still read.
- **Lean 3** (two entries). Inside `begin .. end`, a head is the first token after `begin`, `,`,
  `;`, `<|>`, `{` or `by`.
- **Rocq.** The text is cut into sentences at `.` followed by white space; bullets, braces and
  goal selectors are dropped. Sentences between a theorem-like declaration and `Qed`, `Defined`,
  `Admitted` or `Abort` are tactic sentences unless they start with a vernacular word. A sentence
  is cut at `;` outside brackets, and each part gives the head of its first word: `move=>`,
  `move:`, `move/` are told apart; `by tac` gives the head of `tac`, `by []` gives `done`;
  combinators (`try`, `do`, `first`, `last`) are heads and the next word is read too; `(a; b)` and
  `[a | b]` (head `dispatch`) are entered; a `by tac` later in the part (`have H : P by tac`) is
  read. A definition with `:=` gets `«term»`.
- **Isabelle.** Every Isar command at bracket depth 0 is a head (`proof`, `have`, `show`, `by`,
  `apply`, `also`, ..). After `by`, `apply`, `proof` and `qed` the method expression is read: the
  first identifier of the bracket group and of each part after `,`, `;` or `|`. `by m1 m2` gives
  both. `simp only:` is `simp only`. `(use .. in \<open>m\<close>)` gives `use` and `m`.

### 7.2 Classes

Each head is given one of 25 classes by `CLASS_TABLE` in `feature_terms_lex.py`, version 1. Table
G12 prints the table as the extractor uses it. *The table is the main judgement in the extractor.*
Its calls that a reader might make differently:

- `automation` holds simplifiers, decision procedures and search (`simp`, `omega`, `linarith`,
  `auto`, `lia`, `blast`, `metis`), including normalisers that seldom close a goal (`norm_cast`,
  `field_simp`, `clarsimp`). `simp only`, `dsimp`, `unfold`, `cbn`, `simpl` are `rewrite`.
- `trivial-close` holds closers that do no search (`rfl`, `assumption`, `done`, `.`, `fact`).
- Isabelle's `standard`, `unfold_locales`, `intro_classes` are `automation`; `rule`, `intro`,
  `elim` are `apply`.
- Rocq `elim` is `induction`; `destruct`, `case`, `inversion` are `case-split` whether or not a
  pattern with alternatives follows.
- Lean `rcases` and `obtain` are `obtain` unless their pattern has an alternative.
- A head in no row is `unclassified`. The table was filled in from the heads that occur in this
  corpus, so the unclassified rates of G9 (0.2%, 0.5%, 0.2%) are in-sample; a new source will do
  worse.

### 7.3 Per-site features

| Feature | Type | Definition |
|---|---|---|
| `mode` | string | `tactic`, `term`, `equations` (Lean pattern-matching definition), `fragment` (a range inside a proof), `mixed`, `none` |
| `dialect` | string | `lean4`, `lean3`, `rocq`, `isar` |
| `n_decls` | int | declarations that start in the site |
| `n_lines` (on the site), `n_code_lines` | int | recorded lines; lines not blank after comments are removed |
| `n_tokens`, `n_body_tokens` | int | tokens of the site; tokens after the statement |
| `heads`, `classes` | lists | the head sequence and its classes, in source order |
| `n_heads`, `hist` | int, map | length of the sequence; class to count |
| `closing` | {head, class} or null | the closing step: Lean 4, the last head not inside brackets (in `exact f (by simp)` it is `exact`); Lean 3 and Rocq, the last head; Isabelle, the last of `by` (its last method), `qed` (its method if any), `done`, `.`, `..`, `sorry`, `oops` |
| `closes_by_automation_alone` | bool | heads of class `combinator`, `structure` and `facts` set aside, at least one head remains and all are `automation`. `by simp`, `using a by (auto simp: b)`, `Proof. lia. Qed.` qualify; `unfolding d by auto` does not |
| `closes_by_automation_or_trivial` | bool | the same with `trivial-close` allowed |
| `closing_is_automation` | bool | the class of `closing` is `automation` |
| `share_unclassified` | float | unclassified heads over heads. Meta |
| `n_sorry` | int | tokens `sorry`, `admit` (Lean); `admit`, `Admitted`, `give_up` (Rocq); `sorry`, `oops` (Isabelle), comments excluded |
| `n_api_attrs` | int | attributes and commands that register a lemma: Lean `@[simp]` and the like, `instance`; Rocq `Hint`, `Canonical`, `Coercion`, `Instance`; Isabelle `name[simp]`, `declare`, `lemmas`, `interpretation` |
| `info` | map | counts from the reader: `bullets`; `calc_steps` (Lean: steps after the first, lines led by `_` or `...`; Isabelle: `also` and `finally`); `arms`, `symbol_heads` (Lean); `by`, `alt` (Rocq: parts with an intro pattern holding `\|`); `apply`, `proof`, `qed`, `blocks` (Isabelle) |

`closing` is the last step in the text. It is not known to be the step that closes the last goal.

## 8. Move detectors

A detector is a predicate over an entry's code that says whether the syntactic signature of a move
is present. Detectors are not exclusive: a proof that inducts and then splits cases fires both.
A detector that fires on an entry labelled otherwise has therefore not made an error; it has found
a step that the analyst did not take to be the decomposition.

### 8.1 The glue

The seven code detectors read the *glue*: the proof steps and body tokens of the entry's parent
and skeleton sites, as `validate_entry.py` defines the glue. When those sites hold no proof step
(the parent site stops at `:= by`), the text from the parent site to the end of its declaration is
read instead and `glue.scope` is `declaration-extent`; this happens once. When there is still
none, `scope` is `none` and the code detectors are null; this happens once. `glue` also records
`n_heads`, `hist`, `info`, and `n_children_cited`: the children that are not subgoals whose name
occurs in the glue's body. A name occurs when its last dotted component is a whole dotted component
of an identifier in the body, so `foo.2`, `foo.mp` and `x.foo y` cite `foo` and `foo_aux` does not
(extractor 1.0.1; version 1.0.0 compared last components only and missed a lemma used through Lean
dot notation, in 8 entries). The count agrees with `glue_check` of `validate_entry.py` on 193 of the
195 prover-language entries that have children. The two that differ do so by definition: the
validator searches the whole text of the parent and skeleton sites, and this count searches proof
bodies. In `lean-interface-lemma-carleson-50fa619f` the parent site is the list of the eleven
lemmas themselves, and in `rocq-per-callee-lemma-coq-library-undecidability-683e3c0c` the children
are named by a `Hint Resolve` line and used by `eauto`; both count 0 here.

### 8.2 Definitions

Each detector reports its signals and fires by the rule given. "Name" signals test identifiers in
the glue's body, by their last dotted component unless said otherwise.

| Detector | Signals | Fires when |
|---|---|---|
| `induction` | `tactic`: a head of class `induction`. `nested-tactic` (Rocq): `induction` or `einduction` as a token not in head position. `recursor-name`: an identifier matching `induct` (not `inductive`), `rec`, `recOn`, `strongRec`, or in Rocq ending in `_ind`, `_rect`, `_rec`. `self-reference` (Lean): the parent's own name in its body | any signal |
| `case-split` | `tactic`: a head of class `case-split`. `nested-tactic` (Rocq): `destruct`, `inversion`, `inv`, `invcs`, `case_eq` and the like as tokens inside Ltac. `alt-pattern` (Rocq): an intro pattern with `\|`. `split-modifier` (Isabelle): `split:` in a method. `or-elim-name`: `Or.elim`, `Or.casesOn`, `orP`, `disjE`, `Classical.byCases` | any signal |
| `iff-split` | `goal-iff`: the parent's core class is `iff`. `constructor`: head `constructor` or `split`; Isabelle `iffI` or `standard`. `anon-pair` (Lean): `⟨a, b⟩` with one comma, directly after `:=`, `exact`, `refine`, `use`, `apply` or at the start of the body. `isar-directions`: a `next` and two `assume`. `iff-intro-name`: `Iff.intro`, `iff_def`, `iffI`, `iffP`. `antisymm-name`: a name containing `antisym`, or `eqn_leq`, `equalityI`, `eq_of_le_of_ge` | (`goal-iff` and (`constructor` or `anon-pair` or `isar-directions`)) or `iff-intro-name` or `antisymm-name` |
| `witness` | `goal-exists`: the parent's core class is `exists` or `exists-unique`. `tactic`: a head of class `witness` (`use`, `exists`, `eexists`, `existsi`, `instantiate`). `anon-constructor` (Lean): `⟨a, ..⟩` in the positions above. `exists-intro-name`: `exI`, `bexI`, `ex1I`, `ex_intro`, `Exists.intro`, `existT`, `exist`. `obtain-or-set`: an `obtain` head or `set`, `pose`, `define`, `let`; reported only | `tactic` or (`goal-exists` and `anon-constructor`) or `exists-intro-name` |
| `extensionality` | `tactic`: a head of class `ext` (`ext`, `ext1`, `funext`, `extensionality`). `ext-name`: Lean `ext`, `funext`, `ext_iff`, `hom_ext` and primes; Rocq `functional_extensionality`, `funext..`, `setP`, `ffunP`, `matrixP`, `polyP`, `fsetP`, `nat_trans_eq`; Isabelle `ext`, names ending in `_eqI`, `_eq_iff`, `_ext`, the record rule `.equality` | any signal |
| `calc-chain` | `calc-block`: a head of class `calc` (`calc`, `trans`, `transitivity`, `etransitivity`, `intermediate_path`, `also`, `finally`) or the token `calc`. `n-trans-names`: identifiers `trans`, `x_trans`, `trans_x`, `x_transitive`, `lt_of_lt_of_le` and the like. `calc-steps`, `longest-rewrite-run`: reported only | `calc-block` or `n-trans-names` ≥ 2 |
| `suffices-or-strengthen` | `tactic`: a head of class `suffices` (`suffices`, `wlog`, `suff`, `enough`, `cut`) or the tokens `suffices`, `wlog` | the signal |
| `sorrify-at-failure` | `sorry-token`: the sum of `n_sorry` over the parent, child and skeleton sites | above 0 |
| `blueprint-node` | `blueprint-markup`: occurrences of `\uses`, `\lean`, `\leanok` in copied `.tex` files and of `@[blueprint` in copied Lean files | above 0 |
| `statement-object` | `theorems-in-file`: `theorem`, `lemma`, `problem` declarations in the parent site's file (Lean only) | exactly 1 |
| `workflow` | `skill-kind`: `kind` is `skill`. `skill-text-site`: the entry has a `skill-text` site. T0 | either |
| `interface-lemma` | `api-attr-sites`: read sites with `n_api_attrs` above 0 | at least 2 |
| `per-callee-lemma` | `family-size`, `family-share` (Section 6) | size ≥ 3 and share ≥ 0.6 |
| `generalise-then-instantiate` | `generalising-child`: children with the parent's `family_key`, more bound slots than the parent, and a constant or numeral of the parent that the child lacks | at least 1 |

The thresholds of the last three (2; 3 and 0.6; 1) were fixed before their confusion rows were
computed and were not changed afterwards.

The lists of the first seven were revised once, after I read the first list of disagreements
(Section 10.1 says what changed). The confusion table is therefore not a held-out estimate.

### 8.3 Moves without a syntactic signature

Three moves have no detector, and for four others the detector above captures a part only. What
would define each, in my opinion:

- `key-invariant` (17 entries). The move is a property of use, not of form: one child that the
  main induction's step cites, or that many children cite. It needs the uses-edges of the
  declaration graph: a child with high in-degree among the children, or cited inside the scope of
  an induction head in the glue. The second half could be built at T1 from this file's head lines
  and the graph's citation lines together.
- `interface-lemma` (17). Attributes do not find it: `api-attr-sites` ≥ 2 holds for none of the 16
  readable labelled entries (G6). The entries are theorem-scale; "the client stops unfolding" is a
  negative property. A definition would need the graph (the children are all stated over one
  definition `D` of the entry's files) and a T1 test that the glue does not unfold `D`.
- `per-callee-lemma` (16). The family test fires on 5 of 15. The rest have children that differ
  in their conclusion head by design: one lemma per compiler pass or per constructor. A definition
  would pair the children with the constructors of an inductive type, or with the callees of a
  definition, both of which need the declaration table.
- `generalise-then-instantiate` (16). The relation test fires on 2 of 14. Whether a child's
  statement instantiates to the parent's is a unification question, hence T2.
- `suffices-or-strengthen` (19). The keyword finds 8. The other 11 strengthen by applying a
  stronger lemma, with no keyword; "stronger" is an implication between statements, hence T2. A
  T1 proxy would be a glue of few heads that ends by citing one child.
- `extract-have` (5). The signal is in history: a `have` in one revision and a lemma with the
  same statement in a later one. A snapshot does not show it.
- `statement-object` (2). One theorem per file holds for the 2 labelled entries and for 12 others
  (G6). The defining property is the import graph, which is the sibling extractor's.
- `other` (17). No definition.

## 9. The flat vector

`flat` repeats the features likely to be used as columns, with the class in the name. G4 lists
every key with its class, tier and coverage.

### 9.1 Goal features, `g_`

`g_<name>` is `parent.statement.f.<name>` for the names of Section 5 listed in `GOAL_FLAT`
(all of them except `n_decls`, `n_let_binders`, `core_rel_sides`, `n_free_ident_occurrences`,
`share_unknown_leaves`, `truncated`), plus `g_has_set_builder` (`n_set_builder` > 0),
`g_has_bigop` (`n_bigop` > 0) and `g_language` (T0). All are null when the parent has no skeleton.

`g_core_head` and `g_family_key` are strings of high cardinality; they are there for retrieval,
not as categorical predictors.

### 9.2 Decomposition features, `d_`

- From `relations`: every aggregate of Section 6, as `d_<name>`.
- From `t0`: `d_n_children_subgoal`, `d_scale`, `d_shape_direct_lemmas`, `d_shape_depth`.
- From the sites: `d_parent_site_lines`, `d_child_site_lines` (sums of recorded lines; T0);
  `d_parent_n_heads`, `d_parent_mode`, `d_parent_closing_class` (the first parent site with proof
  steps); `d_n_child_proofs` (child sites with proof steps), `d_child_heads_total`,
  `d_n_children_automation_alone`, `d_n_children_automation_or_trivial`, `d_n_children_term_mode`.
- From the glue: `d_glue_scope`, `d_glue_n_heads`, `d_glue_children_cited`, and `d_glue_n_<class>`
  for each of the 25 classes.
- From the detectors: `d_det_<detector>`, true, false or null.

The detector outputs are decomposition features: they read the proof. They must not be used to
predict the move from the goal.

### 9.3 Meta and T0

`m_status`, `m_kind`, `m_n_claims`, `m_prose_chars_goal_shape`, `m_prose_chars_intent` (T0);
`m_files_ok`, `m_parent_share_unknown_leaves`, `m_glue_share_unclassified` (T1).

`t0` holds more: `language`, `move` (the analyst's label), `status`, `kind`, `source_id`,
`n_files`, `n_sites`, `n_sites_by_role`, `n_children`, `n_children_subgoal`,
`n_children_statement_null`, `parent_statement_recorded`, `scale` (`theorem` when `shape` is
present, else `tactic`), `shape_direct_lemmas`, `shape_depth`, `shape_glue_lines`,
`shape_child_lines_sum`, `n_claims`, `n_claims_by_kind`, `rule_relation`, `rule_f10`,
`prose_chars` (length of each prose field), `n_also_known_as`, `n_known_uses`, `n_related`.
The `shape`, `claims` and `rule` values were written by an analyst model and are copied, not
checked.

## 10. What the results show

### 10.1 Detectors against labels (G5, G6, G7)

*Seven moves leave a trace in the code that a token pattern finds in most labelled entries; the
others do not.* For the 198 prover-language entries with glue:

| Detector | Fires on labelled | Fires on other | Reading |
|---|---|---|---|
| `induction` | 17 of 17 | 13 of 181 | found whenever labelled |
| `case-split` | 16 of 16 | 62 of 182 | found whenever labelled, and in a third of all other proofs |
| `witness` | 13 of 15 | 30 of 183 | |
| `iff-split` | 9 of 12 | 5 of 186 | |
| `extensionality` | 9 of 12 | 12 of 186 | |
| `calc-chain` | 16 of 22 | 28 of 176 | |
| `suffices-or-strengthen` | 8 of 19 | 10 of 179 | the keyword half only |
| `per-callee-lemma` | 5 of 15 | 7 of 168 | |
| `generalise-then-instantiate` | 2 of 14 | 8 of 168 | |
| `interface-lemma` | 0 of 16 | 6 of 183 | the attribute signature does not describe these entries |

The "precision" column of G5 treats the label as the truth about which steps occur, which it is
not: the label names one move per entry. `case-split` at 0.21 means that case analysis occurs in
78 glues and is the recorded decomposition in 16. For predicting the label the code detectors are
weak evidence when they fire and strong evidence when they are silent, `induction` and
`case-split` above all.

The split by status (G5) shows no clear difference between accepted and draft entries; the draft
counts are small (4, 4, 2, 6, 3, 3 labelled entries for the first six detectors of the table
above).

The silent cases are the informative ones. I read each of them in the source; G7 lists them.

- `iff-split`, 3 silent. Two entries are labelled `iff-split` and have no iff in the parent:
  `lean-iff-split-numina-putnam2025-95670702` proves a conjunction `IsGreatest .. ∧ IsLeast ..`
  by `constructor`, and `isabelle-iff-split-munkres-isabelle-05cdf9d1` states its two directions
  as two `shows` implications. In `rocq-iff-split-reglang-7747be2e` the iff is the project's
  notation `<-T->`, which the parser does not know.
- `witness`, 2 silent. `lean-witness-arklib-aa588c93` supplies its witness as an argument to a
  lemma, under a goal `≠ none`. `rocq-witness-unimath-e5043582` supplies an inverse map to
  `isweq_iso`; nothing in the syntax says "witness".
- `extensionality`, 3 silent. All three prove a pointwise statement with no extensionality rule:
  a goal stated with `pointwise_relation` (`rocq-extensionality-fourcolor-a5f0540e`), a measure
  equality `≡μ` unfolded by `move=> A mA` (`rocq-extensionality-mathcomp-analysis-fa807b35`), and
  an equality of tuples split by `injective_projections` (`rocq-extensionality-fiat-crypto-cb9f23da`).
- `calc-chain`, 6 silent. The chains are written without a chain keyword: nested applications of
  a composition lemma (`rocq-calc-chain-bedrock2-f158f24e`), a sequence of `have` steps
  (`lean-calc-chain-infinity-cosmos-933fc1d5`), runs of `rewrite` or `conv`
  (`rocq-calc-chain-abel-2c55660e`, `lean-calc-chain-sampcert-c1d1c12b`), a single `.trans_lt`
  (`lean-calc-chain-con-nf-9a04fb7d`), and `ssprove triangle`
  (`rocq-calc-chain-ssprove-54f699c2`).
- `suffices-or-strengthen`, 11 silent. Each proves its parent by applying a stronger or more
  general lemma (`apply X_of_Y`, `exact stronger ..`, `rule sim_imp_refines`). None uses
  `suffices`, `enough` or `wlog`. Isabelle has no such keyword, and all three Isabelle entries are
  silent.

The first version of the code detectors was silent on five more labelled entries. Reading them
showed four signatures that the protocol's signal table implies and my lists lacked, and I added
them: Isabelle's `split:` modifier; Rocq tactics nested in Ltac `match goal`; Isabelle rule names
`.equality` and `_eq_iff`; names with `transitive` beside `trans`. This moved `case-split` from 14
to 16 of 16, `extensionality` from 7 to 9 of 12 and `calc-chain` from 15 to 16 of 22; it added one
fire of `case-split` on an entry with another label and none for the other two. I also restricted
Lean's anonymous constructor to the positions where a term is given for the goal, which removed 2
fires of `witness` on other entries and none on labelled ones; putting Rocq's `instantiate` in the
`witness` class afterwards added 1. No list was changed to make a detector fire on an entry whose
code lacks the signature; the entries listed above are left as disagreements.

### 10.2 Do the goal features carry signal? (G8)

They carry some, for the moves whose definition mentions the goal's shape. No model was fitted;
G8 is a set of count tables. Among the 192 parents with a skeleton:

- core class `iff`: 13 entries, 9 of them labelled `iff-split`, and 9 of the 12 `iff-split`
  entries have it;
- core class `exists`: 33 entries, 12 labelled `witness`, and 12 of 15 `witness` entries have it;
- core class `order`: 23 entries, 11 labelled `calc-chain` (of 22);
- core class `eq`: 41 entries, spread over nine moves, 7 labelled `extensionality` (of 12).

`induction`, `case-split`, `key-invariant`, `interface-lemma`, `per-callee-lemma` and
`suffices-or-strengthen` show no concentration in any row of `g_core_class10`, and the hypothesis
and binder counts are flat across moves. With a median of about 12 entries per move the tables
cannot support a finer statement.

### 10.3 Hand audit

I compared the parsed skeleton of the parent statement and the head sequence of the parent site
with the source, by eye, for two samples of twelve. The rule: sort the ids of a language; with
`n` ids take the indices `floor(i n / 4)`, `i` = 0..3 (sample A), and `floor((i + 1/2) n / 4)`
(sample B). A skeleton is "right" when the binder groups, their kinds and counts, the hypotheses
and the tree of binders, connectives and relations agree with the text read with standard
precedence, and leaf heads are the leading identifiers. A leaf marked as unknown notation is not
an error if its boundaries are right.

Sample A was audited first and used to fix what it showed.

| Sample A (12 entries) | Right | Wrong or incomplete | Null |
|---|---|---|---|
| Skeleton of the parent statement | 11 | 1 | 0 |
| Head sequence of the parent site | 11 | 1 | 0 |
| Closing step | 11 | 1 | 0 |

The wrong skeleton: `rocq-per-callee-lemma-metarocq-861d7783`, whose conclusion
`∥.. e⊢ .. ⇓ ..∥` was read as a turnstile relation because the truncation bars were not treated as
a bracket. The incomplete sequence: one Isabelle method of 71 heads, inside
`(use .. in \<open>auto\<close>)`, was missed (`isabelle-calc-chain-afp-4d3178de`). The wrong
closing step: Lean's was reported as the `simp` nested inside the last `exact`
(`lean-induction-mathlib4-e5402126`). All three were fixed.

Sample B was audited after those fixes.

| Sample B (12 entries) | Right | Wrong or incomplete | Null |
|---|---|---|---|
| Skeleton of the parent statement | 11 | 0 | 1 |
| Head sequence of the parent site | 10 | 1 | 1 |
| Closing step | 9 | 2 | 1 |

The two nulls are correct nulls: the parent statement of
`isabelle-sorrify-at-failure-veriso-7de60ce6` is prose (`not-verbatim`), and the parent site of
`lean-suffices-or-strengthen-pfr-744a22ce` holds the statement only. The incomplete sequence:
`rocq-suffices-or-strengthen-hydra-battles-ffb3ec65`, where the three tactics inside `[trivial |
now apply ..]` were not read and the closing step was reported as `dispatch`. The other wrong
closing step: a Lean 3 proof's was reported as `any_goals`
(`lean-key-invariant-lean-liquid-01d1344d`), a regression from the fix made after A. Three
smaller errors were seen in B. `calc_steps` was 0 for a Lean 4 `calc` whose steps are on indented
lines (`lean-calc-chain-strongpnt-570bdcdb`). In `isabelle-case-split-autocorrode-5c995779` the
conclusion `case c of ..` is a `prefix` leaf, which is coarse but not wrong, and its pattern
variables are counted among the constants. In `rocq-other-math-comp-2c832601` the notation
`'Sym_T` is one identifier and hides the variable `T`. The dispatch, the Lean 3 closing step and
the calc count were fixed after B, and the fixes checked on the entries concerned; the last two
errors stand (Section 11).

Both samples have now been used for fixing, so the extractor as delivered has no held-out audit.
On the evidence of B before its fixes, I take the skeleton of a parsed parent statement to be right
about nine times in ten or better, with the errors at leaves that hold project notation, and the
head sequence to be right or nearly so, with errors in what counts as the closing step. Twelve
entries cannot fix those rates more closely than that.

### 10.4 Coverage and notation (G2, G3, G10)

Among prover-language entries the parent skeleton is null for 7 of 199: 5 statements that are not
code (4 deprecated Lean entries that hold `TODO`, 1 Isabelle statement in prose) and 2 that are
null by design (a goal inside a proof; a class instance). 42 child statements are null by design
(subgoals and lemmas outside the copied files) and 4 are prose.

G10 measures where notation defeats the parser. The mean share of conclusion leaves that hold
unknown notation is 0.06 for Lean parents, 0.06 for Rocq and 0.15 for Isabelle; the Isabelle
figure is high because every opaque symbol, a Greek variable included, is "unknown". The core
itself is an unparsed `expr` leaf for none of 113 Lean parents, 2 of 54 Rocq and 1 of 25 Isabelle.

## 11. Failure modes

Those I know of, the more consequential first.

(i) *Project notation.* A notation that reuses a connective's token is read as the connective.
Rocq's `∑` and `∏` are read as sigma and pi binders, which is right for UniMath and MetaRocq and
wrong where they are sums and products. `⇒` is read as an arrow in Rocq. A notation with a tag
inside (`<-T->`, `≡μ`, `e⊢`) is unknown. A mathcomp notation that absorbs a variable (`'Sym_T`,
`'M[R]_n`) hides it.

(ii) *Hypotheses.* `n_hyps` is not the number of hypotheses. It misses a hypothesis whose type is
an application and whose name does not start with `h` (`(pp : p.Prime)`), and it counts a function
argument on the spine of a conclusion as a premise.

(iii) *Constants.* `consts` holds free variables wherever the binder is out of sight: every free
variable of an Isabelle statement and every locale parameter; Lean auto-bound implicits; pattern
variables of `match` and `case .. of`; variables declared in another file. Isabelle symbols that
are constants (`\<MM>`) are not counted at all, since they are symbols.

(iv) *Binding is statement-wide.* A name bound in one sub-term and free in another is treated as
bound in both.

(v) *Field notation.* `x.foo` on a bound `x` gives `.foo`; the constant it denotes is not known.

(vi) *Lean layout.* A continuation line that starts in the column of its tactic block is taken for
a head; in this corpus about 15 of 10,400 Lean heads are of this kind. The arms of a term-mode
`match` inside a tactic block are read as tactics. `first` with alternatives on several lines is
read to its first alternative. Heads inside `conv` are classed as ordinary tactics.

(vii) *Rocq.* A tactic nested in Ltac `match goal` is not a head (two detectors read a short list
of such tactics as tokens). A project's own tactics are heads only if the table knows them. A `.`
followed by white space inside a term would end the sentence early; I have not seen one.

(viii) *Isabelle.* Methods inside a cartouche are read only after `use .. in`. The closing step of
a structured proof is `qed`, which says nothing. Which subgoal an `apply` acts on is not tracked.

(ix) *The closing step* is the last step in the text, not the step shown to close the last goal.

(x) *The glue is what the sites cover.* A narrow parent site hides steps from the detectors; a
wide one shows them steps that have nothing to do with the decomposition.

(xi) *Exact-match relations* (`child_is_conjunct`, `child_is_iff_direction`, `child_core_in_parent`)
miss any match that needs more than renaming bound variables.

(xii) *Child-to-site matching* is by equal names: 714 of 794 children in prover languages have a
site. A child without one gets no context variables and no proof features of its own.

(xiii) *Several declarations in one statement*: only the first is parsed (one entry).

(xiv) *The class table and the detector lists were written against this corpus.*

Entries whose data limit the features, listed and not edited: four deprecated Lean entries have
the statement `TODO`; `isabelle-sorrify-at-failure-veriso-7de60ce6` has prose for its parent and
four child statements; `lean-interface-lemma-carleson-50fa619f` records eleven lemmas as one
parent statement; twenty read sites hold no proof step: nine Lean, nine Rocq (eight child sites of
`rocq-per-callee-lemma-certicoq-2bfeffdd` and one `Hint` line) and two Isabelle.

## 12. T2: what an elaborated-term export would add

Everything in this section about what the tools do is stated from memory and is unverified; no
prover was run. Tool names and flags should be checked before any work is planned on them.

**What T2 would settle, in all three provers.**

(i) The sort of every binder, hence the exact hypothesis count and the exact reading of each
arrow as implication or function type.

(ii) The head constant of every sub-term, fully qualified, with notation, coercions, field
notation and implicit arguments resolved; hence a true constant multiset, and the separation of
constants from variables that T1 lacks for Isabelle.

(iii) The discharged statement: section variables, locale parameters and auto-bound implicits made
explicit binders.

(iv) Goal states at each proof step: how many goals a tactic leaves, and the statement of each.
That would give statements to the 33 children recorded as subgoals with a null statement, and
would turn "a `cases` head occurs" into "the step produced these cases".

(v) Exact uses-edges from proof terms, for the sibling's graph.

The export I would design is one term graph per statement (nodes: constants by qualified name,
binders with their sort, applications; edges: argument positions), written as JSONL keyed by
entry id with the toolchain version in each record. The features of Sections 5 and 6 would then be
recomputed on the graph with the same definitions, and the agreement of each T1 feature with its
T2 value would measure the T1 extractor directly.

**Lean 4.** A metaprogram run with `lake env lean --run` in the project can read each declaration's
`ConstantInfo`, open its type with `Lean.Meta.forallTelescope`, and report `BinderInfo` and whether
each binder's type is a `Prop`. Existing extractors that do some of this: LeanDojo (tactic states
and premises), `lean4export` (declarations in an exchange format), jixia (declarations, symbols
and elaboration data), the `lean-training-data` scripts, Pantograph. The cost is the build: each
source must be built at its pinned commit with its own toolchain. Projects on Mathlib can fetch a
build cache with `lake exe cache get`; others compile from source, which for the larger ones is
hours. The library has Lean entries from 40 sources, so my guess is a few tens of gigabytes of
disk and a day or two of machine time, most of it unattended. The two Lean 3 entries need the
Lean 3 community toolchain, which is no longer maintained.

**Rocq.** The cheapest step is not full elaboration. `coqc -dump-glob` writes, for every
identifier occurrence, the qualified name it resolves to; that alone would fix failure modes (i)
and (iii) for constants. Beyond that: `coq-lsp` (its `fcc` compiler can emit goals per sentence),
SerAPI (`sercomp`, `sertop`; S-expressions of terms; superseded by `coq-lsp` on recent versions),
Alectryon (goals per sentence), `coq-dpdgraph` (dependencies), MetaRocq's quoting. The cost is one
opam switch per version family: the 31 Rocq sources span Coq 8.x to Rocq 9, with their own pins of
mathcomp and the like. CompCert, fiat-crypto and VST each build in an hour or more. The `coqorg`
and `mathcomp` Docker images would shorten the setup.

**Isabelle.** `isabelle build -o export_theory` followed by `isabelle export` writes each theory's
constants and theorems with propositions as typed terms; `isabelle dump` writes PIDE markup, which
includes the entity each identifier refers to; `scala-isabelle` gives programmatic access to
terms; PISA (Portal to ISAbelle) gives the proof state at each step; `Thm_Deps` gives theorem
dependencies. The cost is the session build for 13 sources: AFP entries need the AFP release that
matches the Isabelle release, and l4v needs its own setup and, by repute, many hours and tens of
gigabytes of memory.

**Order of work**, were this taken up: Rocq `.glob` files first, since they need only a compile
and no plugin; then Lean projects with a build cache; Isabelle last. Each step should be costed on
one source before it is run on all.

## 13. Not built

- The declaration-level graph, uses-edges, fan-out, depth and reuse: the sibling extractor's.
- Any classifier or score. The task forbade one, and the corpus is too small to fit one honestly.
- Features from the prose fields, other than their lengths.
- Statements for subgoal children. They are in no file; they are goal states (T2).
- Section hypotheses as hypotheses of a statement. Which of them a statement uses is decided by
  elaboration in Lean 4 and by the proof in Rocq.
- Isabelle locale and context parameters. A locale's parameters may be declared in another file
  or inherited; resolving them is the prover's work.
- A generality relation between statements (does the child's statement instantiate to the
  parent's). It is unification, hence T2; `more_bound` and `same_family_key` are the T1 traces.
- Detectors for `key-invariant`, `extract-have` and `other` (Section 8.3).
- A third audit sample taken after the last fixes.

## 14. Appendix: generated tables

Printed by `feature_terms.py --write-report`; `--check` fails if this block is stale.

<!-- BEGIN GENERATED by feature_terms.py --write-report; do not edit by hand -->

Extractor 1.0.1, lexer 1.0.0, class table 1, detectors 1. 229 entries, 199 in a prover language.

### G1. Entries by language and status

| language | accepted | deprecated | draft | verified | total |
|---|---|---|---|---|---|
| isabelle | 10 |  | 17 |  | 27 |
| latex | 10 |  |  |  | 10 |
| lean | 82 | 4 | 31 | 1 | 118 |
| markdown | 1 |  | 16 |  | 17 |
| python |  |  | 3 |  | 3 |
| rocq | 51 |  | 3 |  | 54 |
| total | 154 | 4 | 70 | 1 | 229 |

### G2. Coverage: share of entries with a non-null value, by language

| feature group | isabelle | latex | lean | markdown | python | rocq | all |
|---|---|---|---|---|---|---|---|
| parent skeleton | 25/27 (93%) | 0/10 (0%) | 113/118 (96%) | 0/17 (0%) | 0/3 (0%) | 54/54 (100%) | 192/229 (84%) |
| parent core class | 25/27 (93%) | 0/10 (0%) | 113/118 (96%) | 0/17 (0%) | 0/3 (0%) | 54/54 (100%) | 192/229 (84%) |
| at least one child skeleton | 25/27 (93%) | 0/10 (0%) | 104/118 (88%) | 0/17 (0%) | 0/3 (0%) | 54/54 (100%) | 183/229 (80%) |
| at least one parent-child relation | 24/27 (89%) | 0/10 (0%) | 104/118 (88%) | 0/17 (0%) | 0/3 (0%) | 54/54 (100%) | 182/229 (79%) |
| parent-site proof steps | 27/27 (100%) | 0/10 (0%) | 113/118 (96%) | 0/17 (0%) | 0/3 (0%) | 54/54 (100%) | 194/229 (85%) |
| at least one child-site proof | 27/27 (100%) | 0/10 (0%) | 105/118 (89%) | 0/17 (0%) | 0/3 (0%) | 53/54 (98%) | 185/229 (81%) |
| glue for the code detectors | 27/27 (100%) | 0/10 (0%) | 117/118 (99%) | 0/17 (0%) | 0/3 (0%) | 54/54 (100%) | 198/229 (86%) |
| T0 features | 27/27 (100%) | 10/10 (100%) | 118/118 (100%) | 17/17 (100%) | 3/3 (100%) | 54/54 (100%) | 229/229 (100%) |

Per object rather than per entry:

| language | children with a skeleton | children with relation features | parent sites with proof steps | child sites with proof steps | skeleton sites with proof steps |
|---|---|---|---|---|---|
| lean | 400/433 (92%) | 400/433 (92%) | 113/117 (97%) | 390/395 (99%) | 4/4 (100%) |
| rocq | 263/266 (99%) | 263/266 (99%) | 54/54 (100%) | 238/246 (97%) | 0/1 (0%) |
| isabelle | 85/95 (89%) | 83/95 (87%) | 27/27 (100%) | 93/95 (98%) | n/a |

### G3. Null reason codes

| object | reason | isabelle | latex | lean | markdown | python | rocq | all |
|---|---|---|---|---|---|---|---|---|
| parent statement | (value) | 25 |  | 113 |  |  | 54 | 192/229 (84%) |
| parent statement | no-parent |  |  |  | 11 | 2 |  | 13/229 (6%) |
| parent statement | not-prover-language |  | 10 |  | 6 | 1 |  | 17/229 (7%) |
| parent statement | not-verbatim | 1 |  | 4 |  |  |  | 5/229 (2%) |
| parent statement | statement-null | 1 |  | 1 |  |  |  | 2/229 (1%) |
| child statement | (value) | 85 |  | 400 |  |  | 263 | 748/891 (84%) |
| child statement | not-prover-language |  | 35 |  | 49 | 13 |  | 97/891 (11%) |
| child statement | not-verbatim | 4 |  |  |  |  |  | 4/891 (0%) |
| child statement | statement-null | 6 |  | 33 |  |  | 3 | 42/891 (5%) |
| relation | (value) | 83 |  | 400 |  |  | 263 | 746/891 (84%) |
| relation | child-statement-null | 6 |  | 30 |  |  | 3 | 39/891 (4%) |
| relation | parent-statement-null | 6 | 35 | 3 | 49 | 13 |  | 106/891 (12%) |
| site proof | (value) | 120 |  | 507 |  |  | 292 | 919/1009 (91%) |
| site proof | no-proof-text | 2 |  | 9 |  |  | 9 | 20/1009 (2%) |
| site proof | not-prover-text |  | 35 |  | 30 | 5 |  | 70/1009 (7%) |
| glue | (value: declaration-extent) |  |  | 1 |  |  |  | 1/229 (0%) |
| glue | (value: sites) | 27 |  | 116 |  |  | 54 | 197/229 (86%) |
| glue | no-glue-proof |  |  | 1 |  |  |  | 1/229 (0%) |
| glue | not-prover-language |  | 10 |  | 17 | 3 |  | 30/229 (13%) |

Detector outcomes over all entries (a null outcome is named by its reason):

| detector | fires | silent | no-child-statement | no-glue-proof | no-parent-site | no-parent-statement | not-lean | not-prover-language |
|---|---|---|---|---|---|---|---|---|
| blueprint-node | 20 | 209 |  |  |  |  |  |  |
| calc-chain | 44 | 154 |  | 1 |  |  |  | 30 |
| case-split | 78 | 120 |  | 1 |  |  |  | 30 |
| extensionality | 21 | 177 |  | 1 |  |  |  | 30 |
| generalise-then-instantiate | 10 | 172 | 16 |  |  | 1 |  | 30 |
| iff-split | 14 | 184 |  | 1 |  |  |  | 30 |
| induction | 30 | 168 |  | 1 |  |  |  | 30 |
| interface-lemma | 6 | 193 |  |  |  |  |  | 30 |
| per-callee-lemma | 12 | 171 | 16 |  |  |  |  | 30 |
| sorrify-at-failure | 2 | 197 |  |  |  |  |  | 30 |
| statement-object | 14 | 103 |  |  | 1 |  | 111 |  |
| suffices-or-strengthen | 18 | 180 |  | 1 |  |  |  | 30 |
| witness | 43 | 155 |  | 1 |  |  |  | 30 |
| workflow | 15 | 214 |  |  |  |  |  |  |

### G4. Flat features: class, tier and coverage

| flat feature | class | tier | non-null, prover languages | non-null, all entries |
|---|---|---|---|---|
| `d_child_heads_total` | decomposition | T1 | 199/199 (100%) | 199/229 (87%) |
| `d_child_site_lines` | decomposition | T0 | 187/199 (94%) | 204/229 (89%) |
| `d_det_blueprint_node` | decomposition | T1 | 199/199 (100%) | 229/229 (100%) |
| `d_det_calc_chain` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_det_case_split` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_det_extensionality` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_det_generalise_then_instantiate` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_det_iff_split` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_det_induction` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_det_interface_lemma` | decomposition | T1 | 199/199 (100%) | 199/229 (87%) |
| `d_det_per_callee_lemma` | decomposition | T1 | 183/199 (92%) | 183/229 (80%) |
| `d_det_sorrify_at_failure` | decomposition | T1 | 199/199 (100%) | 199/229 (87%) |
| `d_det_statement_object` | decomposition | T1 | 117/199 (59%) | 117/229 (51%) |
| `d_det_suffices_or_strengthen` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_det_witness` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_det_workflow` | decomposition | T0 | 199/199 (100%) | 229/229 (100%) |
| `d_family_share` | decomposition | T1 | 183/199 (92%) | 183/229 (80%) |
| `d_family_size` | decomposition | T1 | 183/199 (92%) | 183/229 (80%) |
| `d_glue_children_cited` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_apply` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_automation` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_calc` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_case_split` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_combinator` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_constructor` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_context` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_contra` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_domain` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_exact` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_ext` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_facts` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_have` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_heads` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_induction` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_intro` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_obtain` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_rewrite` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_show` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_sorry` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_structure` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_suffices` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_term` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_trivial_close` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_unclassified` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_n_witness` | decomposition | T1 | 198/199 (99%) | 198/229 (86%) |
| `d_glue_scope` | decomposition | T1 | 199/199 (100%) | 199/229 (87%) |
| `d_jaccard_max` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_jaccard_mean` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_jaccard_min` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_child_proofs` | decomposition | T1 | 199/199 (100%) | 199/229 (87%) |
| `d_n_children` | decomposition | T0 | 199/199 (100%) | 229/229 (100%) |
| `d_n_children_automation_alone` | decomposition | T1 | 199/199 (100%) | 199/229 (87%) |
| `d_n_children_automation_or_trivial` | decomposition | T1 | 199/199 (100%) | 199/229 (87%) |
| `d_n_children_stated` | decomposition | T1 | 199/199 (100%) | 199/229 (87%) |
| `d_n_children_subgoal` | decomposition | T0 | 199/199 (100%) | 229/229 (100%) |
| `d_n_children_term_mode` | decomposition | T1 | 199/199 (100%) | 199/229 (87%) |
| `d_n_conjunct` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_core_in_parent` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_fewer_bound` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_fewer_hyps` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_iff_direction` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_iff_side` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_introduce_consts` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_more_bound` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_more_hyps` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_relations` | decomposition | T1 | 199/199 (100%) | 199/229 (87%) |
| `d_n_same_core_class` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_same_core_head` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_n_same_family_key` | decomposition | T1 | 182/199 (91%) | 182/229 (79%) |
| `d_name_common_prefix` | decomposition | T0 | 176/199 (88%) | 202/229 (88%) |
| `d_name_common_suffix` | decomposition | T0 | 176/199 (88%) | 202/229 (88%) |
| `d_parent_closing_class` | decomposition | T1 | 194/199 (97%) | 194/229 (85%) |
| `d_parent_mode` | decomposition | T1 | 194/199 (97%) | 194/229 (85%) |
| `d_parent_n_heads` | decomposition | T1 | 194/199 (97%) | 194/229 (85%) |
| `d_parent_site_lines` | decomposition | T0 | 198/199 (99%) | 217/229 (95%) |
| `d_scale` | decomposition | T0 | 199/199 (100%) | 229/229 (100%) |
| `d_shape_depth` | decomposition | T0 | 172/199 (86%) | 188/229 (82%) |
| `d_shape_direct_lemmas` | decomposition | T0 | 172/199 (86%) | 188/229 (82%) |
| `g_concl_class` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_core_class` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_core_class10` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_core_head` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_decl_kind` | goal | T1 | 182/199 (91%) | 182/229 (79%) |
| `g_family_key` | goal | T1 | 114/199 (57%) | 114/229 (50%) |
| `g_form` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_has_bigop` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_has_set_builder` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_language` | goal | T0 | 199/199 (100%) | 229/229 (100%) |
| `g_max_bracket_depth` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_and` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_arrow` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_assumes` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_bigop` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_binder_groups` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_binders_hyp_named` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_binders_prop_form` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_bound_all` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_bound_names` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_consts` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_ctx_vars` | goal | T1 | 167/199 (84%) | 167/229 (73%) |
| `g_n_distinct_numerals` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_exists` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_exists_unique` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_explicit` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_field_uses` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_forall` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_free_idents` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_hyps` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_iff` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_implicit` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_instance` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_ite` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_lambda` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_let` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_not` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_numerals` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_or` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_premises` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_rel` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_set_builder` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_shows` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_sorts` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_spine_forall` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_strict_implicit` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_tokens` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_n_tokens_concl` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_quant_alternations` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_quant_prefix` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_tree_depth` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `g_tree_size` | goal | T1 | 192/199 (96%) | 192/229 (84%) |
| `m_files_ok` | meta | T1 | 199/199 (100%) | 229/229 (100%) |
| `m_glue_share_unclassified` | meta | T1 | 198/199 (99%) | 198/229 (86%) |
| `m_kind` | meta | T0 | 199/199 (100%) | 229/229 (100%) |
| `m_n_claims` | meta | T0 | 199/199 (100%) | 229/229 (100%) |
| `m_parent_share_unknown_leaves` | meta | T1 | 192/199 (96%) | 192/229 (84%) |
| `m_prose_chars_goal_shape` | meta | T0 | 199/199 (100%) | 229/229 (100%) |
| `m_prose_chars_intent` | meta | T0 | 199/199 (100%) | 229/229 (100%) |
| `m_status` | meta | T0 | 199/199 (100%) | 229/229 (100%) |

### G5. Move detectors against the recorded move

`labelled` counts entries whose recorded move is the detector's target; `other` counts the rest. An entry where the detector is null (G3) is in neither numerator nor denominator. Precision is fires-on-labelled over all fires; recall is fires-on-labelled over labelled entries where the detector applies.

Status group: all (229 entries).

| detector (target move) | labelled | labelled, applies | fires on labelled | other, applies | fires on other | precision | recall |
|---|---|---|---|---|---|---|---|
| case-split | 16 | 16 | 16 | 182 | 62 | 0.21 | 1.00 |
| induction | 17 | 17 | 17 | 181 | 13 | 0.57 | 1.00 |
| iff-split | 12 | 12 | 9 | 186 | 5 | 0.64 | 0.75 |
| witness | 15 | 15 | 13 | 183 | 30 | 0.30 | 0.87 |
| extensionality | 12 | 12 | 9 | 186 | 12 | 0.43 | 0.75 |
| calc-chain | 23 | 22 | 16 | 176 | 28 | 0.36 | 0.73 |
| suffices-or-strengthen | 19 | 19 | 8 | 179 | 10 | 0.44 | 0.42 |
| generalise-then-instantiate | 16 | 14 | 2 | 168 | 8 | 0.20 | 0.14 |
| interface-lemma | 17 | 16 | 0 | 183 | 6 | 0.00 | 0.00 |
| per-callee-lemma | 16 | 15 | 5 | 168 | 7 | 0.42 | 0.33 |
| sorrify-at-failure | 4 | 1 | 1 | 198 | 1 | 0.50 | 1.00 |
| blueprint-node | 13 | 13 | 9 | 216 | 11 | 0.45 | 0.69 |
| statement-object | 2 | 2 | 2 | 115 | 12 | 0.14 | 1.00 |
| workflow | 8 | 8 | 7 | 221 | 8 | 0.47 | 0.88 |

Status group: accepted (154 entries).

| detector (target move) | labelled | labelled, applies | fires on labelled | other, applies | fires on other | precision | recall |
|---|---|---|---|---|---|---|---|
| case-split | 11 | 11 | 11 | 132 | 47 | 0.19 | 1.00 |
| induction | 13 | 13 | 13 | 130 | 11 | 0.54 | 1.00 |
| iff-split | 6 | 6 | 4 | 137 | 4 | 0.50 | 0.67 |
| witness | 13 | 13 | 11 | 130 | 24 | 0.31 | 0.85 |
| extensionality | 9 | 9 | 6 | 134 | 9 | 0.40 | 0.67 |
| calc-chain | 19 | 19 | 13 | 124 | 21 | 0.38 | 0.68 |
| suffices-or-strengthen | 16 | 16 | 7 | 127 | 10 | 0.41 | 0.44 |
| generalise-then-instantiate | 13 | 11 | 2 | 123 | 7 | 0.22 | 0.18 |
| interface-lemma | 13 | 13 | 0 | 130 | 3 | 0.00 | 0.00 |
| per-callee-lemma | 10 | 9 | 2 | 125 | 6 | 0.25 | 0.22 |
| sorrify-at-failure | 0 | 0 | 0 | 143 | 0 | n/a | n/a |
| blueprint-node | 10 | 10 | 9 | 144 | 11 | 0.45 | 0.90 |
| statement-object | 0 | 0 | 0 | 82 | 9 | 0.00 | n/a |
| workflow | 0 | 0 | 0 | 154 | 1 | 0.00 | n/a |

Status group: draft (70 entries).

| detector (target move) | labelled | labelled, applies | fires on labelled | other, applies | fires on other | precision | recall |
|---|---|---|---|---|---|---|---|
| case-split | 4 | 4 | 4 | 47 | 13 | 0.24 | 1.00 |
| induction | 4 | 4 | 4 | 47 | 2 | 0.67 | 1.00 |
| iff-split | 6 | 6 | 5 | 45 | 1 | 0.83 | 0.83 |
| witness | 2 | 2 | 2 | 49 | 6 | 0.25 | 1.00 |
| extensionality | 3 | 3 | 3 | 48 | 3 | 0.50 | 1.00 |
| calc-chain | 4 | 3 | 3 | 48 | 7 | 0.30 | 1.00 |
| suffices-or-strengthen | 2 | 2 | 0 | 49 | 0 | n/a | 0.00 |
| generalise-then-instantiate | 2 | 2 | 0 | 45 | 1 | 0.00 | 0.00 |
| interface-lemma | 4 | 3 | 0 | 48 | 3 | 0.00 | 0.00 |
| per-callee-lemma | 6 | 6 | 3 | 42 | 1 | 0.75 | 0.50 |
| sorrify-at-failure | 4 | 1 | 1 | 50 | 1 | 0.50 | 1.00 |
| blueprint-node | 3 | 3 | 0 | 67 | 0 | n/a | 0.00 |
| statement-object | 2 | 2 | 2 | 29 | 3 | 0.40 | 1.00 |
| workflow | 8 | 8 | 7 | 62 | 7 | 0.50 | 0.88 |

Status group: verified or deprecated (5 entries).

| detector (target move) | labelled | labelled, applies | fires on labelled | other, applies | fires on other | precision | recall |
|---|---|---|---|---|---|---|---|
| case-split | 1 | 1 | 1 | 3 | 2 | 0.33 | 1.00 |
| induction | 0 | 0 | 0 | 4 | 0 | n/a | n/a |
| iff-split | 0 | 0 | 0 | 4 | 0 | n/a | n/a |
| witness | 0 | 0 | 0 | 4 | 0 | n/a | n/a |
| extensionality | 0 | 0 | 0 | 4 | 0 | n/a | n/a |
| calc-chain | 0 | 0 | 0 | 4 | 0 | n/a | n/a |
| suffices-or-strengthen | 1 | 1 | 1 | 3 | 0 | 1.00 | 1.00 |
| generalise-then-instantiate | 1 | 1 | 0 | 0 | 0 | n/a | 0.00 |
| interface-lemma | 0 | 0 | 0 | 5 | 0 | n/a | n/a |
| per-callee-lemma | 0 | 0 | 0 | 1 | 0 | n/a | n/a |
| sorrify-at-failure | 0 | 0 | 0 | 5 | 0 | n/a | n/a |
| blueprint-node | 0 | 0 | 0 | 5 | 0 | n/a | n/a |
| statement-object | 0 | 0 | 0 | 4 | 0 | n/a | n/a |
| workflow | 0 | 0 | 0 | 5 | 0 | n/a | n/a |

### G6. Signals of each detector: how often each is true

| detector | signal | in the rule | true on labelled | true on other |
|---|---|---|---|---|
| case-split | alt-pattern | yes | 1/16 (6%) | 9/182 (5%) |
| case-split | nested-tactic | yes | 1/16 (6%) | 0/182 (0%) |
| case-split | or-elim-name | yes | 1/16 (6%) | 0/182 (0%) |
| case-split | split-modifier | yes | 1/16 (6%) | 2/182 (1%) |
| case-split | tactic | yes | 14/16 (88%) | 58/182 (32%) |
| induction | nested-tactic | yes | 0/17 (0%) | 0/181 (0%) |
| induction | recursor-name | yes | 15/17 (88%) | 12/181 (7%) |
| induction | self-reference | yes | 0/17 (0%) | 0/181 (0%) |
| induction | tactic | yes | 15/17 (88%) | 10/181 (6%) |
| iff-split | anon-pair | yes | 2/12 (17%) | 11/186 (6%) |
| iff-split | antisymm-name | yes | 0/12 (0%) | 1/186 (1%) |
| iff-split | constructor | yes | 10/12 (83%) | 31/186 (17%) |
| iff-split | goal-iff | yes | 9/12 (75%) | 4/186 (2%) |
| iff-split | iff-intro-name | yes | 0/12 (0%) | 1/186 (1%) |
| iff-split | isar-directions | yes | 0/12 (0%) | 2/186 (1%) |
| witness | anon-constructor | yes | 4/15 (27%) | 30/183 (16%) |
| witness | exists-intro-name | yes | 0/15 (0%) | 0/183 (0%) |
| witness | goal-exists | yes | 12/15 (80%) | 21/183 (11%) |
| witness | obtain-or-set | no | 7/15 (47%) | 67/183 (37%) |
| witness | tactic | yes | 9/15 (60%) | 23/183 (13%) |
| extensionality | ext-name | yes | 9/12 (75%) | 12/186 (6%) |
| extensionality | tactic | yes | 5/12 (42%) | 8/186 (4%) |
| calc-chain | calc-block | yes | 12/22 (55%) | 14/176 (8%) |
| calc-chain | calc-steps >= 1 | no | 12/22 (55%) | 12/176 (7%) |
| calc-chain | longest-rewrite-run >= 3 | no | 6/22 (27%) | 22/176 (12%) |
| calc-chain | n-trans-names >= 2 | yes | 5/22 (23%) | 19/176 (11%) |
| suffices-or-strengthen | tactic | yes | 8/19 (42%) | 10/179 (6%) |
| generalise-then-instantiate | generalising-child >= 1 | yes | 2/14 (14%) | 8/168 (5%) |
| interface-lemma | api-attr-sites >= 2 | yes | 0/16 (0%) | 6/183 (3%) |
| per-callee-lemma | family-share >= 0.6 | yes | 6/15 (40%) | 23/168 (14%) |
| per-callee-lemma | family-size >= 3 | yes | 6/15 (40%) | 14/168 (8%) |
| sorrify-at-failure | sorry-token >= 1 | yes | 1/1 (100%) | 1/198 (1%) |
| blueprint-node | blueprint-markup >= 1 | yes | 9/13 (69%) | 11/216 (5%) |
| statement-object | theorems-in-file == 1 | yes | 2/2 (100%) | 12/115 (10%) |
| workflow | skill-kind | yes | 6/8 (75%) | 7/221 (3%) |
| workflow | skill-text-site | yes | 7/8 (88%) | 7/221 (3%) |

A signal that is not in the rule is reported only; it does not make the detector fire.

### G7. Entries where detector and label disagree

The entries are listed, not edited. `silent` lists entries labelled with the move on which the detector does not fire; `null` lists labelled entries where it cannot run; `fires elsewhere` lists entries with another label on which it fires, grouped by that label.

**case-split** (rule: tactic or nested-tactic or alt-pattern or split-modifier or or-elim-name)

- silent on 0 labelled: none
- null on 0 labelled: none
- fires elsewhere on 62: calc-chain 4, extensionality 2, generalise-then-instantiate 3, iff-split 4, induction 11, interface-lemma 4, key-invariant 9, other 4, per-callee-lemma 6, sorrify-at-failure 1, suffices-or-strengthen 8, witness 6
  - `isabelle-calc-chain-afp-4d3178de`, `isabelle-calc-chain-cvm-7b177a86`, `isabelle-induction-munta-f75b04fe`, `isabelle-key-invariant-afp-773f380f`, `isabelle-other-isabelle-dist-cb5b330e`, `isabelle-per-callee-lemma-cogent-53de77e6`, `isabelle-sorrify-at-failure-veriso-7de60ce6`, `lean-calc-chain-apap-17556d40`, `lean-extensionality-harmonic-imo2025-7b7ec713`, `lean-extensionality-numina-putnam2025-88be3839`, `lean-generalise-then-instantiate-mathlib4-57b9f5e4`, `lean-iff-split-axiom-imo2026-5ffbca5d`, `lean-iff-split-compfiles-9264faf4`, `lean-iff-split-mathlib4-56646dd1`, `lean-induction-apap-5dd33a6c`, `lean-induction-compfiles-235f3159`, `lean-induction-flt-anthropic-46946403`, `lean-induction-formal-conjectures-e2f33737`, `lean-induction-formal-proofs-ffaeb961`, `lean-induction-mathlib4-7990f97f`, `lean-interface-lemma-harmonic-imo2025-8920cc7b`, `lean-key-invariant-compfiles-f9a0ece2`, `lean-key-invariant-pramaana-imo2026-f2c90a7c`, `lean-key-invariant-seed-prover-ccd41e1d`, `lean-key-invariant-sphere-eversion-6e399f2e`, `lean-other-carleson-cfff7ffe`, `lean-other-flt-imperial-4b2bc017`, `lean-other-flt-imperial-ac21422b`, `lean-per-callee-lemma-equational-theories-b60a63fd`, `lean-per-callee-lemma-formal-proofs-4f0e8f5a`, `lean-per-callee-lemma-pnt-and-3ba98173`, `lean-suffices-or-strengthen-carleson-a02af82b`, `lean-suffices-or-strengthen-formal-conjectures-7ee9bbe2`, `lean-suffices-or-strengthen-pfr-16fd5d4d`, `lean-suffices-or-strengthen-pnt-and-36592f32`, `lean-witness-arklib-aa588c93`, `lean-witness-brownian-motion-8893edf0`, `lean-witness-equational-theories-f93d568f`, `lean-witness-pfr-e55fc34d`, `rocq-calc-chain-coqeal-665ffa2e`, `rocq-generalise-then-instantiate-metarocq-f9d21519`, `rocq-generalise-then-instantiate-tarjan-3d1027db`, `rocq-iff-split-reglang-7747be2e`, `rocq-induction-interaction-trees-b0a7a191`, `rocq-induction-jasmin-dc9a0691`, `rocq-induction-math-comp-8c9c659d`, `rocq-induction-ssprove-47a61d8e`, `rocq-interface-lemma-certicoq-43993c65`, `rocq-interface-lemma-metarocq-dfd0eaa4`, `rocq-interface-lemma-vellvm-c6bfef84`, `rocq-key-invariant-bedrock2-c3d50249`, `rocq-key-invariant-compcert-4abf5603`, `rocq-key-invariant-rocq-stdlib-1a358d2f`, `rocq-key-invariant-unimath-70bbfe4a`, `rocq-per-callee-lemma-metarocq-861d7783`, `rocq-per-callee-lemma-wasmcert-coq-808e3c09`, `rocq-suffices-or-strengthen-certicoq-933592e6`, `rocq-suffices-or-strengthen-fourcolor-2e61be44`, `rocq-suffices-or-strengthen-hydra-battles-ffb3ec65`, `rocq-suffices-or-strengthen-interaction-trees-afae2097`, `rocq-witness-hydra-battles-f45d6a98`, `rocq-witness-mathcomp-analysis-dc247f7a`

**induction** (rule: tactic or nested-tactic or recursor-name or self-reference)

- silent on 0 labelled: none
- null on 0 labelled: none
- fires elsewhere on 13: extensionality 1, generalise-then-instantiate 1, interface-lemma 1, key-invariant 3, per-callee-lemma 3, sorrify-at-failure 1, suffices-or-strengthen 3
  - `isabelle-sorrify-at-failure-veriso-7de60ce6`, `lean-extensionality-harmonic-imo2025-7b7ec713`, `lean-interface-lemma-harmonic-imo2025-8920cc7b`, `lean-key-invariant-pramaana-imo2026-f2c90a7c`, `lean-suffices-or-strengthen-formal-conjectures-7ee9bbe2`, `lean-suffices-or-strengthen-pfr-16fd5d4d`, `rocq-generalise-then-instantiate-apery-814e5d20`, `rocq-key-invariant-rocq-stdlib-1a358d2f`, `rocq-key-invariant-unimath-70bbfe4a`, `rocq-per-callee-lemma-certicoq-2bfeffdd`, `rocq-per-callee-lemma-metarocq-861d7783`, `rocq-per-callee-lemma-wasmcert-coq-808e3c09`, `rocq-suffices-or-strengthen-interaction-trees-afae2097`

**iff-split** (rule: (goal-iff and (constructor or anon-pair or isar-directions)) or iff-intro-name or antisymm-name)

- silent on 3 labelled: `isabelle-iff-split-munkres-isabelle-05cdf9d1`, `lean-iff-split-numina-putnam2025-95670702`, `rocq-iff-split-reglang-7747be2e`
- null on 0 labelled: none
- fires elsewhere on 5: calc-chain 1, case-split 1, generalise-then-instantiate 1, key-invariant 2
  - `lean-calc-chain-compfiles-5cbadaea`, `lean-case-split-harmonic-imo2025-09c4818f`, `lean-generalise-then-instantiate-compfiles-f96a55bd`, `lean-key-invariant-compfiles-f9a0ece2`, `lean-key-invariant-pramaana-imo2026-f2c90a7c`

**witness** (rule: tactic or (goal-exists and anon-constructor) or exists-intro-name)

- silent on 2 labelled: `lean-witness-arklib-aa588c93`, `rocq-witness-unimath-e5043582`
- null on 0 labelled: none
- fires elsewhere on 30: calc-chain 1, case-split 3, generalise-then-instantiate 5, iff-split 1, induction 3, interface-lemma 2, key-invariant 6, other 1, per-callee-lemma 4, suffices-or-strengthen 4
  - `lean-calc-chain-carleson-eeedf502`, `lean-case-split-harmonic-imo2025-09c4818f`, `lean-case-split-pfr-7d058764`, `lean-case-split-pnt-and-96d6a0ca`, `lean-generalise-then-instantiate-carleson-63234e9a`, `lean-generalise-then-instantiate-compfiles-f96a55bd`, `lean-generalise-then-instantiate-mathlib4-0ccee655`, `lean-generalise-then-instantiate-navierstokesandeuler-985e7e4f`, `lean-induction-flt-anthropic-46946403`, `lean-induction-formal-proofs-ffaeb961`, `lean-interface-lemma-formal-proofs-fecde902`, `lean-key-invariant-seed-prover-ccd41e1d`, `lean-key-invariant-sphere-eversion-6e399f2e`, `lean-other-axiom-imo2026-adc45ecb`, `lean-per-callee-lemma-equational-theories-b60a63fd`, `lean-suffices-or-strengthen-pfr-16fd5d4d`, `lean-suffices-or-strengthen-pnt-and-36592f32`, `rocq-generalise-then-instantiate-metarocq-f9d21519`, `rocq-iff-split-reglang-7747be2e`, `rocq-induction-jasmin-dc9a0691`, `rocq-interface-lemma-certicoq-43993c65`, `rocq-key-invariant-bedrock2-c3d50249`, `rocq-key-invariant-compcert-4abf5603`, `rocq-key-invariant-rocq-stdlib-1a358d2f`, `rocq-key-invariant-unimath-70bbfe4a`, `rocq-per-callee-lemma-coq-library-undecidability-683e3c0c`, `rocq-per-callee-lemma-metarocq-861d7783`, `rocq-per-callee-lemma-wasmcert-coq-808e3c09`, `rocq-suffices-or-strengthen-certicoq-933592e6`, `rocq-suffices-or-strengthen-fourcolor-2e61be44`

**extensionality** (rule: tactic or ext-name)

- silent on 3 labelled: `rocq-extensionality-fiat-crypto-cb9f23da`, `rocq-extensionality-fourcolor-a5f0540e`, `rocq-extensionality-mathcomp-analysis-fa807b35`
- null on 0 labelled: none
- fires elsewhere on 12: calc-chain 1, case-split 1, iff-split 1, interface-lemma 1, key-invariant 2, sorrify-at-failure 1, suffices-or-strengthen 2, witness 2, workflow 1
  - `isabelle-sorrify-at-failure-veriso-7de60ce6`, `lean-calc-chain-sampcert-c1d1c12b`, `lean-case-split-harmonic-imo2025-09c4818f`, `lean-iff-split-mathlib4-56646dd1`, `lean-interface-lemma-harmonic-imo2025-8920cc7b`, `lean-key-invariant-pramaana-imo2026-f2c90a7c`, `lean-key-invariant-sphere-eversion-6e399f2e`, `lean-suffices-or-strengthen-carleson-a02af82b`, `lean-suffices-or-strengthen-formal-conjectures-7ee9bbe2`, `lean-witness-brownian-motion-8893edf0`, `lean-witness-sphere-eversion-2ae37d14`, `lean-workflow-lean-stat-learning-theory-683bae5a`

**calc-chain** (rule: calc-block or trans-names>=2)

- silent on 6 labelled: `lean-calc-chain-con-nf-9a04fb7d`, `lean-calc-chain-infinity-cosmos-933fc1d5`, `lean-calc-chain-sampcert-c1d1c12b`, `rocq-calc-chain-abel-2c55660e`, `rocq-calc-chain-bedrock2-f158f24e`, `rocq-calc-chain-ssprove-54f699c2`
- null on 1 labelled: markdown-calc-chain-leanprover-skills-d842291a (not-prover-language)
- fires elsewhere on 28: case-split 4, extensionality 1, generalise-then-instantiate 2, induction 3, interface-lemma 2, key-invariant 4, other 3, per-callee-lemma 1, sorrify-at-failure 1, suffices-or-strengthen 6, workflow 1
  - `isabelle-extensionality-afp-38fc5bd6`, `isabelle-key-invariant-afp-773f380f`, `isabelle-key-invariant-autocorrode-d7f695a1`, `isabelle-sorrify-at-failure-veriso-7de60ce6`, `lean-case-split-mathlib4-c53126e3`, `lean-case-split-perennial-78263300`, `lean-case-split-pfr-7d058764`, `lean-case-split-pnt-and-96d6a0ca`, `lean-generalise-then-instantiate-sphere-packing-9e03f73b`, `lean-induction-apap-5dd33a6c`, `lean-induction-formal-proofs-ffaeb961`, `lean-interface-lemma-formal-proofs-fecde902`, `lean-interface-lemma-lean-liquid-96015c5e`, `lean-key-invariant-lean-liquid-01d1344d`, `lean-key-invariant-sphere-eversion-6e399f2e`, `lean-other-carleson-cfff7ffe`, `lean-suffices-or-strengthen-carleson-a02af82b`, `lean-suffices-or-strengthen-compfiles-25eb18ba`, `lean-suffices-or-strengthen-formal-conjectures-7ee9bbe2`, `lean-suffices-or-strengthen-pfr-16fd5d4d`, `lean-suffices-or-strengthen-pnt-and-36592f32`, `lean-workflow-lean-stat-learning-theory-683bae5a`, `rocq-generalise-then-instantiate-apery-814e5d20`, `rocq-induction-math-comp-8c9c659d`, `rocq-other-odd-order-295f8af4`, `rocq-other-unimath-a6108b06`, `rocq-per-callee-lemma-metarocq-861d7783`, `rocq-suffices-or-strengthen-fiat-crypto-efce3e48`

**suffices-or-strengthen** (rule: tactic)

- silent on 11 labelled: `isabelle-suffices-or-strengthen-afp-eb3f1a40`, `isabelle-suffices-or-strengthen-l4v-0a36f701`, `isabelle-suffices-or-strengthen-l4v-d7945679`, `lean-suffices-or-strengthen-compfiles-25eb18ba`, `lean-suffices-or-strengthen-mathlib4-b3035491`, `lean-suffices-or-strengthen-pnt-and-36592f32`, `lean-suffices-or-strengthen-seed-prover-c33ea164`, `lean-suffices-or-strengthen-sphere-packing-68ac6a8d`, `rocq-suffices-or-strengthen-certicoq-933592e6`, `rocq-suffices-or-strengthen-fiat-crypto-efce3e48`, `rocq-suffices-or-strengthen-hydra-battles-ffb3ec65`
- null on 0 labelled: none
- fires elsewhere on 10: case-split 2, extensionality 1, generalise-then-instantiate 2, induction 3, key-invariant 1, witness 1
  - `lean-case-split-pfr-7d058764`, `lean-generalise-then-instantiate-carleson-63234e9a`, `lean-induction-apap-5dd33a6c`, `lean-induction-compfiles-235f3159`, `lean-induction-formal-conjectures-e2f33737`, `lean-key-invariant-mathlib4-3f171129`, `rocq-case-split-odd-order-fe6c7643`, `rocq-extensionality-fourcolor-a5f0540e`, `rocq-generalise-then-instantiate-apery-814e5d20`, `rocq-witness-mathcomp-analysis-dc247f7a`

**generalise-then-instantiate** (rule: generalising-child)

- silent on 12 labelled: `lean-generalise-then-instantiate-arklib-c3287ad6`, `lean-generalise-then-instantiate-carleson-63234e9a`, `lean-generalise-then-instantiate-lean-atiyah-singer-83424c2a`, `lean-generalise-then-instantiate-mathlib4-0ccee655`, `lean-generalise-then-instantiate-mathlib4-57b9f5e4`, `lean-generalise-then-instantiate-navierstokesandeuler-985e7e4f`, `lean-generalise-then-instantiate-pnt-and-1d2fc8e6`, `lean-generalise-then-instantiate-sphere-packing-9e03f73b`, `rocq-generalise-then-instantiate-apery-814e5d20`, `rocq-generalise-then-instantiate-metarocq-f9d21519`, `rocq-generalise-then-instantiate-qcert-32b1fe62`, `rocq-generalise-then-instantiate-tarjan-3d1027db`
- null on 2 labelled: isabelle-generalise-then-instantiate-voblint-verification-master-thesis-b47c5898 (no-child-statement), lean-generalise-then-instantiate-compfiles-f96a55bd (no-child-statement)
- fires elsewhere on 8: calc-chain 1, case-split 1, induction 2, key-invariant 2, suffices-or-strengthen 2
  - `lean-case-split-mathlib4-d8adc729`, `lean-induction-formal-conjectures-e2f33737`, `lean-suffices-or-strengthen-pnt-and-36592f32`, `rocq-calc-chain-coqeal-665ffa2e`, `rocq-induction-jordan-curve-theorem-3e5df212`, `rocq-key-invariant-bedrock2-c3d50249`, `rocq-key-invariant-verdi-09db5810`, `rocq-suffices-or-strengthen-interaction-trees-afae2097`

**interface-lemma** (rule: api-attr-sites>=2)

- silent on 16 labelled: `isabelle-interface-lemma-cogent-da73726a`, `isabelle-interface-lemma-voblint-verification-master-thesis-f80093c1`, `lean-interface-lemma-carleson-50fa619f`, `lean-interface-lemma-cedar-spec-654be43c`, `lean-interface-lemma-equational-theories-048d3d79`, `lean-interface-lemma-formal-proofs-fecde902`, `lean-interface-lemma-harmonic-imo2025-8920cc7b`, `lean-interface-lemma-lean-liquid-96015c5e`, `lean-interface-lemma-navierstokesandeuler-a97a0c4b`, `lean-interface-lemma-odd-order-2-6e6d20ec`, `lean-interface-lemma-pnt-and-a92f866a`, `lean-interface-lemma-strongpnt-f735021c`, `rocq-interface-lemma-certicoq-43993c65`, `rocq-interface-lemma-compcert-eda26107`, `rocq-interface-lemma-metarocq-dfd0eaa4`, `rocq-interface-lemma-vellvm-c6bfef84`
- null on 1 labelled: markdown-interface-lemma-isabelle-pide-ai-c76a2eee (not-prover-language)
- fires elsewhere on 6: calc-chain 2, generalise-then-instantiate 1, key-invariant 1, per-callee-lemma 1, suffices-or-strengthen 1
  - `isabelle-calc-chain-cvm-7b177a86`, `isabelle-generalise-then-instantiate-voblint-verification-master-thesis-b47c5898`, `isabelle-key-invariant-afp-773f380f`, `isabelle-per-callee-lemma-cogent-53de77e6`, `isabelle-suffices-or-strengthen-l4v-d7945679`, `lean-calc-chain-classfieldtheory-7c2ce288`

**per-callee-lemma** (rule: family-size>=3 and family-share>=0.6)

- silent on 10 labelled: `isabelle-per-callee-lemma-cogent-53de77e6`, `isabelle-per-callee-lemma-munkres-isabelle-97b8b78b`, `lean-per-callee-lemma-cedar-spec-ffe042b1`, `lean-per-callee-lemma-equational-theories-b60a63fd`, `lean-per-callee-lemma-formal-proofs-4f0e8f5a`, `rocq-per-callee-lemma-compcert-6decbbae`, `rocq-per-callee-lemma-coq-library-undecidability-683e3c0c`, `rocq-per-callee-lemma-metarocq-861d7783`, `rocq-per-callee-lemma-rocq-stdlib-096380b6`, `rocq-per-callee-lemma-wasmcert-coq-808e3c09`
- null on 1 labelled: latex-per-callee-lemma-infinity-cosmos-d5bd17fc (not-prover-language)
- fires elsewhere on 7: calc-chain 3, induction 2, key-invariant 1, suffices-or-strengthen 1
  - `lean-calc-chain-infinity-cosmos-933fc1d5`, `lean-induction-formal-conjectures-e2f33737`, `lean-induction-seymour-4222c0a6`, `rocq-calc-chain-bedrock2-f158f24e`, `rocq-calc-chain-coqeal-665ffa2e`, `rocq-key-invariant-vst-b22e13ea`, `rocq-suffices-or-strengthen-interaction-trees-afae2097`

**sorrify-at-failure** (rule: sorry-token)

- silent on 0 labelled: none
- null on 3 labelled: markdown-sorrify-at-failure-lean4-skills-430f389e (not-prover-language), markdown-sorrify-at-failure-leanprover-skills-9066c346 (not-prover-language), python-sorrify-at-failure-ml-hilbert-123da6f9 (not-prover-language)
- fires elsewhere on 1: witness 1
  - `lean-witness-analysis-dd193d51`

**blueprint-node** (rule: blueprint-markup)

- silent on 4 labelled: `lean-blueprint-node-flt-anthropic-a734af31`, `lean-blueprint-node-flt-regular-5f4403ff`, `markdown-blueprint-node-lean-autoformalization-skills-46b535bc`, `markdown-blueprint-node-numina-lean-agent-91c2a449`
- null on 0 labelled: none
- fires elsewhere on 11: calc-chain 2, case-split 1, extensionality 1, generalise-then-instantiate 1, interface-lemma 1, key-invariant 1, other 1, per-callee-lemma 1, suffices-or-strengthen 1, witness 1
  - `latex-per-callee-lemma-infinity-cosmos-d5bd17fc`, `lean-calc-chain-infinity-cosmos-933fc1d5`, `lean-calc-chain-sphere-packing-7d6a60c4`, `lean-case-split-pnt-and-96d6a0ca`, `lean-extensionality-strongpnt-8892e42d`, `lean-generalise-then-instantiate-pnt-and-1d2fc8e6`, `lean-interface-lemma-pnt-and-a92f866a`, `lean-key-invariant-sphere-packing-ad9db4d3`, `lean-other-pnt-and-9e1ff179`, `lean-suffices-or-strengthen-pnt-and-36592f32`, `lean-witness-equational-theories-f93d568f`

**statement-object** (rule: theorems-in-file==1)

- silent on 0 labelled: none
- null on 0 labelled: none
- fires elsewhere on 12: calc-chain 1, case-split 3, induction 1, interface-lemma 2, key-invariant 1, other 1, per-callee-lemma 2, witness 1
  - `lean-calc-chain-compfiles-5cbadaea`, `lean-case-split-flt-imperial-b72a01ad`, `lean-case-split-flt-regular-696a9e84`, `lean-case-split-mathlib4-c53126e3`, `lean-induction-compfiles-235f3159`, `lean-interface-lemma-formal-proofs-fecde902`, `lean-interface-lemma-lean-liquid-96015c5e`, `lean-key-invariant-compfiles-f9a0ece2`, `lean-other-flt-anthropic-4f58acd6`, `lean-per-callee-lemma-equational-theories-b60a63fd`, `lean-per-callee-lemma-pnt-and-3ba98173`, `lean-witness-compfiles-b724f0b7`

**workflow** (rule: skill-kind or skill-text-site)

- silent on 1 labelled: `markdown-workflow-numina-lean-agent-b4e8ebdf`
- null on 0 labelled: none
- fires elsewhere on 8: blueprint-node 1, calc-chain 1, extract-have 2, interface-lemma 1, other 1, sorrify-at-failure 2
  - `markdown-blueprint-node-lean-autoformalization-skills-46b535bc`, `markdown-calc-chain-leanprover-skills-d842291a`, `markdown-extract-have-trailofbits-skills-9a206aa0`, `markdown-interface-lemma-isabelle-pide-ai-c76a2eee`, `markdown-other-leanprover-skills-68f66bfd`, `markdown-sorrify-at-failure-lean4-skills-430f389e`, `markdown-sorrify-at-failure-leanprover-skills-9066c346`, `python-extract-have-ml-hilbert-30f55e92`

Moves with no detector: `key-invariant` (17 entries), `extract-have` (5 entries), `other` (17 entries).

### G8. Goal features against the recorded move (counts; no model is fitted)

Rows are values of one goal feature of the parent statement; columns are recorded moves. Only the 199 entries in a prover language are counted; `None` is a null feature.

`g_core_class10`:

| value | case | induct | iff | witness | ext | calc | suff | key-inv | gen | iface | callee | sorry | ext-have | bp | stmt-obj | workflow | other | total |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| app | 4 | 6 |  | 2 | 2 | 3 | 6 | 6 | 3 | 5 | 8 |  |  |  | 2 |  | 2 | 49 |
| eq | 1 | 6 |  |  | 7 | 5 | 4 |  | 7 | 4 | 1 |  |  |  |  |  | 6 | 41 |
| exists | 2 | 2 |  | 12 |  | 1 | 1 | 2 | 5 | 4 | 1 |  |  | 1 |  |  | 2 | 33 |
| order |  | 2 |  |  |  | 11 | 3 | 3 |  | 1 | 1 |  |  |  |  | 1 | 1 | 23 |
| iff |  |  | 9 |  |  |  |  | 2 | 1 | 1 |  |  |  |  |  |  |  | 13 |
| other | 2 |  | 1 |  | 1 | 1 | 2 | 2 |  | 1 | 2 |  |  |  |  |  | 1 | 13 |
| and | 2 | 1 | 2 |  | 1 |  | 1 |  |  |  | 2 |  | 1 |  |  |  | 1 | 11 |
| None | 2 |  |  |  | 1 |  | 1 |  |  |  |  | 1 |  |  |  |  | 2 | 7 |
| neg | 2 |  |  | 1 |  | 1 | 1 |  |  |  |  |  |  | 1 |  |  |  | 6 |
| or | 1 |  |  |  |  |  |  | 1 |  |  |  |  |  |  |  |  |  | 2 |
| mem |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |  |  |  | 1 |

`g_concl_class`:

| value | case | induct | iff | witness | ext | calc | suff | key-inv | gen | iface | callee | sorry | ext-have | bp | stmt-obj | workflow | other | total |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| app | 4 | 4 |  | 2 | 1 | 3 | 3 | 4 | 2 | 1 | 5 |  |  |  | 2 |  | 2 | 33 |
| rel:eq | 1 | 4 |  |  | 6 | 3 | 3 |  | 4 | 2 |  |  |  |  |  |  | 5 | 28 |
| arrow | 1 | 2 |  | 3 | 1 | 2 | 5 | 2 | 2 | 2 | 3 |  |  |  |  |  | 1 | 24 |
| exists | 2 | 1 |  | 9 |  | 1 |  |  | 4 | 3 | 1 |  |  | 1 |  |  | 2 | 24 |
| forall | 1 | 4 |  |  |  | 2 | 1 | 3 | 3 | 5 | 4 |  |  |  |  |  |  | 23 |
| rel:le |  | 1 |  |  |  | 6 | 3 | 1 |  | 1 |  |  |  |  |  | 1 | 1 | 14 |
| iff |  |  | 9 |  |  |  |  | 2 | 1 | 1 |  |  |  |  |  |  |  | 13 |
| None | 2 |  |  |  | 1 |  | 1 |  |  |  |  | 1 |  |  |  |  | 2 | 7 |
| and | 1 | 1 | 1 |  | 1 |  | 1 |  |  |  |  |  | 1 |  |  |  | 1 | 7 |
| let |  |  |  |  | 1 |  |  | 1 |  | 1 |  |  |  |  |  |  | 1 | 4 |
| rel:lt |  |  |  |  |  | 2 |  | 1 |  |  |  |  |  |  |  |  |  | 3 |
| expr |  |  | 1 |  |  |  | 1 |  |  |  |  |  |  |  |  |  |  | 2 |
| false | 1 |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  | 2 |
| multi |  |  | 1 |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  | 2 |
| not | 1 |  |  |  |  | 1 |  |  |  |  |  |  |  |  |  |  |  | 2 |
| or | 1 |  |  |  |  |  |  | 1 |  |  |  |  |  |  |  |  |  | 2 |
| rel:equiv |  |  |  |  | 1 | 1 |  |  |  |  |  |  |  |  |  |  |  | 2 |
| prefix | 1 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 1 |
| rel:asymp |  |  |  |  |  |  | 1 |  |  |  |  |  |  |  |  |  |  | 1 |
| rel:entails |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |  |  |  | 1 |
| rel:mem |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  |  |  |  | 1 |
| rel:modeq |  |  |  |  |  | 1 |  |  |  |  |  |  |  |  |  |  |  | 1 |
| rel:ne |  |  |  | 1 |  |  |  |  |  |  |  |  |  |  |  |  |  | 1 |
| triple |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  | 1 |

`g_quant_prefix` (`(none)`: the conclusion starts with no quantifier):

| value | case | induct | iff | witness | ext | calc | suff | key-inv | gen | iface | callee | sorry | ext-have | bp | stmt-obj | workflow | other | total |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| (none) | 11 | 12 | 12 | 3 | 11 | 19 | 15 | 13 | 8 | 7 | 10 |  | 1 | 1 | 2 | 1 | 11 | 137 |
| E | 1 |  |  | 12 |  | 1 |  | 1 | 5 | 3 | 1 |  |  | 1 |  |  | 2 | 27 |
| A | 1 | 3 |  |  |  | 2 | 2 | 2 | 3 | 5 | 4 |  |  |  |  |  |  | 22 |
| None | 2 |  |  |  | 1 |  | 1 |  |  |  |  | 1 |  |  |  |  | 2 | 7 |
| AE |  | 1 |  |  |  |  | 1 | 1 |  | 1 |  |  |  |  |  |  |  | 4 |
| EA | 1 | 1 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 2 |

`g_quant_alternations`:

| value | case | induct | iff | witness | ext | calc | suff | key-inv | gen | iface | callee | sorry | ext-have | bp | stmt-obj | workflow | other | total |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 13 | 15 | 12 | 11 | 11 | 20 | 17 | 15 | 14 | 13 | 15 |  | 1 | 2 | 2 | 1 | 11 | 173 |
| 1 | 1 | 1 |  | 3 |  | 1 | 1 | 2 | 1 | 1 |  |  |  |  |  |  | 2 | 13 |
| None | 2 |  |  |  | 1 |  | 1 |  |  |  |  | 1 |  |  |  |  | 2 | 7 |
| 2 |  |  |  |  |  | 1 |  |  | 1 | 1 |  |  |  |  |  |  |  | 3 |
| 3 |  | 1 |  | 1 |  |  |  |  |  | 1 |  |  |  |  |  |  |  | 3 |

`g_n_hyps`, bucketed:

| value | case | induct | iff | witness | ext | calc | suff | key-inv | gen | iface | callee | sorry | ext-have | bp | stmt-obj | workflow | other | total |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 6 | 4 | 6 | 5 | 3 | 11 | 7 | 4 | 11 | 3 | 6 |  | 1 | 1 | 2 |  | 4 | 74 |
| 1-2 | 5 | 7 | 5 | 8 | 5 | 5 | 5 | 9 | 5 | 7 | 6 |  |  | 1 |  |  | 5 | 73 |
| 3-5 | 2 | 5 | 1 | 2 | 2 | 5 | 5 | 3 |  | 1 | 1 |  |  |  |  | 1 | 3 | 31 |
| 6+ | 1 | 1 |  |  | 1 | 1 | 1 | 1 |  | 5 | 2 |  |  |  |  |  | 1 | 14 |
| null | 2 |  |  |  | 1 |  | 1 |  |  |  |  | 1 |  |  |  |  | 2 | 7 |

`g_n_bound_all`, bucketed:

| value | case | induct | iff | witness | ext | calc | suff | key-inv | gen | iface | callee | sorry | ext-have | bp | stmt-obj | workflow | other | total |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 4 | 2 | 3 | 6 | 5 | 9 | 7 | 4 | 7 |  | 8 |  | 1 |  | 1 |  | 5 | 62 |
| 1-2 | 5 | 5 | 5 | 3 | 2 | 6 | 3 | 6 | 5 | 5 |  |  |  | 1 |  |  | 3 | 49 |
| 3-5 | 3 | 8 | 4 | 5 | 3 | 4 | 5 | 5 | 4 | 5 | 3 |  |  |  | 1 | 1 | 2 | 53 |
| 6+ | 2 | 2 |  | 1 | 1 | 3 | 3 | 2 |  | 6 | 4 |  |  | 1 |  |  | 3 | 28 |
| null | 2 |  |  |  | 1 |  | 1 |  |  |  |  | 1 |  |  |  |  | 2 | 7 |

`g_has_set_builder`:

| value | case | induct | iff | witness | ext | calc | suff | key-inv | gen | iface | callee | sorry | ext-have | bp | stmt-obj | workflow | other | total |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| False | 13 | 17 | 10 | 14 | 9 | 22 | 17 | 15 | 16 | 16 | 14 |  | 1 | 2 | 2 | 1 | 13 | 182 |
| True | 1 |  | 2 | 1 | 2 |  | 1 | 2 |  |  | 1 |  |  |  |  |  |  | 10 |
| None | 2 |  |  |  | 1 |  | 1 |  |  |  |  | 1 |  |  |  |  | 2 | 7 |

`g_has_bigop`:

| value | case | induct | iff | witness | ext | calc | suff | key-inv | gen | iface | callee | sorry | ext-have | bp | stmt-obj | workflow | other | total |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| False | 14 | 16 | 12 | 13 | 10 | 19 | 17 | 15 | 15 | 14 | 15 |  | 1 | 2 | 2 |  | 12 | 177 |
| True |  | 1 |  | 2 | 1 | 3 | 1 | 2 | 1 | 2 |  |  |  |  |  | 1 | 1 | 15 |
| None | 2 |  |  |  | 1 |  | 1 |  |  |  |  | 1 |  |  |  |  | 2 | 7 |

`g_decl_kind`:

| value | case | induct | iff | witness | ext | calc | suff | key-inv | gen | iface | callee | sorry | ext-have | bp | stmt-obj | workflow | other | total |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| theorem | 8 | 7 | 9 | 8 | 4 | 9 | 7 | 6 | 9 | 8 | 4 |  |  | 2 | 2 | 1 | 6 | 90 |
| Theorem |  | 3 |  | 4 | 2 | 2 | 2 | 6 | 2 | 3 | 4 |  |  |  |  |  | 1 | 29 |
| lemma | 2 | 2 |  | 1 | 4 | 3 | 4 | 3 | 1 | 4 | 2 |  |  |  |  |  | 3 | 29 |
| Lemma | 1 | 2 | 1 | 1 | 1 | 3 | 3 | 1 | 3 | 1 | 3 |  |  |  |  |  | 2 | 22 |
| None | 4 | 2 |  |  | 1 | 2 | 2 |  |  |  | 1 | 1 | 1 |  |  |  | 3 | 17 |
| problem | 1 | 1 | 2 | 1 |  | 2 | 1 | 1 | 1 |  |  |  |  |  |  |  |  | 10 |
| Definition |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |  | 1 |
| def |  |  |  |  |  | 1 |  |  |  |  |  |  |  |  |  |  |  | 1 |

### G9. Proof-step heads by class

| class | lean | rocq | isabelle |
|---|---|---|---|
| automation | 2049 (19.7%) | 2081 (15.2%) | 1048 (19.5%) |
| trivial-close | 89 (0.9%) | 408 (3.0%) | 131 (2.4%) |
| exact | 1010 (9.7%) | 172 (1.3%) | 0 (0.0%) |
| apply | 822 (7.9%) | 2480 (18.1%) | 495 (9.2%) |
| rewrite | 1857 (17.8%) | 3049 (22.2%) | 218 (4.1%) |
| intro | 546 (5.2%) | 952 (6.9%) | 109 (2.0%) |
| have | 2122 (20.4%) | 747 (5.4%) | 459 (8.5%) |
| obtain | 394 (3.8%) | 7 (0.1%) | 34 (0.6%) |
| show | 14 (0.1%) | 0 (0.0%) | 197 (3.7%) |
| suffices | 29 (0.3%) | 36 (0.3%) | 0 (0.0%) |
| induction | 38 (0.4%) | 156 (1.1%) | 14 (0.3%) |
| case-split | 294 (2.8%) | 945 (6.9%) | 44 (0.8%) |
| ext | 79 (0.8%) | 0 (0.0%) | 0 (0.0%) |
| witness | 108 (1.0%) | 284 (2.1%) | 0 (0.0%) |
| constructor | 105 (1.0%) | 745 (5.4%) | 0 (0.0%) |
| calc | 82 (0.8%) | 35 (0.3%) | 130 (2.4%) |
| contra | 119 (1.1%) | 36 (0.3%) | 0 (0.0%) |
| context | 337 (3.2%) | 665 (4.8%) | 65 (1.2%) |
| combinator | 44 (0.4%) | 666 (4.9%) | 8 (0.1%) |
| structure | 53 (0.5%) | 0 (0.0%) | 1823 (33.9%) |
| facts | 0 (0.0%) | 0 (0.0%) | 585 (10.9%) |
| term | 94 (0.9%) | 19 (0.1%) | 0 (0.0%) |
| sorry | 4 (0.0%) | 0 (0.0%) | 6 (0.1%) |
| domain | 107 (1.0%) | 163 (1.2%) | 0 (0.0%) |
| unclassified | 26 (0.2%) | 66 (0.5%) | 13 (0.2%) |
| total | 10422 | 13712 | 5379 |

Most frequent unclassified heads, lean: `rpow_ring` 5, `sol` 3, `Nat.card` 2, `simp_do_let` 2, `tendsto_cont` 2, `H` 1, `a` 1, `b` 1, `c` 1, `coprime` 1, `h.Ext'_five_term_exact_seq` 1, `ha` 1, `hb` 1, `hc` 1, `hcdvd` 1, `j` 1, `u` 1.

Most frequent unclassified heads, rocq: `resolve_subtyping` 7, `force_left` 5, `force_right` 5, `do_in_map` 4, `astepl` 3, `rstep` 3, `rtoProp` 3, `sq` 3, `extract_premise` 2, `fs` 2, `simplify` 2, `t_xrbindP` 2, `«sym»` 2, `Errors.monadInv` 1, `InitGPred_tac` 1, `InvSoundState` 1, `aw` 1, `comp_skip` 1, `destruct_head'_and` 1, `distr_length` 1.

Most frequent unclassified heads, isabelle: `ilock_type_inv_tac` 4, `lifting` 4, `refine_dref_type` 2, `ccfv_threshold` 1, `del_insts` 1, `hoare_split` 1.

### G10. Where notation defeats the statement parser

| language | parents parsed | mean share of leaves with unknown notation (parents) | parents whose core is an `expr` leaf | parents whose core is not a connective, relation or application | children parsed | mean share of leaves with unknown notation (children) | children whose core is an `expr` leaf |
|---|---|---|---|---|---|---|---|
| lean | 113 | 0.063 | 0/113 (0%) | 0/113 (0%) | 400 | 0.078 | 4/400 (1%) |
| rocq | 54 | 0.056 | 2/54 (4%) | 2/54 (4%) | 263 | 0.102 | 20/263 (8%) |
| isabelle | 25 | 0.153 | 1/25 (4%) | 2/25 (8%) | 85 | 0.140 | 2/85 (2%) |

### G11. Glue scope and child proofs

| language | None | declaration-extent | none | sites |
|---|---|---|---|---|
| isabelle |  |  |  | 27 |
| latex | 10 |  |  |  |
| lean |  | 1 | 1 | 116 |
| markdown | 17 |  |  |  |
| python | 3 |  |  |  |
| rocq |  |  |  | 54 |

| language | child proofs read | automation alone | automation or trivial close alone | closing step is automation | term mode |
|---|---|---|---|---|---|
| lean | 390 | 13/390 (3%) | 13/390 (3%) | 89/390 (23%) | 65/390 (17%) |
| rocq | 238 | 11/238 (5%) | 11/238 (5%) | 96/238 (40%) | 17/238 (7%) |
| isabelle | 93 | 22/93 (24%) | 22/93 (24%) | 33/93 (35%) | 0/93 (0%) |

### G12. The head class table (version 1)

Printed from `CLASS_TABLE` in `feature_terms_lex.py`. A head is looked up by its name, then with spaces as underscores, then without a trailing `?`, `!` or `'`; then the prefix rules apply; otherwise it is `unclassified`.

lean:

| class | heads |
|---|---|
| automation | `abel` `abel_nf` `aesop` `aesop_cat` `apply?` `apply_assumption` `apply_mod_cast` `apply_rules` `assumption_mod_cast` `bound` `bv_decide` `bv_omega` `cancel_denoms` `cat_disch` `cc` `compute_degree` `continuity` `dec_trivial` `decide` `exact?` `exact_mod_cast` `field` `field_simp` `finish` `finiteness` `fun_prop` `gcongr` `grind` `group` `hint` `interval` `itauto` `lia` `linarith` `linear_combination` `linear_combination'` `measurability` `mod_cast` `module` `monicity` `native_decide` `nia` `nlinarith` `nomatch` `noncomm_ring` `norm_cast` `norm_fin` `norm_num` `norm_num1` `omega` `order` `polyrith` `positivity` `push` `push_cast` `qify` `reduce_mod_char` `rify` `ring` `ring1` `ring_exp` `ring_nf` `rw?` `simp` `simp_all` `simp_all_arith` `simp_arith` `simp_intro` `simp_wf` `simpa` `solve_by_elim` `subsingleton` `tauto` `tidy` `zify` |
| trivial-close | `ac_rfl` `assumption` `contradiction` `done` `eq_refl` `exact_decide` `infer_instance` `refl` `rfl` `trivial` |
| exact | `exact` `exacts` `from` |
| apply | `apply` `apply_fun` `congr` `congr!` `congrm` `convert` `convert_to` `eapply` `fapply` `filter_upwards` `lift` `mono` `peel` `rapply` `refine` `refine'` |
| rewrite | `arg` `beta_reduce` `change` `conv` `conv_lhs` `conv_rhs` `delta` `dsimp` `dsimp_only` `dunfold` `enter` `equals` `erw` `eta_reduce` `grw` `lhs` `nth_rewrite` `nth_rw` `push_neg` `reduce` `rewrite` `rhs` `rw` `rw_mod_cast` `rwa` `simp_all_only` `simp_only` `simp_rw` `subst` `subst_vars` `substs` `unfold` `unfold_coes` `unfold_let` `whnf` |
| intro | `assume` `intro` `intros` `introsI` `introv` `rintro` `rintros` |
| have | `have` `haveI` `observe` `replace` |
| obtain | `cases'` `choose` `obtain` `rcases` |
| show | `show` |
| suffices | `rsuffices` `suffices` `wlog` |
| induction | `decreasing_by` `fun_induction` `induction` `induction'` `induction_on` `strong_induction_on` `termination_by` |
| case-split | `by_cases` `cases` `cases_matching` `cases_type` `casesm` `fin_cases` `if` `injection` `interval_cases` `match` `mod_cases` `obtain_alt` `rcases_alt` `rintro_alt` `split` `split_ifs` |
| ext | `ext` `ext1` `funext` |
| witness | `exists` `existsi` `refine_exists` `use` |
| constructor | `and_intros` `constructor` `econstructor` `fconstructor` `left` `refine_struct` `right` `split_ands` |
| calc | `calc` `trans` `transitivity` |
| contra | `absurd` `by_contra` `by_contradiction` `contrapose` `exfalso` |
| context | `borelize` `classical` `clear` `clear_value` `exactI` `extract_goal` `generalize` `generalize_proofs` `inhabit` `let` `letI` `lift_lets` `open` `pick_goal` `rename` `rename_i` `resetI` `revert` `rotate_left` `rotate_right` `set` `specialize` `substI` `swap` `symm` `symmetry` `unfreezingI` |
| combinator | `all_goals` `any_goals` `first` `focus` `iterate` `on_goal` `repeat` `skip` `solve` `try` `work_on_goal` |
| structure | `case` `next` |
| sorry | `admit` `sorry` `stop` |
| domain | `iapply` `icases` `iclear` `iempintro` `iexact` `iexists` `iframe` `ihave` `iintro` `ileft` `imod` `imodintro` `inext` `ipureintro` `irename` `irevert` `iright` `ispecialize` `isplit` `isplitl` `isplitr` `itrivial` `p2m_exact_reverting` `wp_apply` `wp_bind` `wp_pures` |

Prefix rules: none.

rocq:

| class | heads |
|---|---|
| automation | `CatReducible` `SvD.fsetdec` `algebra` `auto` `autorewrite` `autounfold` `btauto` `cancel` `congruence` `crush` `decide_equality` `dintuition` `easy` `eauto` `entailer` `eomega` `extlia` `f_equiv` `field` `field_simplify` `firstorder` `fmap_solve` `fourier` `fsetdec` `fwd` `hammer` `hauto` `in_crush` `intuition` `itauto` `lia` `lias` `lra` `naive_solver` `nia` `normalize` `now` `nra` `nsatz` `omega` `pcuic` `psatz` `qauto` `remove_bools_options` `rep_lia` `ring` `ring_lia` `ring_simplify` `rtauto` `sauto` `set_solver` `sfirstorder` `simplify_eq` `solve_ndisj` `solve_proper` `ssromega` `tauto` `typeclasses_eauto` `xomega` `zify` |
| trivial-close | `assumption` `contradiction` `discriminate` `done` `eassumption` `idpath` `reflexivity` `tas` `tea` `trea` `trivial` |
| exact | `eexact` `exact` |
| apply | `apply` `apply_in_hyps` `congr` `eapply` `eexploit` `exploit` `f_equal` `find_apply_hyp_hyp` `find_apply_lem_hyp` `lapply` `napply` `nrapply` `rapply` `refine` `sep_apply` `simple_apply` `simple_eapply` `simple_refine` `snrapply` `srapply` `use` |
| rewrite | `cbn` `cbv` `change` `compute` `erewrite` `find_rewrite` `fold` `hnf` `lazy` `native_compute` `pattern` `pull_Zmod` `push_Zmod` `red` `replace` `rewrite` `rewrite_strat` `setoid_rewrite` `simp` `simpl` `simpl_rev` `subst` `under` `unfold` `unlock` `vm_compute` |
| intro | `=>` `Intro` `Intros` `iIntros` `intro` `intros` `introv` `move=>` |
| have | `assert` `assert_PROP` `eassert` `epose_proof` `have` `iAssert` `pose_proof` |
| obtain | `break_exists` `decompose` `iDestruct` |
| show | `show` |
| suffices | `cut` `eenough` `enough` `suff` `suffices` `wlog` |
| induction | `cofix` `dependent_induction` `depind` `ecofix` `eelim` `einduction` `einit` `elim` `fix` `functional_induction` `funelim` `gcofix` `ginit` `iInduction` `iLöb` `induction` `pcofix` `simple_induction` |
| case-split | `bdestruct` `case` `case_eq` `case_leq` `case_match` `decide` `depelim` `dependent_destruction` `dependent_inversion` `destr` `destruct` `destruct_with_eqn` `edestruct` `find_inversion` `if_tac` `inv` `invc` `inversion` `inversion_clear` `invs` `noconf` `simple_destruct` `simple_if_tac` `simple_inversion` |
| ext | `extensionality` `functional_extensionality` `funext` |
| witness | `Exists` `eexists` `exists` `exists2` `iExists` `instantiate` |
| constructor | `constructor` `econstructor` `eleft` `eright` `esplit` `esplits` `iSplit` `iSplitL` `iSplitR` `left` `right` `split` `splits` `ssplit` |
| calc | `etrans` `etransitivity` `intermediate_path` `trans` `transitivity` |
| contra | `Contradict` `absurd` `contradict` `exfalso` |
| context | `clear` `clearbody` `cycle` `dependent_rewrite` `epose` `eset` `forget` `generalize` `iClear` `iFrame` `iLeft` `iModIntro` `iNext` `iPoseProof` `iPureIntro` `iRevert` `iRight` `iSpecialize` `idtac` `injection` `move` `move/` `move:` `pose` `remember` `rename` `revert` `revgoals` `set` `shelve` `specialize` `swap` `symmetry` `unshelve` |
| combinator | `abstract` `all` `dispatch` `do` `first` `last` `lazymatch` `let` `match` `once` `par` `progress` `repeat` `solve` `time` `timeout` `try` `tryif` |
| sorry | `Abort` `Admitted` `admit` `give_up` |
| domain | `TransfInstr` `erbind` `forward` `forward_call` `forward_if` `rbind` `start_function` `tau_steps` |

Prefix rules: `^i[A-Z]\w*$` gives domain, `^wp_\w+$` gives domain, `^ssprove\w*$` gives domain, `^fcf_\w+$` gives domain, `^solve_\w+$` gives automation, `^destruct_\w+$` gives case-split, `^simplify_\w+$` gives automation.

isabelle:

| class | heads |
|---|---|
| automation | `algebra` `approximation` `argo` `arith` `auto` `auto2` `best` `bestsimp` `blast` `clarify` `clarsimp` `code_simp` `eval` `fast` `fastforce` `force` `hoare_auto` `intro_classes` `intro_locales` `iprover` `lexicographic_order` `linarith` `measurable` `meson` `metis` `monad_eq` `normalization` `order` `pat_completeness` `pred_auto` `pred_simp` `presburger` `real_asymp` `refine_rcg` `refine_vcg` `rel_auto` `rel_simp` `safe` `satx` `sep_auto` `sep_cancel` `sep_solve` `sepref` `simp` `simp_all` `simp_arith` `size_change` `sledgehammer` `slow` `slowsimp` `smt` `sos` `standard` `transfer_prover` `unat_arith` `unfold_locales` `vc_solve` `vcg` `wp` `wpsimp` |
| trivial-close | `-` `.` `..` `assumption` `contradiction` `done` `fact` `succeed` `this` |
| apply | `atomize_elim` `cut_tac` `dest` `drule` `drule_tac` `elim` `erule` `erule_tac` `frule` `frule_tac` `intro` `relation` `rule` `rule_format` `rule_tac` `rules` |
| rewrite | `fold` `hypsubst` `hypsubst_thin` `rewrite` `simp_only` `simplesubst` `subst` `unfold` `unfolding` |
| intro | `assume` `fix` `presume` |
| have | `have` `hence` `subgoal_tac` |
| obtain | `guess` `obtain` |
| show | `show` `thus` |
| induction | `coinduct` `coinduction` `induct` `induct_tac` `induction` `infinite_descent` `nominal_induct` |
| case-split | `case_tac` `cases` `consider` `ind_cases` |
| calc | `also` `finally` |
| context | `atomize` `back` `defer` `define` `including` `insert` `interpret` `let` `note` `prefer` `rename_tac` `rotate_tac` `supply` `tactic` `thin_tac` `transfer` `write` |
| combinator | `all` `fail` `use` |
| structure | `apply` `apply_end` `by` `case` `goal_cases` `next` `proof` `qed` `subgoal` `{` |
| facts | `from` `moreover` `then` `ultimately` `using` `with` |
| sorry | `oops` `sorry` |
| domain | `ccorres` `cinit` `corres` `corressimp` `crunch` `csymbr` `ctac` |

Prefix rules: `^wp\w*$` gives automation, `^c?corres\w*$` gives domain.

<!-- END GENERATED -->
