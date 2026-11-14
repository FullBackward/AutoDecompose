# One operation lemma per component: ilock_cycle preserves ilock_type_inv

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | isabelle |
| Status | draft |
| Source | [utp-main](../../sources/utp-main/SOURCE.md) at `ffd472022798` |
| Licence | `BSD-3-Clause` |

## Intent

The cyclic interlocking controller `ilock_cycle` is defined as the sequential
composition of four operations (`set_relays ;; clear_relays ;; set_switches ;;
set_signals`). Rather than prove the type invariant straight through that
composition, the theory gives each operation its own preservation lemma
`{ilock_type_inv} op {ilock_type_inv}`, each closed by one shared method, so
the main theorem is nothing but `unfold ilock_cycle_def`, `hoare_split`, and
one `rule` application per component.

## The decomposition

### parent `ilock_cycle`: [`fmi/Interlocking.thy` lines 193-200](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L193-L200) ([local copy](code/fmi/Interlocking.thy))

```isabelle
lemma "\<lbrace>ilock_type_inv\<rbrace>ilock_cycle\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
apply (unfold ilock_cycle_def)
apply (hoare_split)
apply (rule set_relays_type_inv)
apply (rule clear_relays_type_inv)
apply (rule set_switches_type_inv)
apply (rule set_signals_type_inv)
done
```

### child `set_relays_type_inv`: [`fmi/Interlocking.thy` lines 173-176](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L173-L176) ([local copy](code/fmi/Interlocking.thy))

```isabelle
lemma set_relays_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>set_relays\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
(* unfolding set_relays_def by (hoare_auto) *)
  unfolding set_relays_def by (ilock_type_inv_tac)
```

### child `clear_relays_type_inv`: [`fmi/Interlocking.thy` lines 178-181](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L178-L181) ([local copy](code/fmi/Interlocking.thy))

```isabelle
lemma clear_relays_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>clear_relays\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
(* unfolding clear_relays_def by (hoare_auto) *)
  unfolding clear_relays_def by (ilock_type_inv_tac)
```

### child `set_switches_type_inv`: [`fmi/Interlocking.thy` lines 183-186](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L183-L186) ([local copy](code/fmi/Interlocking.thy))

```isabelle
lemma set_switches_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>set_switches\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
(* unfolding set_switches_def by (hoare_auto) *)
  unfolding set_switches_def by (ilock_type_inv_tac)
```

### child `set_signals_type_inv`: [`fmi/Interlocking.thy` lines 188-191](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L188-L191) ([local copy](code/fmi/Interlocking.thy))

```isabelle
lemma set_signals_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>set_signals\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
(* unfolding set_signals_def by (hoare_auto) *)
  unfolding set_signals_def by (ilock_type_inv_tac)
```

### context `ilock_cycle_def`: [`fmi/Interlocking.thy` lines 133-134](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L133-L134) ([local copy](code/fmi/Interlocking.thy))

```isabelle
definition ilock_cycle :: "ilock_state hrel" where [urel_defs]:
"ilock_cycle = (set_relays ;; clear_relays ;; set_switches ;; set_signals)"
```

### context `ilock_type_inv`: [`fmi/Interlocking.thy` lines 144-150](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L144-L150) ([local copy](code/fmi/Interlocking.thy))

```isabelle
definition ilock_type_inv :: "ilock_state upred" where [urel_defs]:
"ilock_type_inv = (
  #\<^sub>u(&cdv) =\<^sub>u 11 \<and>
  #\<^sub>u(&tc) =\<^sub>u 4 \<and>
  #\<^sub>u(&relays) =\<^sub>u 5 \<and>
  #\<^sub>u(&signals) =\<^sub>u 3 \<and>
  #\<^sub>u(&switches) =\<^sub>u 5)"
```

### context `ilock_type_inv_rules`: [`fmi/Interlocking.thy` lines 154-161](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L154-L161) ([local copy](code/fmi/Interlocking.thy))

```isabelle
lemma ilock_type_inv_rules:
"\<lbrace>ilock_type_inv\<rbrace>S\<lbrace>ilock_type_inv\<rbrace>\<^sub>u \<Longrightarrow>
 \<lbrace>ilock_type_inv \<and> P\<rbrace>S\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
"`ilock_type_inv \<Rightarrow> s \<dagger> ilock_type_inv` \<Longrightarrow>
 `ilock_type_inv \<and> P \<Rightarrow> s \<dagger> ilock_type_inv`"
apply (rel_simp)
apply (erule inv_subst_weakening_lemma)
done
```

### context `ilock_type_inv_tac`: [`fmi/Interlocking.thy` lines 163-166](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L163-L166) ([local copy](code/fmi/Interlocking.thy))

```isabelle
text {* The tactic below is a bit quicker than @{method hoare_auto}. *}

method ilock_type_inv_tac =
  (hoare_split_inv add: ilock_type_inv_rules; rel_simp)
```

### context `inv_subst_weakening_lemma`: [`fmi/Interlocking.thy` lines 17-20](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L17-L20) ([local copy](code/fmi/Interlocking.thy))

```isabelle
lemma inv_subst_weakening_lemma:
"`I \<Rightarrow> s \<dagger> I` \<Longrightarrow> `I \<and> P \<Rightarrow> s \<dagger> I`"
apply (rel_simp)
done
```

How the parts fit. The parent is an anonymous lemma (the source writes `lemma
"…"` with no identifier). Its proof first unfolds the definition to
`set_relays ;; clear_relays ;; set_switches ;; set_signals` (line 194), then
`hoare_split` (line 195) turns that sequential composition into one
Hoare-triple goal per component, and the four `apply (rule …)` lines discharge
each goal with the matching per-operation lemma:

```
ilock_cycle (parent, 193-200)  [anonymous lemma; goal at 193]
├─ set_relays    → set_relays_type_inv    (196; 173-176)
├─ clear_relays  → clear_relays_type_inv  (197; 178-181)
├─ set_switches  → set_switches_type_inv  (198; 183-186)
└─ set_signals   → set_signals_type_inv   (199; 188-191)
    each *_type_inv ──closes by── unfolding <op>_def by (ilock_type_inv_tac)
    ilock_type_inv_tac (165-166) ──adds── ilock_type_inv_rules (154-161)
    ilock_type_inv_rules ──uses── inv_subst_weakening_lemma (160; 17-20)
```

Each child is a good leaf: a self-contained lemma whose statement is that
operation's own Hoare triple and whose proof closes on its own, citing no
sibling and no parent. All four are near-identical — the only difference is
the operation name they unfold — and each is closed by the same method
`ilock_type_inv_tac`, defined as `hoare_split_inv add: ilock_type_inv_rules;
rel_simp` (165-166). That method feeds the shared project lemma
`ilock_type_inv_rules` (154-161), the weakening that lets a Hoare triple hold
under a strengthened precondition; `ilock_type_inv_rules` in turn closes by
`rel_simp` and `erule inv_subst_weakening_lemma` (160), whose leaf
`inv_subst_weakening_lemma` (17-20) is a `rel_simp`-only fact. The chain of
project lemmas below the parent is therefore three deep: the four children,
then `ilock_type_inv_rules`, then `inv_subst_weakening_lemma`.

## Why it is good

1. `set_relays_type_inv` occurs in the parent site, at line 196, as one of
   the four `rule` applications that assemble the proof (`check`,
   [lines 193-200](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L193-L200)).
2. Lines 173-200 of `fmi/Interlocking.thy` contain no `sorry`, so every child
   and the parent are fully proved, not admitted (`check`,
   [lines 173-200](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L173-L200)).
3. The shape is a measurement: an 8-line parent (193-200) whose proof body is
   four `rule` applications plus `done` delegates the invariant proof to four
   children of 4 lines each, for `direct_lemmas 4`, `glue_lines 8`,
   `child_lines [4,4,4,4]` (`measurement`, line counts at the pinned commit).
4. The authors state the decomposition in a comment: "We break down the
   cyclic behaviour into four separate operations." (`author-statement`,
   [line 89](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L89)).
5. The same per-component decomposition is reused verbatim for the relays
   invariant: the anonymous lemma at 308-315 unfolds `ilock_cycle_def`,
   `hoare_split`s, and applies `set_relays_relays_inv`,
   `clear_relays_relays_inv`, `set_switches_relays_inv`,
   `set_signals_relays_inv` (292-306) (`known-use`,
   [lines 292-315](https://github.com/isabelle-utp/utp-main/blob/ffd472022798e60f0385030682b7a07fbeb49e68/fmi/Interlocking.thy#L292-L315)).

In my opinion the detail worth copying is the uniformity of the family: the
four children differ only in the operation name they unfold, one shared method
closes them all, and the parent collapses to four `rule` applications, so the
whole type-invariant section is about 28 lines.

## When to use it, and when not

Use it when the program under proof is a named sequential composition of
operations and the same invariant must hold across each of them: give each
operation a preservation lemma and let the main theorem be `unfold <def>`,
`hoare_split`, then one `rule` per component. The per-operation lemmas are
then independent, bounded units that can be proved, checked and reused
separately.

Avoid it when one operation's preservation needs a stronger precondition than
the shared invariant alone — the same file's switches/signals sections show
that case, and they fall back to a heavier tactic rather than the uniform
`ilock_type_inv_tac`. Avoid it also when the operations share a substantial
common sub-proof: factor that into one shared lemma (here
`ilock_type_inv_rules` and `inv_subst_weakening_lemma`) rather than repeating
it inside each operation's lemma.

## Consequences

The move creates one named obligation per operation, all of the same shape
`{ilock_type_inv} op {ilock_type_inv}`, which is why one method closes them
all. The parent's `hoare_split` turns the sequential composition into one goal
per component, and the proof closes only if every component has its lemma; a
missing component lemma leaves an unproved goal, not a silent gap. The four
children are independent of each other but all depend on the shared
`ilock_type_inv_rules` (depth 2) and its dependency
`inv_subst_weakening_lemma` (depth 3), so a defect there breaks all four at
once. Adding a fifth operation means one more child lemma and one more `rule`
line. The uniform tactic works only because each operation preserves the type
invariant outright; an operation that needs a stronger precondition (as the
file's later sections do) breaks the uniform method and needs its own tactic.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: set_relays_type_inv@fmi/Interlocking.thy:196, clear_relays_type_inv@fmi/Interlocking.thy:197, set_switches_type_inv@fmi/Interlocking.thy:198, set_signals_type_inv@fmi/Interlocking.thy:199; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none; oops (listed, not failed): fmi/Interlocking.thy:387 (oops), fmi/Interlocking.thy:424 (oops) | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, set_relays_type_inv) -> cites: set_relays_type_inv occurs at fmi/Interlocking.thy:196 | check_claims.py |
| 2 | verified | no_sorry(fmi/Interlocking.thy, 173-200) -> no_sorry: none of sorry in fmi/Interlocking.thy:173-200 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/isabelle-utp/utp-main at commit `ffd472022798e60f0385030682b7a07fbeb49e68`, under `BSD-3-Clause`; see the [source note](../../sources/utp-main/SOURCE.md) for the licence text and attribution.
