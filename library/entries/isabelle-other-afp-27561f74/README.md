# Equality with LEAST by minimum characterisation for Harry's measure (IMO 2019 Q5)

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | isabelle |
| Status | draft |
| Source | [afp](../../sources/afp/SOURCE.md) at `07cd9ca548d1` |
| Licence | `LicenseRef-unknown` |

## Intent

Prove that `harry_meas xs` is the least number of steps after which Harry's
coin process leaves no heads, by the two-part minimum characterisation
`Least_equality`: show the value satisfies the predicate, and show every other
satisfying value is at least it. The two halves are already separate lemmas,
so the proof is one line per obligation.

## The decomposition

### parent `harry_meas_eq_LEAST`: [`thys/IMO2019/IMO2019_Q5.thy` lines 315-323](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/IMO2019/IMO2019_Q5.thy#L315-L323) ([local copy](code/thys/IMO2019/IMO2019_Q5.thy))

```isabelle
theorem "harry_meas xs = (LEAST n. True \<notin> set ((harry_step ^^ n) xs))"
proof (rule sym, rule Least_equality, goal_cases)
  show "True \<notin> set ((harry_step ^^ harry_meas xs) xs)"
    by (rule True_notin_funpow_harry_step)
next
  case (2 y)
  show ?case
    by (rule ccontr) (use 2 True_in_funpow_harry_step[of y] in auto)
qed
```

### child `True_in_funpow_harry_step`: [`thys/IMO2019/IMO2019_Q5.thy` lines 277-292](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/IMO2019/IMO2019_Q5.thy#L277-L292) ([local copy](code/thys/IMO2019/IMO2019_Q5.thy))

```isabelle
lemma True_in_funpow_harry_step:
  assumes "n < harry_meas xs"
  shows   "True \<in> set ((harry_step ^^ n) xs)"
  using assms
proof (induction n arbitrary: xs)
  case 0
  show ?case by (rule ccontr) (use 0 in auto)
next
  case (Suc n)
  have "True \<in> set xs" by (rule ccontr) (use Suc in auto)
  have "(harry_step ^^ Suc n) xs = (harry_step ^^ n) (harry_step xs)"
    by (simp only: funpow_Suc_right o_def)
  also have "True \<in> set \<dots>"
    using Suc \<open>True \<in> set xs\<close> by (intro Suc) (auto simp: harry_meas_step)
  finally show ?case .
qed
```

### child `True_notin_funpow_harry_step`: [`thys/IMO2019/IMO2019_Q5.thy` lines 294-309](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/IMO2019/IMO2019_Q5.thy#L294-L309) ([local copy](code/thys/IMO2019/IMO2019_Q5.thy))

```isabelle
lemma True_notin_funpow_harry_step: "True \<notin> set ((harry_step ^^ harry_meas xs) xs)"
proof (induction "harry_meas xs" arbitrary: xs)
  case (Suc n)
  have "True \<in> set xs" by (rule ccontr) (use Suc in auto)
  have "(harry_step ^^ harry_meas xs) xs = (harry_step ^^ Suc n) xs"
    by (simp only: Suc)
  also have "\<dots> = (harry_step ^^ n) (harry_step xs)"
    by (simp only: funpow_Suc_right o_def)
  also have "\<dots> = (harry_step ^^ (harry_meas xs - 1)) (harry_step xs)"
    by (simp flip: Suc(2))
  also have "harry_meas xs - 1 = harry_meas (harry_step xs)"
     using \<open>True \<in> set xs\<close> by (subst harry_meas_step) auto
  also have "True \<notin> set ((harry_step ^^ \<dots>) (harry_step xs))"
    using Suc \<open>True \<in> set xs\<close> by (intro Suc) (auto simp: harry_meas_step)
  finally show ?case .
qed auto
```

### context `harry_meas_step`: [`thys/IMO2019/IMO2019_Q5.thy` lines 259-260](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/IMO2019/IMO2019_Q5.thy#L259-L260) ([local copy](code/thys/IMO2019/IMO2019_Q5.thy))

```isabelle
lemma harry_meas_step: "True \<in> set xs \<Longrightarrow> harry_meas (harry_step xs) = harry_meas xs - 1"
  using harry_meas_step_aux[of xs] by simp
```

### context `harry_meas_step_aux`: [`thys/IMO2019/IMO2019_Q5.thy` lines 226-257](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/IMO2019/IMO2019_Q5.thy#L226-L257) ([local copy](code/thys/IMO2019/IMO2019_Q5.thy))

```isabelle
lemma harry_meas_step_aux:
  assumes "True \<in> set xs"
  shows   "harry_meas xs = Suc (harry_meas (harry_step xs))"
  using assms
proof (induction xs rule: length_induct)
  case (1 xs)
  hence IH: "harry_meas ys = Suc (harry_meas (harry_step ys))"
    if "length ys < length xs" "True \<in> set ys" for ys
    using that by blast

  show ?case
  proof (cases xs rule: head_last_cases)
    case (True ys)
    thus ?thesis by (auto simp: IH)
  next
    case (False ys)
    thus ?thesis using "1.prems" by (auto simp: IH)
  next
    case (False_True ys)
    thus ?thesis
    proof (cases "True \<in> set ys")
      case False
      define n where "n = length ys + 1"
      have "n > 0" by (simp add: n_def)
      from False have "ys = replicate (n - 1) False"
        unfolding n_def by (induction ys) auto
      with False_True \<open>n > 0\<close> have [simp]: "xs = replicate n False @ [True]"
        by (cases n) auto
      show ?thesis using \<open>n > 0\<close> by auto
    qed (auto simp: IH False_True harry_step_False_True harry_meas_False_True)
  qed (use 1 in auto)
qed
```

How the parts fit. The parent goal is `harry_meas xs = (LEAST n. True ∉ set
((harry_step ^^ n) xs))` (the theorem is anonymous in the source; the name
`harry_meas_eq_LEAST` is a gloss). `rule sym` first swaps the sides, because
`Least_equality` is stated for `(LEAST n. P n) = x`. Then `rule Least_equality`
produces its two premises as the two goals:

- the *satisfying-value* goal `True ∉ set ((harry_step ^^ harry_meas xs) xs)`,
  closed by `rule True_notin_funpow_harry_step`;
- the *minimality* goal `⋀y. True ∉ set ((harry_step ^^ y) xs) ⟹ harry_meas xs
  ≤ y`, closed by `rule ccontr` together with `use 2 True_in_funpow_harry_step[of
  y]`: assuming `harry_meas xs > y`, i.e. `y < harry_meas xs`, that lemma yields
  a head at step `y`, contradicting goal 2's premise.

Each child is a self-contained induction over the number of steps, and each
closes from the shared step lemma `harry_meas_step` (context) plus automation,
without needing its sibling:

- `True_in_funpow_harry_step` (`n < harry_meas xs` implies a head at step `n`)
  is a 16-line induction on `n`; the step case rewrites `(harry_step ^^ Suc n)
  xs` to `(harry_step ^^ n) (harry_step xs)` and applies the induction
  hypothesis, using `harry_meas_step` to lower the measure by one.
- `True_notin_funpow_harry_step` (no head at step `harry_meas xs`) is a
  16-line induction on `harry_meas xs`; the step case unfolds the funpow and
  again uses `harry_meas_step`.

`harry_meas_step` is itself `using harry_meas_step_aux` (context), the
induction proving that one step of the process decreases the measure by exactly
one. Below that the chain bottoms out in infrastructure lemmas:
`harry_meas_step_aux` cases on the list shape with `head_last_cases` and uses
`harry_step_False_True`, which uses `flip_append1`. So the longest chain of
project lemmas below the main theorem is `True_in_funpow_harry_step` →
`harry_meas_step` → `harry_meas_step_aux` → `harry_step_False_True` →
`flip_append1` (depth 5).

The two children are good leaves because each is a single named statement whose
proof closes on its own from `harry_meas_step` and library automation — no
sibling is needed inside either child, so a bounded prover filling one hole does
not need the other.

## Why it is good

1. The parent's proof cites `True_notin_funpow_harry_step`, which closes the
   first (satisfying-value) obligation of `Least_equality` (*check*, the
   `cites` form is decided against the parent site, lines 315-323).
2. The parent's proof cites `True_in_funpow_harry_step`, which closes the second
   (minimality) obligation (*check*, the `cites` form against lines 315-323).
3. `True_in_funpow_harry_step` is declared at lines 277-292 of the copied file
   (*check*, the `declared` form).
4. `True_notin_funpow_harry_step` is declared at lines 294-309 of the copied
   file (*check*, the `declared` form).
5. The longest chain of project lemmas below the main theorem is 5 lemmas deep,
   counted by following the citations at lines 322, 290, 260, 255 and 195
   (*measurement*; this records `shape.depth`).

In my opinion the detail worth copying is that the author stated the two
directions of the minimum characterisation as two separate lemmas *before* the
theorem, so the theorem's proof is nothing but the characterisation glue and the
obligations are already-filled holes.

## When to use it, and when not

Use it when a goal is an equality `x = LEAST n. P n` and you already have, or
can state, the two halves separately: a satisfying-value lemma `P x` and a
lower-bound lemma `P y ⟹ x ≤ y`. Then `rule Least_equality` (after `rule sym`
if the equality is written the other way round) turns the goal into exactly
those two named lemmas. Avoid it when the satisfying value must be constructed
as part of the proof (then the construction, not the characterisation, is the
content); when you actually want an iff (`P x ⟷ x = LEAST n. P n`) or an order
antisymmetry between two concrete terms rather than a `LEAST`; or when the
ambient type has no well-order, so `LEAST` and the two-part rule are not
available.

## Consequences

The move creates exactly two obligations (the premises of `Least_equality`):
satisfy the predicate, and bound every other satisfying value from below. Each
is a named child here, so the glue is one line per obligation. The minimality
obligation is discharged by contradiction against the satisfying-value direction
of the sibling lemma, so the two children are not independent — minimality rides
on the contrapositive of `True_in_funpow_harry_step`. A failure mode is that if
the two directions are not stated as separate lemmas, the characterisation
collapses back into one inline proof and the skeleton offers no holes.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: True_in_funpow_harry_step@thys/IMO2019/IMO2019_Q5.thy:322, True_notin_funpow_harry_step@thys/IMO2019/IMO2019_Q5.thy:318; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, True_notin_funpow_harry_step) -> cites: True_notin_funpow_harry_step occurs at thys/IMO2019/IMO2019_Q5.thy:318 | check_claims.py |
| 2 | verified | cites(parent, True_in_funpow_harry_step) -> cites: True_in_funpow_harry_step occurs at thys/IMO2019/IMO2019_Q5.thy:322 | check_claims.py |
| 3 | verified | declared(True_in_funpow_harry_step, thys/IMO2019/IMO2019_Q5.thy, 277-292) -> declared: True_in_funpow_harry_step is declared at thys/IMO2019/IMO2019_Q5.thy:277 | check_claims.py |
| 4 | verified | declared(True_notin_funpow_harry_step, thys/IMO2019/IMO2019_Q5.thy, 294-309) -> declared: True_notin_funpow_harry_step is declared at thys/IMO2019/IMO2019_Q5.thy:294 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/isabelle-prover/mirror-afp-devel at commit `07cd9ca548d180f234c63f06bf5d1cb85c7fc5df`, under `LicenseRef-unknown`; see the [source note](../../sources/afp/SOURCE.md) for the licence text and attribution.
