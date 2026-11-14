# No-prime spec inequality as a calc-chain through the central binomial (2n n)

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | rocq |
| Status | accepted |
| Source | [bertrand](../../sources/bertrand/SOURCE.md) at `033b1a8f1a9c` |
| Licence | `LGPL-2.1-or-later` |

## Intent

Reduce the goal "if no prime lies between n and 2n then
`power 4 n < power (2*n) (div (sqr (2*n)) 2) * power 4 (div (2*n) 3)`" to two
bound lemmas on the central binomial `binomial (2*n) n` — the lower bound
`binomial_even` and the upper bound `upper_bound` — then chain them through the
intermediate `2 * n * binomial (2*n) n` with `Nat.le_lt_trans` and
`Nat.lt_le_trans`.

## The decomposition

### parent `no_prime_imp_spec_inegality`: [`theories/Bertrand.v` lines 187-220](https://github.com/rocq-community/bertrand/blob/033b1a8f1a9c121855b6b78cd55154d3c09e1c23/theories/Bertrand.v#L187-L220) ([local copy](code/theories/Bertrand.v))

```coq
Theorem no_prime_imp_spec_inegality :
 forall n : nat,
 power 2 7 <= n ->
 (forall p : nat, n < p -> p < 2 * n -> ~ prime p) ->
 power 4 n < power (2 * n) (div (sqr (2 * n)) 2) * power 4 (div (2 * n) 3).
Proof.
intros n H H0.
apply Nat.le_lt_trans with (2 * n * binomial (2 * n) n).
replace 4 with (power 2 2); auto with arith.
rewrite power_power; apply binomial_even; auto with arith.
apply Nat.lt_le_trans with (2 := H); auto with arith; simpl in |- *;
 auto with arith.
rewrite <- (Nat.sub_add 1 (div (sqr (2 * n)) 2)).
rewrite Nat.add_comm.
rewrite <- power_mult; rewrite power_SO.
rewrite <- (Nat.mul_assoc (2 * n)).
apply mult_lt_bis; auto with arith.
apply Nat.lt_le_trans with (2 * power 2 7); auto with arith; simpl in |- *;
 auto with arith.
apply upper_bound; auto with arith.
apply Nat.lt_succ_r.
apply lt_mult_right_anti with (z := 2).
apply Nat.lt_trans with (sqr (2 * n)).
apply Nat.succ_lt_mono; apply mult_id_lt_inv; auto with arith.
apply Nat.le_lt_trans with (2 * n).
apply Nat.le_trans with (2 * power 2 3); auto with arith.
simpl in |- *; repeat apply le_n_S; auto with arith.
apply Nat.le_trans with (2 * power 2 7); auto with arith.
apply le_mult; auto with arith.
apply power_le_mono; auto with arith.
apply sqr_lt.
change (sqr (2 * n) < 2 * (1 + div (sqr (2 * n)) 2));
 apply div_lt; auto with arith.
Qed.
```

### child `upper_bound`: [`theories/Bertrand.v` lines 27-184](https://github.com/rocq-community/bertrand/blob/033b1a8f1a9c121855b6b78cd55154d3c09e1c23/theories/Bertrand.v#L27-L184) ([local copy](code/theories/Bertrand.v))

```coq
Theorem upper_bound :
 forall n : nat,
 power 2 7 <= n ->
 (forall p : nat, n < p -> p < 2 * n -> ~ prime p) ->
 binomial (2 * n) n <
 power (2 * n) (div (sqr (2 * n)) 2 - 1) * power 4 (div (2 * n) 3).
Proof.
intros n H H0.
cut (0 < n); [ intros Hn | apply Nat.lt_le_trans with (2 := H); simpl in |- * ];
 auto with arith.
cut (0 < binomial (2 * n) n);
 [ intros Hc
 | replace (2 * n) with (n + n); try apply binomial_lt; auto with arith; ring ].
cut (sqr (2 * n) < div (2 * n) 3); [ intros Hd | idtac ].
rewrite (fun x y : nat => factorization (binomial x y) (div (2 * n) 3));
 auto with arith.
rewrite prod_nm_split with (r := sqr (2 * n)); auto with arith.
apply
 Nat.lt_le_trans
  with
    (prod_nm 0 (sqr (2 * n))
       (fun x : nat =>
        power (prime_dirac x) (power_div (binomial (2 * n) n) x)) *
     power 4 (div (2 * n) 3)).
apply mult_lt_bis.
apply Nat.lt_le_trans with (power 1 (S (sqr (2 * n)))); auto with arith.
rewrite SO_power; auto with arith.
rewrite <- prod_nm_c with (p := 0); apply prod_nm_le; auto with arith.
intros x H1 H2.
apply Nat.le_succ_l; auto with arith.
apply power_lt_O.
case (prime_dec x); intros Hx;
 [ rewrite prime_prime_dirac | rewrite not_prime_prime_dirac ];
 auto with arith.
generalize Hx; case x; auto with arith; intros Hx1; Contradict Hx1;
 auto with arith.
rewrite <- (fun x y f => Nat.mul_1_l (prod_nm x y f)).
pattern 1 at 1 in |- *; rewrite <- (SO_power (S (sqr (2 * n)))).
apply
 Nat.le_lt_trans with (prod_nm 0 (div (2 * n) 3) (fun x : nat => prime_dirac x));
 auto with arith.
rewrite prod_nm_split with (p := 0) (r := sqr (2 * n)); auto with arith.
apply le_mult.
rewrite <- prod_nm_c with (p := 0).
apply prod_nm_le.
intros x H7 H8; unfold prime_dirac in |- *; generalize (primeb_correct x);
 case (primeb x); auto with arith.
case x; auto with arith.
intros H9; Contradict H9; auto with arith.
apply prod_nm_le.
intros x H7 H8.
unfold prime_dirac in |- *; generalize (primeb_correct x); case (primeb x);
 intros Hx.
pattern x at 3 in |- *; rewrite <- power_SO.
apply power_le_mono.
generalize Hx; case x; auto with arith.
intros H9; Contradict H9; auto with arith.
apply power_div_binomial2; auto with arith.
apply Nat.lt_le_trans with (1 := sqr_lt (2 * n)).
replace (power x 2) with (x * x); [ apply le_mult | simpl in |- *; ring ];
 auto with arith.
rewrite SO_power; auto with arith.
apply prod_prime_lt; auto with arith.
apply Nat.lt_le_trans with (2 := Hd).
apply Nat.lt_succ_r; auto with arith.
apply (sqr_mono 1).
apply Nat.le_trans with (2 * power 2 7); auto with arith; simpl in |- *;
 auto with arith.
apply le_mult.
apply
 prod_prime_le
  with
    (f := fun x : nat =>
          power (prime_dirac x) (power_div (binomial (2 * n) n) x));
 auto with arith.
replace (power 2 4) with (sqr (2 * power 2 7)); [ idtac | auto ].
apply sqr_mono; auto with arith.
intros x H7 H8.
rewrite prime_prime_dirac; auto; apply power_div_binomial1; auto.
intros x H7 H8.
rewrite not_prime_prime_dirac; auto; apply SO_power; auto.
auto with arith.
intros x H7 H8.
case (Nat.le_gt_cases x (2 * n)); intros Hp1.
case (Nat.le_gt_cases x n); intros Hp2.
replace x with (power x (1 + power_div (binomial (2 * n) n) x)).
apply power_div_not_divides; auto with arith.
generalize H8; case x; auto with arith.
intros Ht; Contradict Ht; auto with arith.
intros x1; case x1; auto with arith.
intros Ht; Contradict Ht; auto with arith.
rewrite power_div_binomial3; auto with arith.
simpl in |- *; ring.
apply Nat.lt_le_trans with (2 := H); simpl in |- *; auto with arith.
apply Nat.lt_le_trans with (3 * (1 + div (2 * n) 3)); auto with arith.
apply div_lt; auto with arith.
case (proj1 (Nat.lt_eq_cases _ _) Hp1); intros Hp3; auto with arith.
contradict H8; auto with arith.
contradict H8; auto with arith.
rewrite Hp3.
red in |- *; intros (H9, H10).
absurd (2 * n = 2).
red in |- *; intros H11; contradict H.
apply Nat.lt_nge.
apply lt_mult_right_anti with (z := 2); rewrite H11; simpl in |- *;
 auto with arith.
apply H10; auto with arith.
exists n; auto with arith.
red in |- *; intros H9;
 absurd
  (divides (power x (power_div (binomial (2 * n) n) x)) (binomial (2 * n) n)).
red in |- *; intros H10;
 absurd (power x (power_div (binomial (2 * n) n) x) <= 2 * n).
apply Nat.lt_nge; apply Nat.lt_le_trans with (1 := Hp1).
generalize (power_div_not_divides (binomial (2 * n) n) x).
case (power_div (binomial (2 * n) n) x); auto with arith.
intros H11; case H11; auto with arith.
generalize H8; case x; auto with arith.
intros Ht; Contradict Ht; auto with arith.
intros x1; case x1; auto with arith.
intros Ht; Contradict Ht; auto with arith.
rewrite <- plus_n_O; rewrite power_SO; auto.
intros n0 H11; pattern x at 1 in |- *; rewrite <- power_SO; auto with arith.
apply power_le_mono; auto with arith.
apply Nat.lt_trans with (2 := H7); auto with arith.
apply Nat.le_lt_trans with (2 := Hd); auto with arith.
apply power_div_binomial1; auto with arith.
apply power_div_divides; auto with arith.
apply Nat.lt_trans with (2 := H7); auto with arith.
apply Nat.le_lt_trans with (2 := Hd); auto with arith.
change (sqr 1 <= sqr (2 * n)) in |- *.
apply sqr_mono.
apply Nat.le_trans with (2 * power 2 7); auto with arith; simpl in |- *;
 auto with arith.
apply mult_id_lt_inv.
apply Nat.le_lt_trans with (2 * n).
apply sqr_le.
apply Nat.lt_le_trans with (3 * (1 + div (2 * n) 3)); auto with arith.
apply div_lt.
auto with arith.
cut (4 <= div (2 * n) 3); [ intros H1 | idtac ].
apply Nat.le_trans with (4 * div (2 * n) 3); auto with arith.
replace 4 with (1 + 3); auto with arith.
rewrite Nat.mul_add_distr_l; rewrite Nat.mul_add_distr_r.
apply Nat.add_le_mono; auto with arith.
apply Nat.le_trans with 4; auto with arith.
rewrite Nat.mul_1_l; auto.
apply le_mult; auto with arith.
apply Nat.lt_succ_r.
apply lt_mult_right_anti with (z := 3).
apply Nat.le_lt_trans with (2 * n); auto with arith.
apply Nat.le_trans with (2 * power 2 7); auto with arith.
apply Nat.le_trans with (2 * power 2 3).
simpl in |- *; auto with arith.
apply le_mult; auto with arith.
apply power_le_mono; auto with arith.
apply (div_lt (2 * n) 3); auto with arith.
Qed.
```

### child `binomial_even`: [`theories/Binomial.v` lines 255-324](https://github.com/rocq-community/bertrand/blob/033b1a8f1a9c121855b6b78cd55154d3c09e1c23/theories/Binomial.v#L255-L324) ([local copy](code/theories/Binomial.v))

```coq
Theorem binomial_even :
 forall n : nat, 0 < n -> power 2 (2 * n) <= 2 * n * binomial (2 * n) n.
Proof.
intros n Hn.
cut (S (2 * n - 2) = 2 * n - 1);
 [ intros H1
 | generalize Hn; case n; simpl in |- *; auto;
    try (intros H1; inversion H1; fail);
    (intros n1; repeat rewrite <- plus_n_Sm; simpl in |- *;
      rewrite Nat.sub_0_r) ]; auto.
cut (2 * n - 2 < 2 * n - 1); [ intros H2 | rewrite <- H1; auto with arith ].
cut (S (2 * n - 1) = 2 * n);
 [ intros H3
 | generalize Hn; case n; simpl in |- *; auto;
    try (intros H3; inversion H3; fail); intros n1;
    repeat rewrite <- plus_n_Sm; simpl in |- * ]; auto.
rewrite binomial2.
rewrite sum_nm_split with (r := 0); auto with arith.
repeat rewrite <- plus_n_O.
rewrite sum_nm_split with (p := 1) (r := 2 * n - 2); auto with arith.
replace (1 + (1 + (2 * n - 2))) with (2 * n);
 [ idtac | generalize H1 H3; simpl in |- *; intros H4; rewrite H4; auto ].
replace (2 * n - 1 - (1 + (2 * n - 2))) with 0;
 [ idtac | rewrite <- H1, Nat.sub_diag; auto ].
apply Nat.le_trans with (1 + (S (2 * n - 2) * binomial (2 * n) n + 1)).
repeat apply Nat.add_le_mono; auto with arith.
case n; simpl in |- *; auto.
rewrite <- sum_nm_c with (c := binomial (2 * n) n) (p := 1).
apply sum_nm_le.
intros x Hx H4.
assert (Hx2n : x <= 2 * n).
apply Nat.le_trans with (1 := H4).
pattern (2 * n) at 2; rewrite <- H3; rewrite <- H1; auto with arith.
generalize (Nat.lt_succ_pred _ _ Hn); intros H5; rewrite <- H5 at 3.
case (Nat.le_gt_cases x n); intros H6.
replace x with (S (pred n) - (S (pred n) - x)).
apply binomial_mono.
rewrite <- H5; auto with arith.
rewrite H5; auto with arith.
apply Nat.add_sub_eq_l.
apply Nat.sub_add; auto.
rewrite <- (Nat.sub_add x (2 * n)) at 1; auto with arith.
rewrite Nat.add_comm.
rewrite binomial_comp with (n := x).
rewrite Nat.add_comm, Nat.sub_add; auto with arith.
replace (2 * n - x) with (S (pred n) - (x - n)).
apply binomial_mono.
rewrite <- H5; auto with arith.
rewrite H5; auto with arith.
replace x with (n + (x - n)) at 2; auto with arith.
rewrite Nat.sub_add_distr.
replace (2 * n) with (n + n) by ring.
rewrite Nat.add_sub; auto.
simpl in |- *; rewrite binomial_def3; auto with arith.
replace (1 + (S (2 * n - 2) * binomial (2 * n) n + 1)) with
 (2 + S (2 * n - 2) * binomial (2 * n) n); [ idtac | ring ].
rewrite H1.
replace (2 * n * binomial (2 * n) n) with
 (binomial (2 * n) n + (2 * n - 1) * binomial (2 * n) n).
apply Nat.add_le_mono; auto with arith.
generalize Hn; elim n; auto with arith.
intros n1; case n1; auto with arith.
intros n0 H Hn0; replace (2 * S (S n0)) with (S (S (2 * S n0)));
 auto with arith.
2: simpl in |- *; repeat rewrite <- plus_n_Sm; auto.
repeat rewrite binomial_def4; auto with arith.
refine (Nat.le_trans  _ _ _ _ (Nat.le_add_r _ _)); 
  rewrite Nat.add_comm; auto with arith.
pattern (2 * n) at 4 in |- *; rewrite <- H3; auto.
Qed.
```

How the parts fit. The parent `no_prime_imp_spec_inegality` proves a `<`
inequality from the two hypotheses `power 2 7 <= n` and "no prime between n and
2n". Its proof is a single chain through one intermediate, `2 * n * binomial
(2*n) n`:

- the **lower link** is `Nat.le_lt_trans` with `2 * n * binomial (2*n) n`
  (line 194): the left side `power 4 n` is rewritten to `power 2 (2*n)` via
  `replace 4 with (power 2 2)` and `power_power`, and `binomial_even` supplies
  `power 2 (2*n) <= 2*n * binomial (2*n) n`;
- the **upper link** is `Nat.lt_le_trans` (line 197): after massaging the right
  side with `Nat.sub_add` / `power_mult` / `power_SO` / `Nat.mul_assoc` and
  `mult_lt_bis`, `upper_bound` supplies
  `binomial (2*n) n < power (2*n) (div (sqr (2*n)) 2 - 1) * power 4 (div (2*n) 3)`,
  and the remainder of the proof (lines 207-219) closes the side condition that
  `2*n` exceeds `power 2 7`.

The lemma graph is a spine with two leaves:

```
no_prime_imp_spec_inegality
  uses binomial_even   (lower bound of binomial (2*n) n)
   and upper_bound     (upper bound of binomial (2*n) n)
```

Each leaf is a good leaf because its statement is self-contained — a bound on
`binomial (2*n) n` under the same hypotheses — and its proof closes on its own
from named sibling lemmas, not from the parent's context:

- `upper_bound` is itself a calc-chain of the same shape: it factors
  `binomial (2*n) n` with `factorization` (line 41), splits the product with
  `prod_nm_split`, chains `Nat.lt_le_trans`/`Nat.le_lt_trans` through
  `prod_nm 0 (div (2*n) 3) ...`, and closes each prime-power link with
  `power_div_binomial1/2/3`, `prod_prime_lt` and `prod_prime_le`;
- `binomial_even` rewrites the sum form of the binomial (`binomial2`, line 271),
  splits it with `sum_nm_split`, and reduces the comparison to the monotonicity
  lemmas `binomial_mono`/`binomial_comp`/`binomial_def3`/`binomial_def4`,
  closing with `Nat.le_trans`, `Nat.add_le_mono` and `auto with arith`.

Nothing in the parent proof depends on how either child is proved — only on the
two statements. (The glue also uses small arithmetic helper lemmas —
`power_power`, `power_mult`, `power_SO`, `power_le_mono`, `mult_lt_bis`,
`mult_id_lt_inv`, `lt_mult_right_anti`, `le_mult`, `sqr_lt`, `div_lt` — but
these are generic library-style lemmas, not the two lemmas that carry the
argument.)

## Why it is good

1. The parent `no_prime_imp_spec_inegality` is declared in `theories/Bertrand.v`,
   lines 187-220 (`check`, permalink).
2. The parent's proof cites the child `upper_bound` (`check`, permalink).
3. The parent's proof cites the child `binomial_even` (`check`, permalink).
4. The decomposition is shallow: 2 direct lemmas (`upper_bound`,
   `binomial_even`), the longest project-lemma chain below the parent is 2
   (`no_prime_imp_spec_inegality` → `upper_bound` → `factorization`; and
   `no_prime_imp_spec_inegality` → `binomial_even` → `binomial2`), the glue is
   34 lines, and the two children have 158 and 70 proof lines respectively
   (`measurement`, site ranges).
5. The authors label the two children as the lower and upper bound of the
   central binomial: "Lower bound for (binomial 2n n)" (Binomial.v line 253) and
   "Upper Bound for (binonial 2n n)" (Bertrand.v line 25, typo in the source),
   so the chain through `binomial (2*n) n` is the split they had in mind
   (`author-statement`, permalinks).

In my opinion the detail worth copying is that the two children are *bounds on
the same intermediate*, not on the goal directly: the parent never unfolds
`binomial (2*n) n`, it only needs a lower bound below and an upper bound above,
so a reader can replace either bound without touching the other.

## When to use it, and when not

Use it when a target inequality factors through a natural intermediate (here the
central binomial `binomial (2*n) n`) whose lower and upper bounds are each
already proved as their own named lemma, so the parent proof is two transitivity
steps (`Nat.le_lt_trans`, `Nat.lt_le_trans`) and the rest is bookkeeping. This is
the standard "sandwich" or squeeze shape: prove `A <= M` and `M < C`, conclude
`A < C`.

Avoid it when one side is a one-off rewrite with no reuse — the value here is
that `binomial_even` and `upper_bound` are reusable bound lemmas, not that
`power 4 n <= 2*n*binomial(2n n)` is hard. Avoid it when a single library lemma
(`lia`, `auto with arith`, a monotonicity lemma) closes the whole goal, or when
the two links are stated over different intermediates so the transitivity does
not line up.

## Consequences

The move creates one obligation per link: each of the two bound lemmas must be
proved before `Nat.le_lt_trans`/`Nat.lt_le_trans` compose them. Transitivity is
automatic, but the two links must line up on the same intermediate
`2 * n * binomial (2*n) n`; a lower-bound and upper-bound lemma stated over
different intermediates will not typecheck. Failure modes: a child stated too
weak (say the wrong exponent in `binomial_even`) breaks the final result without
a hint in the glue, and the glue's arithmetic bookkeeping (`replace 4 with
(power 2 2)`, the `Nat.sub_add`/`power_mult` massaging of the right-hand side) is
easy to get wrong — in this proof most of the 34 lines are that bookkeeping, not
the two lemma applications.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml runs docker-coq-action with opam_file coq-bertrand.opam on push to master (default branch); opam build runs make over _CoqProject, whose first line is theories/Bertrand.v, so CI builds theories/Bertrand.v | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: upper_bound@theories/Bertrand.v:206, binomial_even@theories/Bertrand.v:196; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 6 file(s) byte-identical at 033b1a8f1a9c121855b6b78cd55154d3c09e1c23 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(no_prime_imp_spec_inegality, theories/Bertrand.v, 187-220) -> declared: no_prime_imp_spec_inegality is declared at theories/Bertrand.v:187 | check_claims.py |
| 2 | verified | cites(parent, upper_bound) -> cites: upper_bound occurs at theories/Bertrand.v:206 | check_claims.py |
| 3 | verified | cites(parent, binomial_even) -> cites: binomial_even occurs at theories/Bertrand.v:196 | check_claims.py |
| 4 | verified | 2 direct lemmas: upper_bound cited at Bertrand.v:206, binomial_even at :196 (check_claims); glue 187-220 = 34 lines; child lines 27-184 = 158, 255-324 = 70; depth 2: upper_bound uses factorization at Bertrand.v:41 and factorization is declared at PrimeDirac.v:449; binomial_even uses binomial2 at Binomial.v:271 and binomial2 is declared at Binomial.v:205 | verifier |
| 5 | verified | Bertrand.v:25 reads '(** Upper Bound for (binonial 2n n) *)' (verbatim, incl. the 'binonial' typo); Binomial.v:253 reads '(** Lower bound for (binomial 2n n) *)' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Opened local copies. Parent no_prime_imp_spec_inegality is declared at Bertrand.v:187-220 and its statement matches entry.json verbatim; it cites binomial_even at :196 and upper_bound at :206, exactly the two children. Child upper_bound declared Bertrand.v:27-184 (statement matches), closes with Qed at :184 (no admit/sorry); child binomial_even declared Binomial.v:255-324 (statement matches), closes Qed at :324. Shape numbers are right: glue_lines 34 = 187-220; child_lines [158,70] = 27-184 and 255-324; direct_lemmas 2; depth 2 matches the two chains parent->upper_bound->factorization (factorization cited Bertrand.v:41) and parent->binomial_even->binomial2 (binomial2 cited Binomial.v:271, declared Binomial.v:205). The parent also uses generic helper lemmas (power_power/power_mult/mult_lt_bis/etc.) which the README honestly flags as non-children; the two bound lemmas are the lemmas written for this argument, so the decomposition is what the entry says. | reviewer-correctness |
| generality | accept | Move is stated generically (sandwich/squeeze: A<=M and M<C conclude A<C via Nat.le_lt_trans/Nat.lt_le_trans) in goal_shape/use_when/also_known_as, so it applies beyond Bertrand. 'When not to use' is specific and honest (one-off rewrite with no reuse; single library lemma closes it; links over different intermediates won't line up). Consequences are specific (one obligation per link, transitivity automatic but intermediates must match, child-too-weak failure mode, most of the 34 glue lines are arithmetic bookkeeping). Good-leaf criterion is answered: self-contained statement + proof closes from named sibling lemmas, not the parent context (verified the child comments at Bertrand.v:25 and Binomial.v:253 and parent site 187-220). Minor imprecisions, not material: binomial_even is stated under the weaker hypothesis 0<n (not 'the same hypotheses'), and both children are cited exactly once so 'reusable bound lemmas' is a slight overstatement of actual reuse; the entry's own 'replace either bound without touching the other' is the more accurate reason. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. check_provenance passes: 6 copied files (Bertrand.v, Binomial.v, Power.v, Div.v, Misc.v, Prime.v) byte-identical at commit 033b1a8f1a9c121855b6b78cd55154d3c09e1c23. Commit is identical across README (abbreviated 033b1a8f1a9c), entry.json source.commit, sources/bertrand/source.json and SOURCE.md. Licence LGPL-2.1 is recorded identically in entry.json, README, source.json, SOURCE.md, and the copied upstream-LICENSE file is LGPL-2.1. All permalinks use the pinned commit and the cited line ranges match the copied files (Bertrand.v:187 'Theorem no_prime_imp_spec_inegality', :196 cites binomial_even, :206 cites upper_bound, :220 Qed, :25 'Upper Bound for (binonial 2n n)'; Binomial.v:253 'Lower bound for (binomial 2n n)', :255 'Theorem binomial_even', :324 Qed). File byte sizes in entry.json match the local copies. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-community/bertrand at commit `033b1a8f1a9c121855b6b78cd55154d3c09e1c23`, under `LGPL-2.1-or-later`; see the [source note](../../sources/bertrand/SOURCE.md) for the licence text and attribution.
