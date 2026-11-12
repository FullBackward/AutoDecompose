# One semax_body lemma per malloc function, assembled by mkVSU into MF_R_VSU

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | rocq |
| Status | draft |
| Source | [vst](../../sources/vst/SOURCE.md) at `c082fe210ec5` |
| Licence | `BSD-2-Clause` |

## Intent

Reduce the correctness proof of the malloc/free Verified Software Unit (VSU)
to one self-contained `semax_body` lemma per function of `malloc.prog` plus one
initializer lemma. `mkVSU` generates an obligation per function, and each is
discharged by exactly one named body lemma (`body_X`), so the glue is one line
per callee.

## The decomposition

### parent `MF_R_VSU`: [`progs/memmgr/VSU_malloc.v` lines 40-59](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/VSU_malloc.v#L40-L59) ([local copy](code/progs/memmgr/VSU_malloc.v))

```coq
  Definition MF_R_VSU: @VSU NullExtension.Espec 
      nil MF_Imports ltac:(QPprog malloc.prog)
      (Malloc_R_ASI R_APD malloc._pre_fill malloc._try_pre_fill malloc._malloc malloc._free)
      (mem_mgr_R emptyResvec).
  Proof.
    mkVSU malloc.prog MF_internal_specs.
  + solve_SF_internal body_malloc_large.
  + solve_SF_internal body_malloc_small.
  + solve_SF_internal body_free_large.
  + solve_SF_internal body_free_small.
  + solve_SF_internal body_bin2size.
  + solve_SF_internal body_size2bin.
  + solve_SF_internal body_list_from_block.
  + solve_SF_internal body_fill_bin.
  + solve_SF_internal body_pre_fill.
  + solve_SF_internal body_try_pre_fill.
  + solve_SF_internal body_malloc.
  + solve_SF_internal body_free.
  + apply create_memmgr_R.
  Qed.
```

### child `create_memmgr_R`: [`progs/memmgr/VSU_malloc.v` lines 20-23](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/VSU_malloc.v#L20-L23) ([local copy](code/progs/memmgr/VSU_malloc.v))

```coq
  Lemma create_memmgr_R: VSU_initializer malloc.prog (mem_mgr_R emptyResvec).
  Proof. InitGPred_tac.
    eapply derives_trans. 2: apply create_mem_mgr_R. entailer!.
  Qed. 
```

### child `body_malloc_large`: [`progs/memmgr/verif_malloc_large.v` lines 10-92](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_malloc_large.v#L10-L92) ([local copy](code/progs/memmgr/verif_malloc_large.v))

```coq
Lemma body_malloc_large: semax_body MF_Vprog MF_Gprog f_malloc_large malloc_large_spec.
Proof.
start_function. 
forward_call (n+WA+WORD). (*! t'1 = mmap0(nbytes+WASTE+WORD ...) !*)
{ entailer!. }
(*{ rep_lia. }*)
Intros p.
(* NOTE could split cases here; then two symbolic executions but simpler ones *)
forward_if. (*! if (p==NULL) !*)
- (* typecheck guard *) 
  if_tac; entailer!.
- (* case p == NULL *) 
  forward. (*! return NULL  !*)
  Exists (Vint (Int.repr 0)).
  if_tac; entailer!. (* cases in post of mmap *)
- (* case p <> NULL *) 
  if_tac. (* cases in post of mmap *)
  + (* impossible case *)
    exfalso. destruct p; try contradiction; simpl in *.
  + assert_PROP (
        (force_val
           (sem_add_ptr_int tuint Signed
                            (force_val
                               (sem_cast_pointer
                                  (force_val
                                     (sem_add_ptr_int tschar Unsigned p
                                                      (Vint
                                                         (Int.sub
                                                            (Int.mul (Ptrofs.to_int (Ptrofs.repr 4)) (Int.repr 2))
                                                            (Ptrofs.to_int (Ptrofs.repr 4))))))))
                            (Vint (Int.repr 0))) = field_address tuint [] (offset_val WA p)) ).
    (* painful pointer reasoning to enable forward (p+WASTE)[0] = nbytes *)
    { entailer!. 
      destruct p; try contradiction; simpl.
      normalize.
      unfold field_address.
      rewrite if_true.
      { simpl.  normalize. }
      hnf. (* drill down *) 
      repeat split; auto.
      - (* size compat *)
        red. 
        match goal with | H:size_compatible' _ _ |- _ => red in H end.
        unfold Ptrofs.add.
        rewrite (Ptrofs.unsigned_repr WA) by rep_lia.
        rewrite Ptrofs.unsigned_repr by rep_lia.
        simpl sizeof. rep_lia.
      - (* align compat *)
        red.
        eapply align_compatible_rec_by_value; try reflexivity.
        simpl in *. unfold natural_alignment in *. unfold Z.divide in *.
        match goal with | HA: (exists z:Z, _) /\ _ |- _ => destruct HA as [Hz Hlim] end. 
        inv Hz.
        rewrite <- (Ptrofs.repr_unsigned i). 
        match goal with | HA: Ptrofs.unsigned _ = _ |- _ => rewrite HA end. 
        exists (2*x+1). change WA with 4.
        rewrite ptrofs_add_repr. rewrite Ptrofs.unsigned_repr.
        lia. rep_lia.
    }
    rewrite malloc_large_chunk; try rep_lia; try assumption.
    Intros. (* flatten sep *)
    forward. (*! (p+WASTE)[0] = nbytes;  !*)
    forward. (*! return (p+WASTE+WORD);  !*)
    (* postcond *)
    Exists (offset_val (WA+WORD) p).
    entailer!.
    simpl.
    if_tac. 
    { exfalso. destruct p; try contradiction; simpl in *. 
      match goal with | HA: Vptr _ _  = nullval |- _ => inv HA end. }
    unfold malloc_token'.
    Exists n.
    unfold malloc_tok.
    if_tac. rep_lia. entailer!. 
    { apply malloc_compatible_offset; try rep_lia; try apply WORD_ALIGN_aligned.
      replace (n+(WA+WORD)) with (n + WA + WORD) by lia. assumption. }
    cancel. 
    (* split off the token's share of chunk *)
    rewrite <- memory_block_Ews_join.
    (* data_at_ from memory_block *)
    replace (n - n) with 0 by lia.
    rewrite memory_block_zero.  entailer!.
Qed.
```

### child `body_malloc`: [`progs/memmgr/verif_malloc_free.v` lines 8-39](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_malloc_free.v#L8-L39) ([local copy](code/progs/memmgr/verif_malloc_free.v))

```coq
Lemma body_malloc i: semax_body MF_Vprog MF_Gprog f_malloc (malloc_spec_R' R_APD i).
Proof. 
start_function. 
forward_call (BINS-1). (*! t'3 = bin2size(BINS-1) !*)
try rep_lia. 
forward_if. (*! if nbytes > t'3 !*)
- (* case nbytes > bin2size(BINS-1) *)
  forward_call (n, gv, rvec).  (*! t'1 = malloc_large(nbytes) !*)
  { simpl. cancel. }
  (*{ (* precond *) destruct H. split; try assumption. } *)
  Intros p.
  forward. (*! return t'1 !*) 
  Exists p.
  assert (guaranteed rvec n = false) by (apply large_not_guaranteed; auto).
  destruct (guaranteed rvec n); [ discriminate |].
  destruct (eq_dec p nullval); entailer!. simpl; cancel.
  bdestruct (n <=? maxSmallChunk); try rep_lia.
  simpl; cancel.
- (* case nbytes <= bin2size(BINS-1) *)
  forward_call(n, gv, rvec).  (*! t'2 = malloc_small(nbytes) !*)
  { simpl; cancel. }
  (*{ (* precond *)  destruct H. split; try rep_lia. }*)
  Intros p.
  forward. (*! result = t'2 !*)
  Exists p. 
  destruct (eq_dec p nullval); entailer.
  simple_if_tac.  
  + simpl; entailer!.
  + bdestruct (n <=? maxSmallChunk); try rep_lia.
    Intros rvec'. Exists rvec'.
    simpl; entailer!.
Qed.
```

### child `body_bin2size`: [`progs/memmgr/verif_bin2size2bin.v` lines 7-9](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_bin2size2bin.v#L7-L9) ([local copy](code/progs/memmgr/verif_bin2size2bin.v))

```coq
Lemma body_bin2size: semax_body MF_Vprog MF_Gprog f_bin2size bin2size_spec.
Proof. start_function. forward. 
Qed.
```

### child `body_size2bin`: [`progs/memmgr/verif_bin2size2bin.v` lines 11-23](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_bin2size2bin.v#L11-L23) ([local copy](code/progs/memmgr/verif_bin2size2bin.v))

```coq
Lemma body_size2bin: semax_body MF_Vprog MF_Gprog f_size2bin size2bin_spec.
Proof. start_function. 
  forward_call (BINS-1). (*rep_lia. *)
  forward_if.
  - (* then *) 
    forward. entailer!. f_equal. f_equal. unfold size2binZ; simpl. 
    bdestruct (bin2sizeZ (BINS - 1) <? s); trivial; try lia.
  - (* else *)
    forward.  entailer!. f_equal. unfold size2binZ. 
    bdestruct (bin2sizeZ (BINS - 1) <? s); try lia.
    unfold Int.divu. do 2 rewrite Int.unsigned_repr by rep_lia. 
    f_equal. normalize.  f_equal. rep_lia.
Qed.
```

### child `body_free_large`: [`progs/memmgr/verif_free_large.v` lines 11-23](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_free_large.v#L11-L23) ([local copy](code/progs/memmgr/verif_free_large.v))

```coq
Lemma body_free_large: semax_body MF_Vprog MF_Gprog f_free_large free_large_spec.
Proof. 
start_function. 
forward_call( (offset_val (-(WA+WORD)) p), (s+WA+WORD) ). (*! munmap( p-(WASTE+WORD), s+WASTE+WORD ) !*)
+ entailer!. destruct p; try contradiction; simpl. normalize.
  rewrite Ptrofs.sub_add_opp. reflexivity.
+ (* munmap pre *)
  entailer!. 
  sep_apply (free_large_chunk s p); try rep_lia.
  entailer!.
(* + rep_lia.*)
+ entailer!.   
Qed.
```

### child `body_fill_bin`: [`progs/memmgr/verif_fill_bin.v` lines 11-59](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_fill_bin.v#L11-L59) ([local copy](code/progs/memmgr/verif_fill_bin.v))

```coq
Lemma body_fill_bin: semax_body MF_Vprog MF_Gprog f_fill_bin fill_bin_spec.
Proof. 
start_function. 
forward_call b.  (*! s = bin2size(b) !*)
set (s:=bin2sizeZ b).
assert (WORD <= s <= bin2sizeZ(BINS-1)) by (pose proof (bin2size_range b); rep_lia).
forward_call BIGBLOCK.  (*! *p = mmap0(BIGBLOCK ...) !*)  
(*{ rep_lia. }*)
Intros p.  
if_tac in H1. (* split cases on mmap post *)
- (* case p = nullval *)
  forward_if. (*! if p == NULL, case true  !*)
  forward. (*! return NULL !*)
  Exists nullval. Exists 1. 
  entailer!. contradiction.
- (* case p <> nullval *)
  assert_PROP (isptr p) by entailer!.
  destruct p; try contradiction. 
  rename b0 into pblk; rename i into poff. (* p as blk+ofs *)
  assert_PROP (Ptrofs.unsigned poff + BIGBLOCK < Ptrofs.modulus) by entailer!.
  forward_if; try contradiction. (*! if p == NULL, case false *)
  forward_call((s,(Vptr pblk poff),nullval,0%nat,b)).  (*! t3 = list_from_block(s,p,null) *)
  { unfold mmlist. entailer!. }
  Intro q.
  forward. (*! return t3 *) 
  Exists q. Exists (chunks_from_block (size2binZ s)).
  if_tac.
  { (* q = null - contradiction *)
    pose proof (chunks_from_block_pos b H).
    assert (q<>nullval).
    { apply (proj1 H7) in H8.
      rewrite Nat.add_0_r in H8.
      rewrite <- Z2Nat.inj_0 in H8.
      apply Z2Nat.inj in H8; try rep_lia.
      subst s.
      rewrite bin2size2bin_id in *; try rep_lia.
      apply chunks_from_block_nonneg.
    }
    contradiction.
  }
  entailer!.
  assert (Hbs: 0 <= s <= bin2sizeZ(BINS-1)) by rep_lia.
  pose proof (size2bin_range s Hbs) as Hs.
  pose proof (chunks_from_block_pos (size2binZ s) Hs).
  rep_lia.
  rewrite Nat.add_0_r. (* ugh *)
  subst s.
  cancel.
Qed.
```

How the parts fit. The parent `MF_R_VSU` is a single
`mkVSU malloc.prog MF_internal_specs` invocation whose obligations are discharged
one line each: twelve `solve_SF_internal body_X` for the twelve internal
functions, then `apply create_memmgr_R` for the initializer. `MF_internal_specs`
([`VSU_malloc_definitions.v` lines 130-133](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/VSU_malloc_definitions.v#L130-L133))
is the eight private funspecs plus `Malloc_R_ASI R_APD _pre_fill _try_pre_fill
_malloc _free`, so the twelve body lemmas correspond one-to-one with the
internal functions:

- `body_bin2size`, `body_size2bin` — the two leaf arithmetic helpers;
- `body_list_from_block`, `body_fill_bin` — build a free list from one mmap'd block;
- `body_malloc_large`, `body_malloc_small`, `body_free_large`, `body_free_small` — the four size-path bodies;
- `body_malloc`, `body_free` — the public API dispatchers, which call the large/small bodies through `forward_call`;
- `body_pre_fill`, `body_try_pre_fill` — the pre-filling bodies.

Every body lemma states `semax_body MF_Vprog MF_Gprog f_X X_spec`: one function
`f_X`, one funspec `X_spec`, so each is a self-contained leaf that closes on its
own (or on the specs of the functions it calls). `body_bin2size` is the
degenerate case — `start_function. forward.` closes it because the C function is
a single statement already matching its spec. `body_malloc` is the
representative dispatcher: it `forward_call`s `malloc_large`/`malloc_small` and
closes each branch with `entailer!`, so its proof depends on those bodies only
through their funspecs. `create_memmgr_R` is the one child that is not a
function body; it closes the initializer obligation with `apply create_mem_mgr_R`
([`malloc_sep.v` line 830](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/malloc_sep.v#L830)).

The six body lemmas not shown as sites above (each copied whole under `code/`):

- `body_malloc_small` — [`verif_malloc_small.v` lines 11-359](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_malloc_small.v#L11-L359)
- `body_free_small` — [`verif_free_small.v` lines 11-137](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_free_small.v#L11-L137)
- `body_list_from_block` — [`verif_list_from_block.v` lines 97-450](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_list_from_block.v#L97-L450)
- `body_pre_fill` — [`verif_pre_fill.v` lines 12-103](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_pre_fill.v#L12-L103)
- `body_try_pre_fill` — [`verif_try_pre_fill.v` lines 44-152](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_try_pre_fill.v#L44-L152)
- `body_free` — [`verif_malloc_free.v` lines 41-96](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_malloc_free.v#L41-L96)

Why each child is a good leaf. Each `body_X` states exactly what one function
must do against one funspec and closes by symbolic execution
(`start_function`/`forward_call`/`forward_if`) plus `entailer!`, appealing to
shared separation-logic lemmas (`mem_mgr_split_R`, `malloc_large_chunk`,
`free_large_chunk`, `mmlist_*`) in `malloc_sep.v` and `malloc_lemmas.v`. Because
the statement is per-function, the leaves are independent: the only place a body
lemma reaches a named sub-lemma is the reference chain `body_list_from_block` →
`list_from_inv_remainder` → `list_from_inv_remainder'`
([`verif_list_from_block.v` lines 291, 82](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_list_from_block.v#L291)),
and those sub-lemmas are arithmetic facts closed by `lia`.

## Why it is good

1. (*check*) The parent `MF_R_VSU` is closed by one `mkVSU malloc.prog
   MF_internal_specs` invocation plus thirteen one-line discharges — twelve
   `solve_SF_internal body_X` and one `apply create_memmgr_R` — across
   `VSU_malloc.v` lines 45-58, with nothing else between `Proof.` and `Qed.`.
   ([permalink](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/VSU_malloc.v#L44-L59))
2. (*check*) No `admit`, `Admitted`, `sorry`, `Axiom` or `Parameter` appears in
   `VSU_malloc.v` or any of the ten `verif_*.v` files, so every function's body
   is closed by a real proof (protocol §4 E3). The grep
   `\b(admit|Admitted|sorry|Axiom|Parameter)\b` over those files returns nothing.
3. (*measurement*) `direct_lemmas = 13` (twelve body lemmas plus
   `create_memmgr_R`), `glue_lines = 16`, `depth = 3` along the chain
   `MF_R_VSU` → `body_list_from_block` → `list_from_inv_remainder` →
   `list_from_inv_remainder'`, and `child_lines = [4, 83, 32, 3, 13, 13, 49]`.
   ([depth chain](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/verif_list_from_block.v#L291))
4. (*measurement*) All twelve body lemmas share one per-callee signature —
   `Lemma body_X : semax_body MF_Vprog MF_Gprog f_X X_spec` — so the glue
   `solve_SF_internal body_X` needs no argument beyond the lemma name.
5. (*known-use*) The same `mkVSU` + `solve_SF_internal` pattern discharges the
   sibling unit `MM0_VSU` one function at a time
   ([`VSU_mmap0.v` lines 46-60](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/progs/memmgr/VSU_mmap0.v#L44-L60)),
   where `body_mmap0`/`body_munmap` are left as `Parameter` rather than proved.

In my opinion the detail worth copying is the split of *what to verify* (one
per-callee `semax_body` lemma) from *how each is verified* (symbolic execution
plus `entailer!`), which keeps the glue at one line per function no matter how
hard any single body is.

## When to use it, and when not

Use it when the goal is a whole-program correctness statement over a fixed set
of functions each carrying its own funspec, and each function body can be
verified in isolation as a self-contained `semax_body` lemma. It is exactly the
shape a bounded per-leaf prover wants: many independent leaves, one line of glue
per leaf. The shared invariant (here `mem_mgr_R`) is threaded through every
funspec so no body needs a global argument.

Avoid it when a function's correctness depends on a whole-program invariant that
cannot be stated per-function, when the bodies are too interdependent to verify
in isolation, or when a body cannot be closed at all — the project's own
`VSU_mmap0.v` defers `body_mmap0`/`body_munmap` as `Parameter` rather than
proving them, so the move buys nothing there until those bodies exist.

## Consequences

`mkVSU` creates one obligation per function of `malloc.prog` — twelve
`semax_body` goals plus one `VSU_initializer` goal — and each must be closed by
a named body lemma, so a single unproved body fails the whole VSU. The API
functions `malloc`/`free`/`pre_fill`/`try_pre_fill` carry an index `i`, letting
one body lemma prove the whole spec family for every `i`. Failure modes: an
uncloseable body has to be deferred (as `VSU_mmap0.v` defers
`body_mmap0`/`body_munmap`), and a spec that is too weak or too strong at one
function surfaces only as an entailment failure deep inside that one body's
proof, not at the glue.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/PrincetonUniversity/VST at commit `c082fe210ec501219abe52b9d0f25541d7c97e59`, under `BSD-2-Clause`; see the [source note](../../sources/vst/SOURCE.md) for the licence text and attribution.
