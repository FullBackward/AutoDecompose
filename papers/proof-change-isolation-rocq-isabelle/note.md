# How Rocq and Isabelle isolate a change in a proof (official documentation)

| Field | Value |
|---|---|
| Authors, organisation | The Rocq development team (Inria and contributors); Makarius Wenzel and contributors (Isabelle) |
| Date and version read | Rocq Prover 9.3.0 reference manual. Isabelle2026 manuals dated 24 October 2026 |
| Source | **R1** https://rocq-prover.org/doc/V9.3.0/refman/proofs/writing-proofs/proof-mode.html ; **R2** https://rocq-prover.org/doc/V9.3.0/refman/proofs/writing-proofs/equality.html ; **R3** https://rocq-prover.org/doc/V9.3.0/refman/practical-tools/coq-commands.html ; **R4** https://rocq-prover.org/doc/V9.3.0/refman/addendum/parallel-proof-processing.html ; **R5** https://rocq-prover.org/doc/V9.3.0/refman/practical-tools/utilities.html ; **I1** https://isabelle.in.tum.de/doc/system.pdf ; **I2** https://isabelle.in.tum.de/doc/implementation.pdf ; **I3** https://isabelle.in.tum.de/doc/isar-ref.pdf ; **I4** https://isabelle.in.tum.de/doc/jedit.pdf ; **I5** https://isabelle.in.tum.de/repos/isabelle/raw-file/Isabelle2026/etc/options ; **I6** https://isabelle.in.tum.de/website-Isabelle2026/dist/Isabelle2026/doc/NEWS.html |
| Licence of the source | Not stated on the pages read |
| Files in this folder | `source.pdf` (104 pages: R3, R4, R1, R2 printed with headless Edge; then the cited pages of I1, I2, I3, I4), `note.md` |
| What was read | R1: two sections. R2: one section. R3: "Command line options" (two entries) and "Compiled interfaces" in full. R4 in full. R5: two sections. I1: Sections 2 (start), 2.2, 2.3 in full; 4.4.8 and 4.4.9 in part. I2, I3, I4, I5, I6: searched; the cited passages read |
| Read on | 2026-11-21 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

No earlier survey in `docs/research/` covers this topic. Lean is in the note `lean-module-system`.

## 1. What the work is

This note reads official documentation only. The question comes from reason (i) of the scaling problem of Prove2Me. Does a change inside one proof force a new check of the files that depend on it? Rocq documents an interface file that leaves out the proofs. Isabelle documents parallel proof checking inside one prover process, and a build tool whose unit is the session. Neither manual gives a measurement of rebuild time.

## 2. How it works

**(a) Rocq.**

- `Qed` gives the proof term to the kernel and adds it "as an opaque constant" [P] (R1, "Entering and exiting proof mode").
- A theorem that ends with `Qed` is "permanently marked opaque". It is never unfolded and cannot become transparent [P] (R2, "Controlling reduction strategies and the conversion algorithm"). So no later file can depend on the content of such a proof (reader's inference).
- `Defined` makes the proof transparent, and type checking can use its content [P] (R1, same section). `Admitted` gives up the proof and declares the goal as an axiom [P] (R1, same section).
- A compiled interface is a `.vos` file. `rocq c -vos foo.v` writes `foo.vos`, which is like `foo.vo` "except that all opaque proofs are skipped" [P] (R3, "Compiled interfaces", Principle).
- `rocq c -vok foo.v` checks the whole file with its opaque proofs. It loads `.vos` files for `Require` and writes no `.vo` file [P] (R3, "Command line options").
- With `rocq makefile`, `foo.vos` and `foo.vok` depend on `foo.v` and on `bar.vos` when `foo.v` requires `bar.v`. "foo.vok does not depend on bar.vok" [P] (R3, "Compiled interfaces").
- `make vos` compiles all statements. `make -j vok` then checks all proofs in parallel [P] (R3, same section).
- The price: Rocq parses and type-checks all definitions twice [P] (R3, same section).
- Inside a section, a proof must start with `Proof using`. Without it, `-vos` processes the proof in full [P] (R3, "Need for Proof using").
- The manual gives four warnings [P] (R3, first warning). The mode is for development only. The user must still produce the standard `.vo` files. `-vos` collects fewer universe constraints. The feature is "still experimental".
- Standard mode: a file must be compiled to `.vo` before another file can require it, and `rocq dep` prints the dependencies for `make` [P] (R5, "Setup for working on your own projects"; "rocq dep"). A change in a proof of `bar.v` gives a new `bar.vo`, so `make` compiles each dependent file again. This is the reader's inference from the timestamp rule of `make`; the manual does not state it [U].
- The manual does not say whether a build tool skips `foo.vok` when a new `bar.vos` is equal to the old one [U].
- Only opaque proofs "can be processed asynchronously" [P] (R4, introduction). A proof that takes less than 0.03 seconds is not given to a worker process [P] (R4, last "Caveats").

**(b) Isabelle.**

- Proofs cannot influence statements. "Proof terms are irrelevant in the Pure logic"; "they cannot occur within propositions" [P] (I2, Section 2.3.1). The system "can never depend on them due to proof irrelevance" [P] (I3, Section 2.1).
- "Significant parts of theory and proof checking is parallelized by default" [P] (I2, Section 0.8.1). The stated speed-up for Isabelle2013 is at most 3.5 on 4 cores and 6.5 on 8 cores [P] (I2, Section 0.8.1).
- A forked proof is a proof that the prover checks as a separate task while it continues with the text after the proof (reader's wording). "Parallel terminal proofs ('by') are enabled by default", so the prover can "run ahead" on the specifications [P] (I6, "New in Isabelle2013", Prover IDE).
- Option `parallel_proofs` is the "level of parallel proof checking: 0, 1, 2", default 1. Option `parallel_subproofs_threshold`, default 0.01, is the "lower bound of timing estimate for forked nested proofs (seconds)" [P] (I5).
- A proof promise is "a placeholder for some proof" that can be "fulfilled eventually". A named theorem keeps a digest of the oracles and promises of its proof [P] (I2, Section 2.5).
- `sorry` is "a fake proof". In batch mode it needs the option `quick_and_dirty`. The result is "tainted by an oracle invocation", which `thm_oracles` shows [P] (I3, Section 6.4.2).
- Option `skip_proofs` is "skip over proofs (implicit 'sorry')" [P] (I5). Option `condition_proofs` "skips proof checking only" [P] (I1, Section 2.2).
- A session is "a collection of related theories". A heap image stores the state of a session, "similar to object-code" [P] (I1, Section 2).
- `isabelle build` "manages dependencies between sessions, related sources of theories and auxiliary files, and target heap images" [P] (I1, Section 2.3). Option `-j` sets the number of prover processes, and `threads` sets the worker threads in each [P] (I1, Sections 2.2, 2.3).
- The build tool updates a session image that is "absent or outdated wrt. its sources" [P] (I4, Section 1.2). Option `-S` selects only sessions "that have changed sources" [P] (I1, Section 2.3). Source files "are identified by content via SHA1 digests" [P] (I6, "New in Isabelle2011-1").
- Sections 2.2 and 2.3 of I1 name no unit of rebuild below the session [P] (read in full).
- Does a change inside one proof force a new check of dependent theories? The manuals do not answer in one sentence [U]. Reader's inference for batch mode: yes. The edit changes the digest of the theory file, the session is outdated, and the tool builds the session and its descendants again.
- For the Prover IDE the manual says only that purged theories "will be rechecked when opened or imported later" [P] (I4, Section 3.1.2). The reach of an edit to importing theories is not stated [U].
- The server command `use_theories` adds theory files to a running session, and "already used theories persist in the session until purged explicitly" [P] (I1, Section 4.4.8).

## 3. How it splits a proof

The documentation does not split proofs. Two commands make a sub-proof a separate unit. Rocq `abstract` "saves the subproof as an auxiliary lemma", which `Qed` inlines again [P] (R1, "Proving a subgoal as a separate lemma: abstract"). Isabelle forks nested proofs above the threshold [P] (I5).

## 4. What it says about scale

- Isabelle: speed-up 3.5 on 4 cores and 6.5 on 8 cores (2013) [P] (I2, Section 0.8.1); "max. speedup factor 5.0" on 8 cores (2009) [P] (I6, "New in Isabelle2009-1").
- Rocq: no figures given.
- Rebuild time after a proof edit: no figures given in either manual.

## 5. Evidence

The sources are manuals. They give no experiment, no baseline and no ablation.

## 6. Limits

- Only official documentation was read. Dune, the usual Rocq build tool, has its own manual, which was not read [U].
- Isabelle source code was not read. The session-level inference in Section 2 rests on the manuals only.

## 7. Relation to the two anchors

Both anchors use Lean only. The order of Turing Agent (statements first, then proofs in parallel) is the order of `make vos` and `make -j vok`. The angelic proof of MathEye has a direct form in both systems: `Admitted` in Rocq and `sorry` in Isabelle, each with a record of the assumption [P] (R1; I3, Section 6.4.2). MathEye cites the Rocq Team and the Isabelle/HOL book as general references [S] (Semantic Scholar reference list). Neither anchor discusses rebuild cost.

## 8. What this repository can use

- Rocq can host the Prove2Me layout without separate statement files (reader's inference). Keep one lemma in each file; the `.vos` file is the statement card. `make foo.required_vos` prepares a parent "even though it was never needed to compile the proofs" of its children [P] (R3, "Compiled interfaces").
- Isabelle has no documented interface file for one theory. A card layout needs one small session for each card, or a warm server session with `use_theories` (reader's inference).
- In both systems the final check must be a full build: `.vo` files in Rocq, and a build without `quick_and_dirty` in Isabelle.

## 9. Open points and things not read

- Does Isabelle/PIDE check importing theories again after an edit inside a proof? A test on a real session can answer this.
- Not read: the Dune manual; the Isabelle sources; I1 Section 2.1; most of I2, I3 and I4.

## Comparison of the three assistants

| Assistant | What hides a proof from dependents | What a dependent file reads | Proof-only edit: are dependents checked again? | Status and measurement |
|---|---|---|---|---|
| Lean 4 (module system) | Proofs are in the private scope [P] (Lean Reference 5.4, https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/) | The public `.olean` file [P] (Lean Reference 5.5) | No, for files with a `module` header [P] (Lean Reference 5.4) | Mathlib from 19 Nov 2025; one log: 1 file rebuilt in 1.2 s [P] (Zulip thread, see the note `lean-module-system`) |
| Rocq 9.3 | `Qed` seals the proof [P] (R2) | `.vo` in standard mode; `.vos` with `-vos` or `-vok` [P] (R3) | Standard mode: yes with `make` (reader's inference) [U]. With `.vos`: the proof checks are independent [P] (R3); the skip of an unchanged `.vos` is not documented [U] | "still experimental" [P] (R3); no measurement |
| Isabelle2026 | Proof irrelevance; forked proofs [P] (I2, Section 2.3.1; I6) | The heap image of the parent session [P] (I1, Section 2) | Batch: the session is built again (reader's inference) [U]. Prover IDE: not stated [U] | Parallel speed-up 6.5 on 8 cores [P] (I2, Section 0.8.1); no rebuild measurement |
