# DeepSeekCoTHandler plan-before-proving prompt: name intermediate lemmas and proof structure before the Lean proof

| | |
|---|---|
| Kind | skill |
| Move | workflow |
| Language | python |
| Status | draft |
| Source | [goedel-prover-v2](../../sources/goedel-prover-v2/SOURCE.md) at `2e9036e11846` |
| Licence | `LicenseRef-unknown` |

## Intent

Make the lemma skeleton a required planning step of every proof attempt: before
writing any Lean code, the prompt asks the DeepSeek-Prover-V2-7B chat model to
produce a proof plan naming key ideas, intermediate lemmas and proof
structures, then to complete the Lean code for a goal fixed as `:= by sorry`.

## The decomposition

### skill-text `plan-before-proving-prompt`: [`src/utils.py` lines 339-350](https://github.com/Goedel-LM/Goedel-Prover-V2/blob/2e9036e118464aa96a8bebaf9f5b9d091aa3585c/src/utils.py#L339-L350) ([local copy](code/src/utils.py))

````python
    def prover_inference(self, lean4_code, tokenizer):
        formal_statement = lean4_code.split(":= by")[0] + ":= by sorry" # include sorry https://huggingface.co/deepseek-ai/DeepSeek-Prover-V2-7B
        prompt = F"Complete the following Lean 4 code:\n\n```lean4\n{formal_statement}```\n\nBefore producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.\nThe plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof."
        messages = [
            {"role": "user", "content": prompt}
        ]
        text = tokenizer.apply_chat_template(
            messages,
            tokenize=False,
            add_generation_prompt=True
        )
        return text, messages
````

How the parts fit. The `DeepSeekCoTHandler` proving pipeline has four stages,
each the input of the next. First *sorrify-goal* (line 340) rewrites the input
theorem into a sorry-able skeleton by splitting on the `:= by` marker and
appending `:= by sorry`, so the statement is fixed and only the proof body is
open. Second, *plan-first-prompt* (line 341) wraps that skeleton in
"Complete the following Lean 4 code" and adds the instruction that, before
producing the code, the model must "provide a detailed proof plan …
highlight key ideas, intermediate lemmas, and proof structures". Third,
*extract-code* (`extrac_code`, lines 323-337) keeps only the last ```lean4
code block of the model's raw output and prepends the import header, so the
plan text is discarded. Fourth, *splice-proof* (`problem_check`, lines
352-354, which calls `replace_statement_in_proof`, lines 210-223) substitutes
that code block in place of the `sorry` in the original statement, closing the
goal and returning the final Lean. The plan's "intermediate lemmas" and "proof
structures" are never extracted, compared against the proof, or checked: they
exist only as a nudge to the model.

The same handler repeats the think-before-proving instruction in its
correction prompt (`generate_correction_prompt`, line 372), which asks for
"a detailed analysis of the error message" before the corrected attempt.

## Why it is good

1. The prompt instructs the model to plan before proving: "Before producing
   the Lean 4 code … provide a detailed proof plan … highlight key ideas,
   intermediate lemmas, and proof structures that will guide the construction
   of the final formal proof" (line 341). Evidence kind: check.
2. The goal is fixed as a sorry-able skeleton — line 340 splits on `:= by` and
   appends `:= by sorry`, and line 341 wraps it in "Complete the following
   Lean 4 code" — so the statement is fixed and only the proof body is open
   (lines 340-341). Evidence kind: check.
3. The plan is a soft instruction, not a checked artifact: `extrac_code`
   (lines 323-337) keeps only the last ```lean4 code block and
   `problem_check` (lines 352-354) splices that block into the statement via
   `replace_statement_in_proof`; no code in the copied file parses or
   validates the plan text (read of the whole copied file). Evidence kind:
   check.
4. The same think-before-proving instruction recurs in the correction-round
   prompt: "Before producing the Lean 4 code … provide a detailed analysis of
   the error message" (line 372). Evidence kind: known-use.
5. The authors explain the sorrify step in a comment: the `:= by sorry`
   rewrite exists to "include sorry" per the model card at
   huggingface.co/deepseek-ai/DeepSeek-Prover-V2-7B (line 340). Evidence kind:
   author-statement.

In my opinion the detail worth copying is the *ordering*: the plan instruction
is placed in the same message and *before* the request for code, so the model
is forced to name its intermediate lemmas before it may write a proof, and the
`sorry` skeleton makes the goal's statement fixed from the start. The weaker
side — worth noting rather than copying — is that the plan is never read back,
so the "lemma skeleton" is a prompt convention, not a structure the harness
verifies.

## When to use it, and when not

Use it when the prover is the DeepSeek chat model (whose model card expects
`sorry` in the goal) and you want the model to name its intermediate lemmas and
proof structure before it writes the proof, with the model's raw output then
parsed for a ```lean4 code block. Avoid it when the prover is a completion-only
(non-chat) model — `DeepSeekNonCoTHandler` (line 386) omits both the `sorry`
and the plan — or when you need the plan parsed, validated, or checked against
the proof (the harness only extracts the final code block and never reads the
plan); or when the statement already has a proof body you must preserve, since
the `:= by sorry` rewrite discards it.

## Consequences

The plan is a soft instruction: the harness never parses, validates or rewards
the plan, and `extrac_code` (lines 323-337) keeps only the last ```lean4 code
block, which `problem_check` (lines 352-354) splices into the statement via
`replace_statement_in_proof` (lines 210-223). Fidelity between the named
intermediate lemmas and the final proof is therefore left entirely to the
model. The `:= by sorry` rewrite discards any existing proof body and must be
undone by `replace_statement_in_proof`, which refuses proofs that use
`apply?`/`exact?` (lines 211-212) or that lack the `theorem … :=` marker
(lines 220-222). The prompt is tied to the DeepSeek chat template
(`tokenizer.apply_chat_template`), so it cannot be reused for completion-only
models. This site is a process prompt, not a proof: it has no named lemmas of
its own to extract, so it does not carry a theorem-scale `shape`; it supports
survey F §10 rule 4 (extract a `have` into a standalone lemma, whose source
list cites DeepSeek-V2) on the *naming* side, while omitting that rule's
fidelity check.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | no CI workflow in the repository: .github/workflows returns 404 (confirmed via GitHub API and list_files.py at pinned commit 2e9036e11846); no CI builds src/utils.py | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 2e9036e118464aa96a8bebaf9f5b9d091aa3585c | check_provenance.py | 2026-11-12 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | line 341 prompt F-string contains verbatim 'Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan ... The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof' (read of byte-identical local copy code/src/utils.py, provenance pass) | verifier |
| 2 | verified | line 340: formal_statement = lean4_code.split(':=' by')[0] + ':= by sorry'; line 341 prompt begins 'Complete the following Lean 4 code:' and embeds formal_statement | verifier |
| 3 | verified | extrac_code lines 323-337 keeps only the last lean4 code block (matches[-1], prepended with import_head); problem_check lines 352-354 calls replace_statement_in_proof; read of whole copied file found no code parsing or validating the plan text | verifier |
| 4 | verified | line 372 correction prompt contains verbatim 'Before producing the Lean 4 code to formally prove the given theorem, provide a detailed analysis of the error message' | verifier |
| 5 | verified | line 340 trailing comment is '# include sorry https://huggingface.co/deepseek-ai/DeepSeek-Prover-V2-7B' — states the sorry rewrite is to include sorry and cites the model-card URL | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Skill (workflow) entry; provenance passes (code byte-identical at 2e9036e). Read code/src/utils.py: site excerpt lines 339-350 match README verbatim. All four children and closed_by match the code: sorrify-goal (L340 lean4_code.split(':=' by')[0]+':=' by sorry'), plan-first-prompt (L341 F-string), extract-code (extrac_code L323-337 re.findall matches[-1] + import_head), splice-proof (problem_check L352-354 -> replace_statement_in_proof L210-223). It closes: replace_statement_in_proof returns stats_re[:span1].replace('sorry','')+proof_str[span2:], a complete theorem. All 5 claims verified against the file: claim1 prompt quote L341, claim2 L340-341, claim3 no plan parsing, claim4 correction prompt L372, claim5 'include sorry' comment L340. No shape field and that is correct for a skill (shape is theorem-scale only); children are pipeline stages, not lemmas, which the entry states honestly. | reviewer-correctness |
| generality | accept | Move is stated beyond the one harness: aliases (plan-before-proving, chain-of-thought proof planning, decompose-before-prove), the transferable ordering principle (plan instruction placed before the code request, with a fixed := by sorry skeleton), and a mapping to survey F rule 4. When-not-to-use and consequences are honest and specific and match the copied code: DeepSeekNonCoTHandler (lines 384-387) drops both sorry and plan; extrac_code keeps only the last lean4 code block so the plan is never parsed; the := by sorry split discards a prior body; replace_statement_in_proof refuses apply?/exact? (211-212) and non-'theorem :=' proofs (220-222). The entry honestly says the named intermediate lemmas are a soft nudge never read back, so it does not overclaim them as good leaves for a bounded prover. Minor gap, not blocking: it does not positively characterize what would make such lemmas good leaves, but it flags the plan is a prompt convention, not a verified skeleton. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. Commit 2e9036e118464aa96a8bebaf9f5b9d091aa3585c agrees across entry.json, source.json and SOURCE.md; check_provenance.py re-fetched src/utils.py at that commit and it is byte-identical (21675 bytes, sha256 594e183d...). Every permalink uses the same commit and path with line anchors that match the local copy: file blob URL, site #L339-L350 (prover_inference), claim1 #L341 (prompt F-string), claim2 #L340-L341, claim3 #L323-L354, claim4 #L372 (correction prompt), claim5 #L340 (include-sorry comment). Licence LicenseRef-unknown is recorded identically in entry.json, source.json and SOURCE.md, and list_files.py at the pinned commit shows 22 files with no LICEN[CS]E/COPYING/COPYRIGHT/NOTICE/CeCILL, so 'no licence file found at the root' and unknown are correct (protocol decision 1 tags unknown licences). SOURCE.md attribution statement matches. Entry language 'python' is from the copied file extension (src/utils.py), per fields.md; the SOURCE.md 'Language: lean' is the project-level label and is not a provenance-licence defect. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/Goedel-LM/Goedel-Prover-V2 at commit `2e9036e118464aa96a8bebaf9f5b9d091aa3585c`, under `LicenseRef-unknown`; see the [source note](../../sources/goedel-prover-v2/SOURCE.md) for the licence text and attribution.
