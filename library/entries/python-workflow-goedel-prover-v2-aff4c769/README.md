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
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/Goedel-LM/Goedel-Prover-V2 at commit `2e9036e118464aa96a8bebaf9f5b9d091aa3585c`, under `LicenseRef-unknown`; see the [source note](../../sources/goedel-prover-v2/SOURCE.md) for the licence text and attribution.
