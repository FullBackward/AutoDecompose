# Extract each have of a proof sketch into a standalone theorem (HILBERT subgoal-extraction prompt)

| | |
|---|---|
| Kind | skill |
| Move | extract-have |
| Language | python |
| Status | draft |
| Source | [ml-hilbert](../../sources/ml-hilbert/SOURCE.md) at `86360f902606` |
| Licence | `LicenseRef-unknown` |

## Intent

Turn a proof sketch — the main theorem with its `have` statements left as
`sorry` — into one standalone theorem per hole, keeping the `have` name and
the context of the preceding subgoals, so each hole can be filled by a
separate prover and the sketch's own application lines remain untouched.

## The decomposition

### skill-text `EXTRACT_SUBGOALS_FROM_SKETCH_PROMPT`: [`src/prompts/hilbert.py` lines 64-87](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/prompts/hilbert.py#L64-L87) ([local copy](code/src/prompts/hilbert.py))

````python
EXTRACT_SUBGOALS_FROM_SKETCH_PROMPT = """From this proof sketch, extract any missing proofs (specified with `sorry`) as independent subgoals (theorems). 
Instructions:
1. Use the same name as the have statements for the theorems.
2. Each subgoal should have the relevant context from the previous subgoals needed to simplify the proof as much as possible.
3. There should be as many extracted theorems as `sorry`s in the given theorem.
4. Do NOT include any imports or open statements. Do NOT add any definitions. ONLY include the theorem statement.
5. Use a separate Lean 4 ``lean`` block for each subgoal.
6. Use sorry for the proof. Do NOT prove any theorem.
7. Do NOT change the conclusion of the theorems from the extracted subgoals. Keep them AS IT IS.
8. Do NOT change the conclusions of the preceding theorems when presenting them as hypotheses for the next subgoals. Keep them AS IT IS.
9. Do NOT duplicate theorem names. Use distinct theorem names for the different theorems.
10. Make sure the names and types of the premises/arguments in the extracted theorems MATCH the subgoals from which they are extracted.

IMPORTANT INSTRUCTION: Do NOT, under ANY circumstances, allow division and subtraction operations on natural number literals with UNDEFINED types, unless REQUIRED by the theorem statement. For example, do NOT allow literals like `1 / 3` or `2 / 5` or `1 - 3` ANYWHERE in the theorem statement. ALWAYS specify the types. AVOID natural number arithmetic UNLESS NEEDED by the theorem statement.
ALWAYS specify types when describing fractions. For example, ((2 : ℝ) / 3) or ((2 : ℚ) / 3) instead of (2 / 3)
IMPORTANT INSTRUCTION: Do NOT, under ANY circumstances, allow division and subtraction operations on variables of type natural numbers (Nat or ℕ), unless REQUIRED by the theorem statement. For example, do NOT allow expressions like (a-b) or (a/b) where a, b are of type ℕ. ALWAYS cast the variables to a suitable type (ℤ, ℚ or ℝ) when performing arithmetic operations. AVOID natural number arithmetic UNLESS NEEDED by the theorem statement.

Lean Hints:
{lean_hints}

Proof Sketch:
```lean4
{proof_sketch}
```"""
````

### context `extract_subgoals_from_sketch`: [`src/models/HILBERTWorker.py` lines 1432-1498](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/models/HILBERTWorker.py#L1432-L1498) ([local copy](code/src/models/HILBERTWorker.py))

```python
    async def extract_subgoals_from_sketch(self, proof_sketch: str, header: str) -> List[str]:
        """
        Extract have statements as standalone theorem statements from a proof sketch.
        
        Args:
            proof_sketch: The proof sketch containing have statements
            
        Returns:
            List of theorem statements extracted from have statements
        """
        if self._closed:
            raise RuntimeError("HILBERTWorker is closed")
        
        # Prompt the LLM to extract have statements as independent theorems
        extract_prompt = EXTRACT_SUBGOALS_FROM_SKETCH_PROMPT.format(proof_sketch=proof_sketch, lean_hints=GENERAL_HINTS)
        
        initial_response = await self.informal_llm_client.simple_chat(
            extract_prompt, 
            max_tokens=16384, 
            reasoning={'effort': 'high'},
            prompt_type=PromptType.SUBGOAL_EXTRACTION.value,
            context="Extracting subgoals from proof sketch"
        )
        logger.info("INITIAL RESPONSE")
        logger.info(initial_response)
        logger.info("\n")
        # Extract theorem statements from the response
        extracted_theorems = extract_all_lean_blocks(initial_response)
        if extracted_theorems is None:
            extracted_theorems = await self._correct_response_for_missing_tags(extract_prompt,
                                                    initial_response,
                                                    MISSING_LEAN_CODE_BLOCK_ERROR_PROMPT,
                                                    extract_all_lean_blocks)
            if extracted_theorems is None:
                return []
        
        extracted_theorems = self.extract_theorems_from_string(extracted_theorems)
        
        logger.info("ALL EXTRACTED THEOREMS")
        for idx, theorem in enumerate(extracted_theorems):
            logger.info(idx)
            logger.info(theorem)
            logger.info(100*"-")
        # Check if all have statements were extracted by comparing with original sketch
        status, missing_theorems = await self._check_and_extract_missing_subgoals(proof_sketch, extracted_theorems)
        if not status:
            logger.info(100*"*")
            logger.info("NOT ALL MISSING THEOREMS COULD BE EXTRACTED, ABANDONING CURRENT ATTEMPT")
            logger.info(100*"*")
            return []
        
        # Combine initial and missing theorems
        all_theorems = extracted_theorems + missing_theorems
        
        # De-duplicate the theorems
        all_theorems = self._deduplicate_theorems(all_theorems)

        # Correct any syntax errors
        corrected_theorems = await self._verify_and_correct_syntax_errors_in_theorems(all_theorems, header)
        final_theorems = []
        if corrected_theorems:
            # check for theorem keyword in all of them
            for theorem in corrected_theorems:
                if bool(re.search(r'\btheorem\b', theorem)):
                    final_theorems.append(theorem)

        return final_theorems
```

### context `rename_theorems`: [`src/models/HILBERTWorker.py` lines 1986-2016](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/models/HILBERTWorker.py#L1986-L2016) ([local copy](code/src/models/HILBERTWorker.py))

```python
    def rename_theorems(self, theorems: List[str], parent_theorem_name: str):
        """
        Rename the list of theorems by appending the parent theorem name to them.
        For example, if the parent theorem is 'theorem main_theorem: ...', and the theorems are named ['theorem h0: ..', 'theorem h1: ...'],
        the renamed theorems will be ['theorem h0_main_theorem: ...', 'theorem h1_main_theorem: ...'].
        """
        renamed_theorems = []
        
        for theorem in theorems:
            try:
                # Extract the current theorem name
                current_name = extract_theorem_name(theorem)
                
                # Create the new name by appending the parent theorem name
                new_name = f"{current_name}_{parent_theorem_name}"
                
                # Replace the old name with the new name in the theorem text
                # Find the pattern "theorem {current_name}" and replace with "theorem {new_name}"
                pattern = rf"theorem(\s+){re.escape(current_name)}"
                replacement = rf"theorem {new_name}"
                renamed_theorem = re.sub(pattern, replacement, theorem, count=1)
                
                renamed_theorems.append(renamed_theorem)
                
            except (ValueError, IndexError) as e:
                # If we can't extract the theorem name, keep the original theorem
                logger.info("Warning: Could not rename theorem due to error: %s", e)
                logger.info("Original theorem: %s", theorem)
                renamed_theorems.append(theorem)
        
        return renamed_theorems    
```

How the parts fit. The prompt (`EXTRACT_SUBGOALS_FROM_SKETCH_PROMPT`) is the
specification of the lift, and the handler method `extract_subgoals_from_sketch`
is the loop that enforces it. The prompt receives the proof sketch as
`{proof_sketch}` and instructs the model to emit, for each `sorry`-ed `have`, a
standalone `theorem` that keeps the `have` name (instruction 1) and carries the
context of the preceding subgoals (instruction 2), one theorem per `sorry`
(instruction 3), statement-only with a `sorry` proof (instructions 4-6). The
main theorem line that applies the haves is left untouched: nothing in the
prompt asks to rewrite the sketch, only to extract from it.

The handler closes the loop. It formats the prompt (line 1446), parses the
model's Lean blocks, then `_check_and_extract_missing_subgoals` compares every
`have` name in the sketch against the extracted theorem names and re-prompts
(via `EXTRACT_MISSING_SUBGOALS_PROMPT`, lines 89-114 of hilbert.py) for any
missing one; if it cannot close the gap it abandons the attempt by returning
`[]` (lines 1476-1481). Finally `rename_theorems` (lines 1986-2016, called from
line 2050) appends the parent theorem name to each child, so `h0` under
`main_theorem` becomes `h0_main_theorem`, giving every child a globally unique
name in the assembled file.

The lemma graph produced by one run is `main_theorem` ← { `h0_main_theorem`,
`h1_main_theorem`, … }, where each `hi_main_theorem` is a leaf — it has no
further children, because the prompt forbids adding definitions or nested
sub-lemmas (instructions 4-5) — and the sketch's own lines are the glue that
applies each `hi` in order. Because no concrete lemma names exist before a run,
the five children below are the invariants the prompt imposes on every
extracted leaf, not concrete instances.

## Why it is good

1. The prompt maps each `sorry` hole to exactly one theorem and keeps the
   `have` name: instruction 1 says "Use the same name as the have statements
   for the theorems" and instruction 3 says "There should be as many extracted
   theorems as `sorry`s in the given theorem" (lines 66-68; `check`).
2. The handler refuses to proceed unless every `have` was extracted:
   `_check_and_extract_missing_subgoals` computes `missing_names` as the
   `have` names absent from the extracted theorem names, and
   `extract_subgoals_from_sketch` returns `[]` — abandoning the attempt — when
   the check fails (HILBERTWorker.py lines 1476-1481 and 1516-1535; `check`).
3. Each child is renamed under the parent theorem name after extraction —
   `new_name = f"{current_name}_{parent_theorem_name}"` (line 2000), called
   from the orchestration loop at line 2050 — so `h0` under `main_theorem`
   becomes `h0_main_theorem` (lines 1986-2016 and 2048-2050; `check`).
4. The prompt carries a standing constraint against undefined natural-number
   arithmetic in the extracted statements: "Do NOT, under ANY circumstances,
   allow division and subtraction operations on natural number literals with
   UNDEFINED types, unless REQUIRED by the theorem statement" (lines 77-79;
   `author-statement`).
5. The extraction prompt is one 24-line string (lines 64-87) with 10 numbered
   instructions (lines 65-75) and two IMPORTANT INSTRUCTION paragraphs (lines
   77 and 79); the consuming method `extract_subgoals_from_sketch` spans 67
   lines (1432-1498) (`measurement`).

In my opinion the load-bearing detail is instruction 1 combined with the
handler's name-based coverage check: keeping the `have` name is what makes the
sketch's application lines stay valid without editing them, and it is also what
turns "did I extract everything?" into a cheap string comparison rather than a
semantic check.

## When to use it, and when not

Use it when you have a skeleton proof with `sorry`-ed `have` holes to farm out
to per-hole provers, and you want each hole to become a self-contained theorem
that keeps the `have` name so the sketch's application lines do not change.
This is the theorem-scale lift AutoDecompose must produce: a main theorem with
its glue (the sketch), plus one named lemma per hole.

Avoid it when the sketch has no named `have` statements (the handler returns
early, `_check_and_extract_missing_subgoals` returning `True, []`), when a hole
needs its conclusion changed or its statement strengthened or weakened
(instructions 7-8 forbid it), or when the holes share context that cannot be
lifted into clean standalone statements. The prompt only extracts: it does not
check that the extracted statements are true or sufficient, which must be done
downstream (survey F §10 rule 1's type/disproof/sufficiency checks, and the
assembly prompt's "ALWAYS use the supplied theorems").

## Consequences

The lift creates one standalone theorem per `sorry`-ed `have`, with the `have`
name preserved and the sketch's application lines untouched, so the sketch
stays valid once each child is proved. Obligations it creates: (i) name and
conclusion fidelity (instructions 1, 7, 10) — a child that changes its
conclusion or argument types would break the sketch, and the prompt forbids
repairing a hole by strengthening or weakening its statement during extraction;
(ii) coverage (instruction 3) — the handler re-prompts for missing `have` names
and abandons the attempt if they cannot be covered; (iii) statement hygiene —
the two IMPORTANT INSTRUCTION paragraphs filter ill-typed natural-number
arithmetic, but this is a literal model instruction, not a type check, so it
can be misapplied. What the prompt does not check is truth and sufficiency:
whether each extracted theorem is true and whether the assembled sketch closes
is decided downstream (the assembly prompt `USE_SKETCH_AND_THEOREMS_TO_PROVE`,
whose instruction is "ALWAYS use the supplied theorems", and the no-`sorry`
check `_check_for_sorries` on the completed proof). Failure modes: an unnamed
`have` (e.g. `have : P := ...`) yields an empty name in `extract_all_have_names`
and is silently dropped from the completeness comparison; the coverage check is
by name only, so two distinct holes with the same `have` name would count as
one.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/apple/ml-hilbert at commit `86360f90260613d21e08a001c83971a1998a5b5e`, under `LicenseRef-unknown`; see the [source note](../../sources/ml-hilbert/SOURCE.md) for the licence text and attribution.
