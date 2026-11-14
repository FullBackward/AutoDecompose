# Sorrify each named have of cases_hierarchical into a hole, keeping the exact glue

| | |
|---|---|
| Kind | instance |
| Move | sorrify-at-failure |
| Language | python |
| Status | draft |
| Source | [ml-hilbert](../../sources/ml-hilbert/SOURCE.md) at `86360f902606` |
| Licence | `AML` |

## Intent

Turn a Lean proof assembled from named `have` steps into the same skeleton with every `have` proof replaced by `:= by sorry`, so the declarations and the glue lines (`exact h2`, `exact h4`) survive intact and each `have` becomes a named hole a repair model can fill one at a time.

## The decomposition

### context `replace_have_proofs_with_sorry`: [`src/tools/lean_utils.py` lines 156-250](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/tools/lean_utils.py#L156-L250) ([local copy](code/src/tools/lean_utils.py))

```python
def replace_have_proofs_with_sorry(theorem_text: str) -> str:
    """
    Replace the proofs of have statements with sorry while preserving the theorem structure.
    
    This function takes a Lean 4 theorem containing have statements and replaces all
    have statement proofs with 'sorry', while keeping the declarations intact.
    
    Handles various Lean 4 syntax patterns:
    - have h : P := by proof
    - have h : P by proof  
    - have h : P := proof
    - have h (params) : P := by proof
    - · have h : P := by proof (with bullet points)
    
    Args:
        theorem_text: String containing a Lean 4 theorem with have statements
        
    Returns:
        String with have statement proofs replaced by sorry
        
    Example:
        Input:
        theorem cases_hierarchical (n : ℕ) : n = 0 ∨ n > 0 := by
          cases' n with k
          · have h1 : 0 = 0 := by rfl
            have h2 : 0 = 0 ∨ 0 > 0 := by
              left
              exact h1
            exact h2
          · have h3 : Nat.succ k > 0 := by
              exact Nat.succ_pos k
            have h4 : Nat.succ k = 0 ∨ Nat.succ k > 0 := by
              right
              exact h3
            exact h4
            
        Output:
        theorem cases_hierarchical (n : ℕ) : n = 0 ∨ n > 0 := by
          cases' n with k
          · have h1 : 0 = 0 := by sorry
            have h2 : 0 = 0 ∨ 0 > 0 := by sorry
            exact h2
          · have h3 : Nat.succ k > 0 := by sorry
            have h4 : Nat.succ k = 0 ∨ Nat.succ k > 0 := by sorry
            exact h4
    """
    if not theorem_text or not theorem_text.strip():
        return theorem_text
    
    lines = theorem_text.split('\n')
    result_lines = []
    i = 0
    
    while i < len(lines):
        line = lines[i]
        stripped_line = line.strip()
        
        # Handle empty lines and comments
        if not stripped_line or stripped_line.startswith('--'):
            result_lines.append(line)
            i += 1
            continue
        
        # Check if this line contains a have statement (accounting for bullets and other prefixes)
        if 'have ' in line:
            have_pos = line.find('have ')
            # Make sure 'have' is at a word boundary (not part of another word)
            if (have_pos == 0 or not line[have_pos - 1].isalnum()) and \
               (have_pos + 4 >= len(line) or not line[have_pos + 4].isalnum()):
                
                # Parse the have statement to extract declaration and proof parts
                have_declaration, next_i = _parse_have_statement(lines, i)
                
                if have_declaration:
                    # Get the prefix before 'have' (bullets, indentation, etc.)
                    prefix = line[:have_pos]
                    
                    result_lines.append(f"{prefix}{have_declaration} := by sorry")
                    
                    # Skip to the next statement after this have block
                    i = next_i
                else:
                    # Couldn't parse the have statement, keep original line
                    result_lines.append(line)
                    i += 1
            else:
                # 'have' is part of another word, keep the line as is
                result_lines.append(line)
                i += 1
        else:
            # No have statement, keep the line as is
            result_lines.append(line)
            i += 1
    
    return '\n'.join(result_lines)
```

### parent `cases_hierarchical`: [`src/tools/lean_utils.py` lines 178-190](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/tools/lean_utils.py#L178-L190) ([local copy](code/src/tools/lean_utils.py))

```python
        theorem cases_hierarchical (n : ℕ) : n = 0 ∨ n > 0 := by
          cases' n with k
          · have h1 : 0 = 0 := by rfl
            have h2 : 0 = 0 ∨ 0 > 0 := by
              left
              exact h1
            exact h2
          · have h3 : Nat.succ k > 0 := by
              exact Nat.succ_pos k
            have h4 : Nat.succ k = 0 ∨ Nat.succ k > 0 := by
              right
              exact h3
            exact h4
```

### child `h1`: [`src/tools/lean_utils.py` lines 180-180](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/tools/lean_utils.py#L180-L180) ([local copy](code/src/tools/lean_utils.py))

```python
          · have h1 : 0 = 0 := by rfl
```

### child `h2`: [`src/tools/lean_utils.py` lines 181-183](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/tools/lean_utils.py#L181-L183) ([local copy](code/src/tools/lean_utils.py))

```python
            have h2 : 0 = 0 ∨ 0 > 0 := by
              left
              exact h1
```

### child `h3`: [`src/tools/lean_utils.py` lines 185-186](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/tools/lean_utils.py#L185-L186) ([local copy](code/src/tools/lean_utils.py))

```python
          · have h3 : Nat.succ k > 0 := by
              exact Nat.succ_pos k
```

### child `h4`: [`src/tools/lean_utils.py` lines 187-189](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/tools/lean_utils.py#L187-L189) ([local copy](code/src/tools/lean_utils.py))

```python
            have h4 : Nat.succ k = 0 ∨ Nat.succ k > 0 := by
              right
              exact h3
```

### How the parts fit

The parent `cases_hierarchical` is a case split: `cases' n with k` opens two branches, and each branch is a two-step chain of named `have`s applied with `exact`. The lemma graph is two parallel chains, depth 2:

```
cases_hierarchical (n : ℕ) : n = 0 ∨ n > 0
├── branch k = 0
│     h2 (0 = 0 ∨ 0 > 0)  ── left; exact h1 ──>  h1 (0 = 0)
│     applied by: exact h2                                (glue, line 184)
└── branch k = succ
      h4 (Nat.succ k = 0 ∨ Nat.succ k > 0)  ── right; exact h3 ──>  h3 (Nat.succ k > 0)
      applied by: exact h4                                      (glue, line 190)
```

Each child is a good leaf: `h1` closes by `rfl` and `h3` by `Nat.succ_pos k` (self-contained statements), while `h2` and `h4` close from a named sibling (`exact h1`, `exact h3`). The move `sorrify-at-failure` then flattens every leaf proof to `:= by sorry`, so the output keeps the same declarations, the same case split and the same `exact h2` / `exact h4` glue, with the four `have` proofs as named holes. The dependence between siblings survives only through the glue: `h2` no longer contains `exact h1` (both are holes), but the shape of what must be filled is unchanged.

## Why it is good

1. **The glue cites `h2`** (`check`). `h2` occurs in the parent site `cases_hierarchical` (lines 178-190) — the glue line `exact h2` at line 184 and the `have h2` declaration at line 181. Locator: [lean_utils.py L178-L190](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/tools/lean_utils.py#L178-L190). Form: `cites(cases_hierarchical, h2)`.
2. **The glue is 13 lines** (`check`). The parent site `cases_hierarchical` spans lines 178-190, matching `shape.glue_lines = 13`. Locator: [lean_utils.py L178-L190](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/tools/lean_utils.py#L178-L190). Form: `lines(cases_hierarchical, 13)`.
3. **The theorem-scale shape is 4 direct lemmas, depth 2, 13 glue lines, children [1, 3, 2, 3]** (`measurement`). Counted from the site line ranges 180, 181-183, 185-186 and 187-189, with h2 depending on h1 and h4 on h3.
4. **The authors state the move in the docstring** (`author-statement`). "Replace the proofs of have statements with sorry while preserving the theorem structure." ([lean_utils.py L158](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/tools/lean_utils.py#L158)).
5. **The same move runs in the harness** (`known-use`). `HILBERTWorker` calls `replace_have_proofs_with_sorry(proof_sketch)` (line 1660) and verifies the result with `is_sorry_ok=True` (line 1672), so a model repairs the sorrified holes one at a time ([HILBERTWorker.py L1659-L1675](https://github.com/apple/ml-hilbert/blob/86360f90260613d21e08a001c83971a1998a5b5e/src/models/HILBERTWorker.py#L1659-L1675)).

## When to use it, and when not

Use it when you have a proof assembled from named `have` steps and you want to keep the skeleton — every `have` declaration, the case split and the exact `exact hN` glue — while turning each leaf proof into a `sorry` hole, so the structure still parses (with `is_sorry_ok=True`) and a downstream model fills one hole at a time.

Do not use it when the block has no named `have` statements (nothing is rewritten); when a `have` cannot be parsed (`_parse_have_statement` returns no declaration, so that line is silently left as-is rather than sorrified); or when you need the proofs themselves rather than holes. The function only sordifies — it never checks that the original proofs were correct, that the holes are fillable, or that the `have` names it keeps still match the glue.

## Consequences

Sorrifying preserves the theorem's skeleton while replacing each leaf proof with a named hole, so the sketch parses and a bounded prover can fill one hole at a time. Obligations it creates: (i) declaration fidelity — the `have` name and type must be reproduced exactly by `_parse_have_statement`, or the glue's `exact hN` no longer names the hole; (ii) coverage — every `have` the glue cites must itself be sorrified, or the sketch will not compile with `is_sorry_ok=True`. Failure modes visible in the code: a single-line `have` and a multi-line `have` are both flattened to `:= by sorry`, so any dependence between children (h2 on h1, h4 on h3) survives only through the glue; and a `have` the parser cannot read is silently left with its original proof instead of being sorrified.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(cases_hierarchical, h2) -> cites: h2 occurs at src/tools/lean_utils.py:181 | check_claims.py |
| 2 | verified | lines(cases_hierarchical, 13) -> lines: site cases_hierarchical has 13 lines | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/apple/ml-hilbert at commit `86360f90260613d21e08a001c83971a1998a5b5e`, under `AML`; see the [source note](../../sources/ml-hilbert/SOURCE.md) for the licence text and attribution.
