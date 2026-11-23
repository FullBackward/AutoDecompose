/-
Print, for every constant of the given Lean modules, the constants that its checked statement and
its checked proof (or definition body) contain. One JSON object per line:

  {"module": ..., "name": ..., "kind": ..., "type": [names], "value": [names]}

This is the prover-backed dependency data ("T2") that library/features/graph.md describes. The
graph of feature_graph.py is made from source text; this file asks the Lean kernel's data instead.

Run it inside the built source, with that source's own toolchain:

  lake env lean --run <path to>/lean_deps.lean Module.One Module.Two > deps.jsonl

The modules must be built first (`lake build Module.One Module.Two`). The script imports with the
default level `private`, which loads the proofs of theorems although the source uses the module
system. Written against Lean v4.36.0-rc2; it uses `importModules`, `Environment.getModuleIdx?`
and `ConstantInfo.value?` only.
-/
import Lean
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def names (xs : Array Name) : Json :=
  Json.arr (xs.map fun n => Json.str n.toString)

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods := args.map String.toName
  let imports : Array Import := mods.toArray.map fun m => { module := m }
  let env ← importModules imports {} (trustLevel := 1024)
  let mut missing : UInt32 := 0
  for m in mods do
    match env.getModuleIdx? m with
    | none =>
      IO.eprintln s!"module not found: {m}"
      missing := missing + 1
    | some idx =>
      let md := env.header.moduleData[idx.toNat]!
      for n in md.constNames do
        match env.find? n with
        | none => pure ()
        | some ci =>
          let val := match ci.value? (allowOpaque := true) with
            | some v => v.getUsedConstants
            | none => #[]
          IO.println (Json.mkObj [
            ("module", Json.str m.toString), ("name", Json.str n.toString), ("kind", Json.str (kindOf ci)),
            ("type", names ci.type.getUsedConstants), ("value", names val)]).compress
  return missing
