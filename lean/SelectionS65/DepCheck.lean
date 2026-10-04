/-
  S67-08 (scratch).  `#dep_check thm forbid "a", "b", …` walks the TRANSITIVE closure of constants used in the type and
  value of `thm` (theorems included, opaque values included) and reports every constant whose name contains one of
  the given substrings.  Output: `DEPCHECK OK <thm>: <k> constants` or `DEPCHECK FAIL <thm>: [names]`.
  `scripts/audit_gate.py` fails on any DEPCHECK FAIL.
-/
import Lean

open Lean Elab Command

partial def depClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some ci =>
      let vs : Array Name := match ci.value? (allowOpaque := true) with
        | some v => v.getUsedConstants
        | none => #[]
      for c in ci.type.getUsedConstants ++ vs do
        if !seen.contains c then todo := todo.push c
    | none => pure ()
  return seen

syntax (name := depCheck) "#dep_check " ident " forbid " str,* : command

@[command_elab depCheck] def elabDepCheck : CommandElab := fun stx => do
  match stx with
  | `(#dep_check $id:ident forbid $[$ss:str],*) =>
    let env ← getEnv
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let deps := depClosure env n
    let pats : Array String := ss.map (·.getString)
    let bad := deps.toList.filter fun c => pats.any fun p => (c.toString.splitOn p).length > 1
    if bad.isEmpty then
      logInfo m!"DEPCHECK OK {n}: {deps.size} constants, none matching {pats}"
    else
      logInfo m!"DEPCHECK FAIL {n}: {bad}"
  | _ => throwUnsupportedSyntax
