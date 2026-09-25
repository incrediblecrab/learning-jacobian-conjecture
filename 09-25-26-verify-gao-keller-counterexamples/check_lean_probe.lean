import Lean
open Lean

/-!
Probe run by `check_lean.py` as `lean --run check_lean_probe.lean <theorem> ...`, with the compiled `KellerCE.olean` on `LEAN_PATH`.

It is elaborated without `KellerCE`, then loads that module at run time with `loadExts := false`. So no code from `KellerCE` runs, and none of its environment extensions is read, including the axiom table that Lean precomputes when it writes an `.olean`: `collectAxioms` finds that table empty and walks the declarations' bodies itself.

For each theorem named on the command line it prints two lines: the axioms the theorem depends on, and the constants of `KellerCE` that its statement mentions. The second line shows that a name in a statement, such as `Function.Injective`, refers to Lean core and not to a definition of the same name in `KellerCE`.
-/

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `KellerCE }] {} (loadExts := false)
  let some idx := env.getModuleIdx? `KellerCE
    | IO.eprintln "KellerCE is not among the loaded modules"; return 1
  for arg in args do
    let name := Name.mkStr `KellerCE arg
    match env.find? name with
    | none => IO.println s!"MISSING {arg}"
    | some info =>
      let (axioms, _) ← (collectAxioms name : CoreM (Array Name)).toIO { fileName := "<probe>", fileMap := default } { env }
      let own := info.type.getUsedConstants.filter fun c => env.getModuleIdxFor? c == some idx
      IO.println s!"AXIOMS {arg}: {" ".intercalate (axioms.toList.map toString)}"
      IO.println s!"MENTIONS {arg}: {" ".intercalate (own.toList.map toString)}"
  return 0
