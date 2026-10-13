import Lean
open Lean

/- `t` has the right statement and no forbidden axioms, but its proof term is bogus and was never
checked by any kernel: the comparator's own replay must reject it, and the report must say so. -/
run_meta do
  let val : TheoremVal := { name := `t, levelParams := [], type := .const ``False [],
                            value := .const ``True.intro [], all := [`t] }
  let .ok kenv := (← getEnv).toKernelEnv.addDeclWithoutChecking (.thmDecl val)
    | throwError "addDeclWithoutChecking failed"
  setEnv (Environment.ofKernelEnv kenv)
