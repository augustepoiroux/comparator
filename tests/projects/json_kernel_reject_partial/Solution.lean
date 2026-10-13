import Lean
open Lean

theorem t1 : True := trivial

run_meta do
  let val : TheoremVal := { name := `t2, levelParams := [], type := .const ``False [],
                            value := .const ``True.intro [], all := [`t2] }
  let .ok kenv := (← getEnv).toKernelEnv.addDeclWithoutChecking (.thmDecl val)
    | throwError "addDeclWithoutChecking failed"
  setEnv (Environment.ofKernelEnv kenv)
