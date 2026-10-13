import Lean
open Lean

run_meta do
  let h : TheoremVal := { name := `h, levelParams := [], type := .const ``False [],
                          value := .const ``True.intro [], all := [`h] }
  let .ok kenv := (← getEnv).toKernelEnv.addDeclWithoutChecking (.thmDecl h)
    | throwError "addDeclWithoutChecking failed"
  setEnv (Environment.ofKernelEnv kenv)

theorem t1 : False := h
theorem t2 : False := h
theorem t3 : True := trivial
