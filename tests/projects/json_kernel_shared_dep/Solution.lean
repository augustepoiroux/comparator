import Lean
open Lean

/- `h : False := True.intro` is never checked by any kernel; `t1` and `t2` genuinely depend on it and
`t3` does not. All three raw declarations are inserted the same way, so that the test does not depend
on whether the elaborator resolves constants added behind its back, which differs between Lean
versions. -/
run_meta do
  let thm (n : Name) (ty val : Expr) : TheoremVal :=
    { name := n, levelParams := [], type := ty, value := val, all := [n] }
  let mut kenv := (← getEnv).toKernelEnv
  for d in [thm `h (.const ``False []) (.const ``True.intro []),
            thm `t1 (.const ``False []) (.const `h []),
            thm `t2 (.const ``False []) (.const `h [])] do
    let .ok k := kenv.addDeclWithoutChecking (.thmDecl d)
      | throwError "addDeclWithoutChecking failed for {d.name}"
    kenv := k
  setEnv (Environment.ofKernelEnv kenv)

theorem t3 : True := trivial
