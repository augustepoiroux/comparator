/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Environment

namespace Comparator

partial def getUsedConstants (e : Lean.Expr) : Array Lean.Name :=
  let base := e.getUsedConstants
  let rec visit (e : Lean.Expr) : StateM (Std.HashSet Lean.Expr × Std.HashSet Lean.Name) Unit := do
    let (visited, _) ← get
    if visited.contains e then
      return
    modify fun (v, n) => (v.insert e, n)
    match e with
    | .forallE _ d b _ => visit d *> visit b
    | .lam _ d b _ => visit d *> visit b
    | .mdata _ b => visit b
    | .letE _ t v b _ => visit t *> visit v *> visit b
    | .app f a => visit f *> visit a
    | .proj typeName _ b => modify (fun (v, n) => (v, n.insert typeName)) *> visit b
    | _ => pure ()
  let (_, (_, projNames)) := (visit e).run ({}, {})
  projNames.fold (init := base) fun acc p => if acc.contains p then acc else acc.push p

def runForUsedConsts [Monad m] (info : Lean.ConstantInfo) (f : Lean.Name → m Unit) : m Unit := do
  (getUsedConstants info.type).forM f
  f info.name
  if let some val := info.value? (allowOpaque := true) then
    (getUsedConstants val).forM f

  match info with
  | .axiomInfo .. | .quotInfo .. | .defnInfo .. | .thmInfo .. | .opaqueInfo .. => return ()
  | .inductInfo info =>
    info.ctors.forM f
    info.all.forM f
  | .ctorInfo info =>
    f info.induct
  | .recInfo info =>
    info.rules.forM fun rule => do
      f rule.ctor
      (getUsedConstants rule.rhs).forM f

end Comparator
