/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean
import Export.Parse

namespace Comparator.Parse
open Lean

structure State where
  names : Array Name := #[.anonymous]
  levels : Array Level := #[.zero]
  exprs : Array Expr := #[]
  constMap : Std.HashMap Name ConstantInfo := {}
  constOrder : Array Name := #[]

abbrev M := EStateM String State

@[inline] def peekAt (s : String) (i : Nat) : UInt8 := if h : i < s.utf8ByteSize then s.getUTF8Byte ⟨i⟩ h else 0

@[inline] def matchAt (s : String) (pos : Nat) (lit : String) : Bool :=
  if pos + lit.utf8ByteSize > s.utf8ByteSize then false
  else
    let rec loop (i : Nat) : Bool :=
      if i < lit.utf8ByteSize then
        if peekAt s (pos + i) == peekAt lit i then loop (i + 1) else false
      else true
    loop 0

@[inline] def getName (i : Nat) : M Name := do match (← get).names[i]? with | some x => pure x | none => throw "name"
@[inline] def getLevel (i : Nat) : M Level := do match (← get).levels[i]? with | some x => pure x | none => throw "level"
@[inline] def getExpr (i : Nat) : M Expr := do match (← get).exprs[i]? with | some x => pure x | none => throw "expr"
@[inline] def pushName (n : Name) : M Bool := do modify (fun s => { s with names := s.names.push n }); pure true
@[inline] def pushExpr (e : Expr) : M Bool := do modify (fun s => { s with exprs := s.exprs.push e }); pure true
@[inline] def addConst (name : Name) (ci : ConstantInfo) : M Unit := do
  if (← get).constMap.contains name then throw s!"Duplicate declaration: {name}"
  modify fun s => { s with constMap := s.constMap.insert name ci, constOrder := s.constOrder.push name }

@[inline] def jNat : Json → M Nat | .num ⟨.ofNat n, 0⟩ => pure n | _ => throw "nat"
@[inline] def jStr : Json → M String | .str s => pure s | _ => throw "str"
@[inline] def jBool : Json → M Bool | .bool b => pure b | _ => throw "bool"
@[inline] def jArr : Json → M (Array Json) | .arr a => pure a | _ => throw "arr"
@[inline] def jObj : Json → M (Std.TreeMap.Raw String Json) | .obj o => pure o | _ => throw "obj"
@[inline] def fGet (o : Std.TreeMap.Raw String Json) (k : String) : M Json := match o[k]? with | some v => pure v | none => throw k
@[inline] def fNat (o : Std.TreeMap.Raw String Json) (k : String) : M Nat := fGet o k >>= jNat
@[inline] def fName (o : Std.TreeMap.Raw String Json) (k : String) : M Name := fNat o k >>= getName
@[inline] def fExpr (o : Std.TreeMap.Raw String Json) (k : String) : M Expr := fNat o k >>= getExpr
@[inline] def fBool (o : Std.TreeMap.Raw String Json) (k : String) : M Bool := fGet o k >>= jBool
@[inline] def fStr (o : Std.TreeMap.Raw String Json) (k : String) : M String := fGet o k >>= jStr
@[inline] def fNames (o : Std.TreeMap.Raw String Json) (k : String) : M (List Name) := do (← fGet o k >>= jArr).toList.mapM (jNat · >>= getName)
@[inline] def parseBi : String → M BinderInfo
  | "default" => pure .default | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit | "instImplicit" => pure .instImplicit | s => throw s

def parseSlowItem (line : String) : M Unit := do
  let .ok (.obj top) := Json.parse line | throw "Expected JSON object"
  let kv := match top.toList with
    | [x, y@("in", _)] | [x, y@("il", _)] | [x, y@("ie", _)] => [y, x] | kv => kv
  match kv with
  | [("in", jIdx), (k, j)] =>
    let idx ← jNat jIdx; let d ← jObj j; let pre ← fName d "pre"
    let n ← if k == "str" then .str pre <$> fStr d "str" else if k == "num" then .num pre <$> fNat d "i" else throw k
    if idx != (← get).names.size then throw "in" else modify fun s => { s with names := s.names.push n }
  | [("il", jIdx), (k, j)] =>
    let idx ← jNat jIdx
    let l : Level ← match k with
      | "succ" => .succ <$> (jNat j >>= getLevel)
      | "param" => .param <$> (jNat j >>= getName)
      | "max" | "imax" =>
        let #[a, b] ← jArr j | throw k
        pure ((if k == "max" then Level.max else Level.imax) (← jNat a >>= getLevel) (← jNat b >>= getLevel))
      | _ => throw k
    if idx != (← get).levels.size then throw "il" else modify fun s => { s with levels := s.levels.push l }
  | [("ie", jIdx), (k, j)] =>
    let idx ← jNat jIdx
    let e : Expr ← match k with
      | "bvar" => let b ← jNat j; if b >= 2^20 - 1 then throw "bvar" else pure (.bvar b)
      | "sort" => .sort <$> (jNat j >>= getLevel)
      | "const" => let d ← jObj j; .const (← fName d "name") <$> (← fGet d "us" >>= jArr).toList.mapM (jNat · >>= getLevel)
      | "app" => let d ← jObj j; pure (.app (← fExpr d "fn") (← fExpr d "arg"))
      | "lam" | "forallE" =>
        let d ← jObj j; let c := if k == "lam" then Expr.lam else Expr.forallE
        pure (c (← fName d "name") (← fExpr d "type") (← fExpr d "body") (← fStr d "binderInfo" >>= parseBi))
      | "letE" => let d ← jObj j; pure (.letE (← fName d "name") (← fExpr d "type") (← fExpr d "value") (← fExpr d "body") (← fBool d "nondep"))
      | "proj" => let d ← jObj j; pure (.proj (← fName d "typeName") (← fNat d "idx") (← fExpr d "struct"))
      | "natVal" => (match (← jStr j).toNat? with | some n => pure (.lit (.natVal n)) | none => throw "natVal")
      | "strVal" => (.lit ∘ .strVal) <$> jStr j
      | "mdata" => let d ← jObj j; let _ ← fGet d "data" >>= jObj; .mdata {} <$> fExpr d "expr"
      | _ => throw k
    if idx != (← get).exprs.size then throw "ie" else modify fun s => { s with exprs := s.exprs.push e }
  | [("inductive", .obj d)] =>
    for j in ← fGet d "types" >>= jArr do
      let o ← jObj j; let name ← fName o "name"
      addConst name (.inductInfo { name, levelParams := ← fNames o "levelParams", type := ← fExpr o "type", numParams := ← fNat o "numParams", numIndices := ← fNat o "numIndices", all := ← fNames o "all", ctors := ← fNames o "ctors", numNested := ← fNat o "numNested", isRec := ← fBool o "isRec", isUnsafe := ← fBool o "isUnsafe", isReflexive := ← fBool o "isReflexive" })
    for j in ← fGet d "ctors" >>= jArr do
      let o ← jObj j; let name ← fName o "name"
      addConst name (.ctorInfo { name, levelParams := ← fNames o "levelParams", type := ← fExpr o "type", induct := ← fName o "induct", cidx := ← fNat o "cidx", numParams := ← fNat o "numParams", numFields := ← fNat o "numFields", isUnsafe := ← fBool o "isUnsafe" })
    for j in ← fGet d "recs" >>= jArr do
      let o ← jObj j; let name ← fName o "name"
      let rules ← (← fGet o "rules" >>= jArr).toList.mapM fun r => do
        let ro ← jObj r; pure { ctor := ← fName ro "ctor", nfields := ← fNat ro "nfields", rhs := ← fExpr ro "rhs" }
      addConst name (.recInfo { name, levelParams := ← fNames o "levelParams", type := ← fExpr o "type", all := ← fNames o "all", numParams := ← fNat o "numParams", numIndices := ← fNat o "numIndices", numMotives := ← fNat o "numMotives", numMinors := ← fNat o "numMinors", rules, k := ← fBool o "k", isUnsafe := ← fBool o "isUnsafe" })
  | [(k, .obj d)] =>
    let name ← fName d "name"; let levelParams ← fNames d "levelParams"; let type ← fExpr d "type"
    match k with
    | "axiom" => addConst name (.axiomInfo { name, levelParams, type, isUnsafe := ← fBool d "isUnsafe" })
    | "thm" => addConst name (.thmInfo { name, levelParams, type, value := ← fExpr d "value", all := ← fNames d "all" })
    | "opaque" => addConst name (.opaqueInfo { name, levelParams, type, value := ← fExpr d "value", all := ← fNames d "all", isUnsafe := ← jBool (d["isUnsafe"]?.getD (.bool false)) })
    | "quot" =>
      let kind ← match ← fStr d "kind" with | "type" => pure .type | "ctor" => pure .ctor | "lift" => pure .lift | "ind" => pure .ind | s => throw s
      addConst name (.quotInfo { name, levelParams, type, kind })
    | "def" =>
      let hints ← match ← fGet d "hints" with
        | .str "opaque" => pure .opaque | .str "abbrev" => pure .abbrev
        | .obj h => let r ← fNat h "regular"; if r >= 2^32 then throw "hints" else pure (.regular r.toUInt32)
        | _ => throw "hints"
      let safety ← match ← fStr d "safety" with | "unsafe" => pure .unsafe | "safe" => pure .safe | "partial" => pure .partial | s => throw s
      addConst name (.defnInfo { name, levelParams, type, value := ← fExpr d "value", hints, safety, all := ← fNames d "all" })
    | _ => throw k
  | _ => throw "Unknown export object"

@[inline] def rIdx (r : UInt64) : Nat := (r >>> 32).toNat
@[inline] def rPos (r : UInt64) : Nat := (r &&& 0xFFFFFFFF).toNat
@[inline] def atEnd (s : String) (p stop : Nat) : Bool := p + 1 == stop && peekAt s p == 125

@[inline] def parseIdx (s : String) (pos stop : Nat) : UInt64 :=
  let c0 := peekAt s pos
  if pos >= stop then 0
  else if c0 == 48 then if peekAt s (pos + 1) - 48 < 10 then 0 else (pos + 1).toUInt64
  else if c0 - 49 < 9 then
    let lim := Nat.min stop (pos + 9)
    let rec loop (i : Nat) (acc : UInt64) : UInt64 :=
      let d := peekAt s i - 48
      if i < lim then
        if d < 10 then loop (i + 1) (acc * 10 + d.toUInt64) else (acc <<< 32) ||| i.toUInt64
      else if d < 10 then 0 else (acc <<< 32) ||| i.toUInt64
    loop (pos + 1) (c0 - 48).toUInt64
  else 0

@[inline] def parseLitIdx (s : String) (pos stop : Nat) (lit : String) : UInt64 := if matchAt s pos lit then parseIdx s (pos + lit.utf8ByteSize) stop else 0
@[inline] def stepIdx (s : String) (r : UInt64) (stop : Nat) (lit : String) : UInt64 := if r != 0 then parseLitIdx s (rPos r) stop lit else 0

partial def parseFastLevels (s : String) (pos stop : Nat) (ls : Array Level) (acc : List Level) : UInt64 × List Level :=
  let r := parseIdx s pos stop
  if h : r != 0 ∧ rIdx r < ls.size then
    let c := peekAt s (rPos r)
    if c == 44 then parseFastLevels s (rPos r + 1) stop ls (ls[rIdx r] :: acc)
    else if c == 93 then ((rPos r + 1).toUInt64, (ls[rIdx r] :: acc).reverse) else (0, [])
  else (0, [])

def parseFastBinder (s : String) (pos stop : Nat) (ctor : Name → Expr → Expr → BinderInfo → Expr) (st : State) : Option (Expr × Nat) :=
  let p1 := pos + 15
  let (bi, p2) :=
    if !matchAt s pos "{\"binderInfo\":\"" then (.default, 0)
    else if matchAt s p1 "default\"" then (.default, p1 + 8)
    else if matchAt s p1 "implicit\"" then (.implicit, p1 + 9)
    else if matchAt s p1 "instImplicit\"" then (.instImplicit, p1 + 13)
    else if matchAt s p1 "strictImplicit\"" then (.strictImplicit, p1 + 15) else (.default, 0)
  let rB := if p2 != 0 then parseLitIdx s p2 stop ",\"body\":" else 0
  let rN := stepIdx s rB stop ",\"name\":"; let rT := stepIdx s rN stop ",\"type\":"
  if h : rT != 0 ∧ rPos rT < stop ∧ peekAt s (rPos rT) == 125 ∧ rIdx rB < st.exprs.size ∧ rIdx rN < st.names.size ∧ rIdx rT < st.exprs.size then
    some (ctor st.names[rIdx rN] st.exprs[rIdx rT] st.exprs[rIdx rB] bi, rPos rT + 1)
  else none

def tryFastLine (s : String) (pos stop : Nat) : M Bool := do
  if pos + 10 > stop || stop >= 0x100000000 then return false
  let st ← get
  match peekAt s (pos + 2) with
  | 97 => -- 'a': app
    let r1 := parseLitIdx s pos stop "{\"app\":{\"arg\":"; let r2 := stepIdx s r1 stop ",\"fn\":"; let r3 := stepIdx s r2 stop "},\"ie\":"
    if h : r3 != 0 ∧ atEnd s (rPos r3) stop ∧ rIdx r1 < st.exprs.size ∧ rIdx r2 < st.exprs.size ∧ rIdx r3 == st.exprs.size then
      pushExpr (.app st.exprs[rIdx r2] st.exprs[rIdx r1])
    else return false
  | 99 => -- 'c': const
    let rN := parseLitIdx s pos stop "{\"const\":{\"name\":"
    if h : rN != 0 ∧ rIdx rN < st.names.size ∧ matchAt s (rPos rN) ",\"us\":[" then
      let (p2, us) := if peekAt s (rPos rN + 7) == 93 then ((rPos rN + 8).toUInt64, []) else parseFastLevels s (rPos rN + 7) stop st.levels []
      let rE := stepIdx s p2 stop "},\"ie\":"
      if rE != 0 && atEnd s (rPos rE) stop && rIdx rE == st.exprs.size then pushExpr (.const st.names[rIdx rN] us) else return false
    else return false
  | 102 => -- 'f': forallE
    if let some (e, p1) := if matchAt s pos "{\"forallE\":" then parseFastBinder s (pos + 11) stop .forallE st else none then
      let rE := parseLitIdx s p1 stop ",\"ie\":"
      if rE != 0 && atEnd s (rPos rE) stop && rIdx rE == st.exprs.size then pushExpr e else return false
    else return false
  | 105 => -- 'i': ie (lam) or in (str)
    let r1 := parseLitIdx s pos stop "{\"ie\":"
    if r1 != 0 then
      if let some (e, p2) := if rIdx r1 == st.exprs.size && matchAt s (rPos r1) ",\"lam\":" then parseFastBinder s (rPos r1 + 7) stop .lam st else none then
        if atEnd s p2 stop then pushExpr e else return false
      else return false
    else
      let rN := parseLitIdx s pos stop "{\"in\":"; let rP := stepIdx s rN stop ",\"str\":{\"pre\":"; let p2 := rPos rP
      if h : rP != 0 ∧ rIdx rP < st.names.size ∧ rIdx rN == st.names.size ∧ matchAt s p2 ",\"str\":\"" ∧ stop >= p2 + 11 ∧ matchAt s (stop - 3) "\"}}" then
        let rec checkAscii (i : Nat) : Bool :=
          if i < stop - 3 then let c := peekAt s i; if c >= 32 && c < 127 && c != 34 && c != 92 then checkAscii (i + 1) else false else true
        if checkAscii (p2 + 8) then pushName (.str st.names[rIdx rP] (String.Pos.Raw.extract s ⟨p2 + 8⟩ ⟨stop - 3⟩)) else return false
      else return false
  | _ => return false

partial def scanLineEnd (s : String) (i : Nat) : Nat :=
  if h : i < s.utf8ByteSize then
    let c := s.getUTF8Byte ⟨i⟩ h
    if c == 0 then s.utf8ByteSize + 1 else if c == 10 then i else scanLineEnd s (i + 1)
  else i

@[inline] def parseLine (s : String) (pos lf : Nat) : M Unit := do
  if lf > s.utf8ByteSize then throw "NUL byte in export"
  let stop := if lf > pos && peekAt s (lf - 1) == 13 then lf - 1 else lf
  if !(← tryFastLine s pos stop) then parseSlowItem (String.Pos.Raw.extract s ⟨pos⟩ ⟨stop⟩)

partial def parseLines (s : String) (pos : Nat) : M Unit := do
  if pos < s.utf8ByteSize then
    let lf := scanLineEnd s pos
    parseLine s pos lf
    parseLines s (lf + 1)

def parse (s : String) : IO Export.ExportedEnv := do
  if s.isEmpty then return { constMap := {}, constOrder := #[] }
  let lf := scanLineEnd s 0
  if lf > s.utf8ByteSize then throw (.userError "NUL byte in export")
  match (parseLines s (lf + 1)).run {} with
  | .ok _ st => return { constMap := st.constMap, constOrder := st.constOrder }
  | .error e _ => throw (.userError e)

partial def parseStreamLines (stream : IO.FS.Stream) (st : State) : IO State := do
  let line ← stream.getLine
  if line.isEmpty then return st
  match (parseLine line 0 (scanLineEnd line 0)).run st with
  | .ok _ st' => parseStreamLines stream st'
  | .error e _ => throw (.userError e)

def parseStream (stream : IO.FS.Stream) : IO Export.ExportedEnv := do
  let hdr ← stream.getLine
  if hdr.isEmpty then return { constMap := {}, constOrder := #[] }
  if scanLineEnd hdr 0 > hdr.utf8ByteSize then throw (.userError "NUL byte in export")
  let st ← parseStreamLines stream {}
  return { constMap := st.constMap, constOrder := st.constOrder }

end Comparator.Parse
