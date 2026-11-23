import Lean

/-! A shared expression DAG for transporting already constructed proof terms.
This format is untrusted input. Its consumer must use `addDecl`, never insert
declarations directly into an environment. No free or metavariables are admitted.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/

open Lean
namespace Classicism.CertificateData

/- The following scalar JSON codecs are adapted from Lean/Elab/lean,
Copyright (c) 2026 Lean FRO, LLC, Apache 2.0, Sebastian Ullrich. -/
/-- Custom `Name` serialization that preserves the exact structure.
The standard `ToJson`/`FromJson Name` uses `toString`/`toName` which doesn't
round-trip for hygienic names (e.g., names containing `@`). -/
def nameToJson : Name → Json
  | .anonymous => Json.null
  | .str p s   => Json.mkObj [("str", Json.arr #[nameToJson p, toJson s])]
  | .num p n   => Json.mkObj [("num", Json.arr #[nameToJson p, n])]

/-- Inverse of `nameToJson`. -/
partial def nameFromJson? (j : Json) : Except String Name := do
  if j.isNull then return .anonymous
  if let some arr := (j.getObjVal? "str").toOption then
    let #[p, s] := (← fromJson? arr : Array Json) | .error "str expects 2 elements"
    return .str (← nameFromJson? p) (← fromJson? s)
  if let some arr := (j.getObjVal? "num").toOption then
    let #[p, n] := (← fromJson? arr : Array Json) | .error "num expects 2 elements"
    return .num (← nameFromJson? p) (← fromJson? n)
  .error s!"expected Name, got {j}"

/-- Serialize `BinderInfo` to JSON. -/
def binderInfoToJson : BinderInfo → Json
  | .default        => "default"
  | .implicit       => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit   => "instImplicit"

/-- Deserialize `BinderInfo` from JSON. -/
def binderInfoFromJson? : Json → Except String BinderInfo
  | .str "default"        => .ok .default
  | .str "implicit"       => .ok .implicit
  | .str "strictImplicit" => .ok .strictImplicit
  | .str "instImplicit"   => .ok .instImplicit
  | j => .error s!"expected BinderInfo, got {j}"

/-- Serialize `Literal` to JSON. -/
def literalToJson : Literal → Json
  | .natVal n => Json.mkObj [("natVal", n)]
  | .strVal s => Json.mkObj [("strVal", s)]

/-- Deserialize `Literal` from JSON. -/
def literalFromJson? (j : Json) : Except String Literal := do
  if let some n := (j.getObjVal? "natVal").toOption then
    return .natVal (← fromJson? n)
  if let some s := (j.getObjVal? "strVal").toOption then
    return .strVal (← fromJson? s)
  .error s!"expected Literal, got {j}"

/-- Serialize `Level` to JSON. -/
partial def levelToJson : Level → Json
  | .zero     => Json.mkObj [("zero", Json.null)]
  | .succ l   => Json.mkObj [("succ", levelToJson l)]
  | .max a b  => Json.mkObj [("max", Json.arr #[levelToJson a, levelToJson b])]
  | .imax a b => Json.mkObj [("imax", Json.arr #[levelToJson a, levelToJson b])]
  | .param n  => Json.mkObj [("param", nameToJson n)]
  | .mvar id  => Json.mkObj [("mvar", nameToJson id.name)]

/-- Deserialize `Level` from JSON. -/
partial def levelFromJson? (j : Json) : Except String Level := do
  if (j.getObjVal? "zero").toOption.isSome then
    return .zero
  if let some l := (j.getObjVal? "succ").toOption then
    return .succ (← levelFromJson? l)
  if let some arr := (j.getObjVal? "max").toOption then
    let #[a, b] := (← fromJson? arr : Array Json) | .error "max expects 2 elements"
    return .max (← levelFromJson? a) (← levelFromJson? b)
  if let some arr := (j.getObjVal? "imax").toOption then
    let #[a, b] := (← fromJson? arr : Array Json) | .error "imax expects 2 elements"
    return .imax (← levelFromJson? a) (← levelFromJson? b)
  if let some n := (j.getObjVal? "param").toOption then
    return .param (← nameFromJson? n)
  if let some n := (j.getObjVal? "mvar").toOption then
    return .mvar ⟨← nameFromJson? n⟩
  .error s!"expected Level, got {j}"


structure Encoder where
  nodes : Array Json := #[]
  memo : Std.HashMap Expr Nat := {}

partial def encode (e : Expr) : StateT Encoder (Except String) Nat := do
  if let some i := (← get).memo[e]? then return i
  if let .mdata _ b := e then return ← encode b
  let row ← match e with
    | .bvar i => pure #[toJson "bvar", toJson i]
    | .sort u => pure #[toJson "sort", levelToJson u]
    | .const n us => pure #[toJson "const", nameToJson n, toJson (us.map levelToJson)]
    | .app f a => do pure #[toJson "app", toJson (← encode f), toJson (← encode a)]
    | .lam n t b bi => do pure #[toJson "lam", nameToJson n, toJson (← encode t),
        toJson (← encode b), binderInfoToJson bi]
    | .forallE n t b bi => do pure #[toJson "forall", nameToJson n, toJson (← encode t),
        toJson (← encode b), binderInfoToJson bi]
    | .letE n t v b nd => do pure #[toJson "let", nameToJson n, toJson (← encode t),
        toJson (← encode v), toJson (← encode b), toJson nd]
    | .lit l => pure #[toJson "lit", literalToJson l]
    | .proj n i e => do pure #[toJson "proj", nameToJson n, toJson i, toJson (← encode e)]
    | _ => throw "certificate data contains a free variable or metavariable"
  let i := (← get).nodes.size
  modify fun s => { s with nodes := s.nodes.push (.arr row), memo := s.memo.insert e i }
  return i

def decodeNodes (rows : Array Json) : Except String (Array Expr) := do
  let mut nodes := #[]
  for row in rows do
    let a ← row.getArr?
    let field (i : Nat) : Except String Json := match a[i]? with | some x => .ok x | none => .error "missing node field"
    let ref (i : Nat) : Except String Expr := do
      let n : Nat ← fromJson? (← field i)
      match nodes[n]? with | some x => pure x | none => throw "non-backward expression reference"
    let tag : String ← fromJson? (← field 0)
    let e ← match tag with
      | "bvar" => do pure <| Expr.bvar (← fromJson? (← field 1))
      | "sort" => do pure <| Expr.sort (← levelFromJson? (← field 1))
      | "const" => do
          let us : Array Json ← fromJson? (← field 2)
          pure <| Expr.const (← nameFromJson? (← field 1)) (← us.toList.mapM levelFromJson?)
      | "app" => do pure <| Expr.app (← ref 1) (← ref 2)
      | "lam" => do pure <| Expr.lam (← nameFromJson? (← field 1)) (← ref 2) (← ref 3) (← binderInfoFromJson? (← field 4))
      | "forall" => do pure <| Expr.forallE (← nameFromJson? (← field 1)) (← ref 2) (← ref 3) (← binderInfoFromJson? (← field 4))
      | "let" => do pure <| Expr.letE (← nameFromJson? (← field 1)) (← ref 2) (← ref 3) (← ref 4) (← fromJson? (← field 5))
      | "lit" => do pure <| Expr.lit (← literalFromJson? (← field 1))
      | "proj" => do pure <| Expr.proj (← nameFromJson? (← field 1)) (← fromJson? (← field 2)) (← ref 3)
      | _ => throw s!"unknown expression tag {tag}"
    if e.hasMVar || e.hasFVar || e.hasLevelMVar then
      throw "certificate data contains an unresolved variable"
    nodes := nodes.push e
  return nodes

end Classicism.CertificateData
