import Lean

/-! Read the preserved, closed expression DAG into ordinary kernel-checked declarations. -/

set_option autoImplicit false
open Lean Elab Term

namespace DaggerRecoveredClosedExpression

private partial def decodeName (j : Json) : Except String Name := do
  match (← j.getArr?).toList with
  | [] => return .anonymous
  | [.str "s", p, .str s] => return .str (← decodeName p) s
  | [.str "n", p, n] => return .num (← decodeName p) (← n.getNat?)
  | _ => throw "Malformed preserved name"

private partial def decodeLevel (j : Json) : Except String Level := do
  match (← j.getArr?).toList with
  | [.str "z"] => return .zero
  | [.str "s", l] => return .succ (← decodeLevel l)
  | [.str "m", l, r] => return .max (← decodeLevel l) (← decodeLevel r)
  | [.str "i", l, r] => return .imax (← decodeLevel l) (← decodeLevel r)
  | [.str "p", n] => return .param (← decodeName n)
  | _ => throw "Malformed or non-closed preserved universe"

private def decodeBinder (s : String) : Except String BinderInfo :=
  match s with
  | "Lean.BinderInfo.default" => .ok .default
  | "Lean.BinderInfo.implicit" => .ok .implicit
  | "Lean.BinderInfo.strictImplicit" => .ok .strictImplicit
  | "Lean.BinderInfo.instImplicit" => .ok .instImplicit
  | _ => .error "Malformed preserved binder"

private def prior (nodes : Array Expr) (j : Json) : Except String Expr := do
  let i ← j.getNat?
  match nodes[i]? with
  | some e => return e
  | none => throw "Preserved DAG has a missing or forward expression reference"

private def decodeNode (nodes : Array Expr) (j : Json) : Except String Expr := do
  match (← j.getArr?).toList with
  | [.str "b", i] => return .bvar (← i.getNat?)
  | [.str "s", l] => return .sort (← decodeLevel l)
  | [.str "c", n, ls] =>
    return .const (← decodeName n) (← (← ls.getArr?).toList.mapM decodeLevel)
  | [.str "a", f, a] => return .app (← prior nodes f) (← prior nodes a)
  | [.str "l", n, t, b, .str bi] =>
    return .lam (← decodeName n) (← prior nodes t) (← prior nodes b) (← decodeBinder bi)
  | [.str "f", n, t, b, .str bi] =>
    return .forallE (← decodeName n) (← prior nodes t) (← prior nodes b) (← decodeBinder bi)
  | [.str "e", n, t, v, b, nondep] =>
    return .letE (← decodeName n) (← prior nodes t) (← prior nodes v) (← prior nodes b)
      (← nondep.getBool?)
  | [.str "n", n] => return .lit (.natVal (← n.getNat?))
  | [.str "t", .str s] => return .lit (.strVal s)
  | [.str "p", n, i, b] =>
    return .proj (← decodeName n) (← i.getNat?) (← prior nodes b)
  | _ => throw "Unsupported preserved expression; metavariables are forbidden"

private def decodeTerms (literal : String) : Except String (Array Expr) := do
  let data ← Json.parse literal
  let rows ← (← data.getObjVal? "nodes").getArr?
  let mut nodes : Array Expr := #[]
  for row in rows do
    nodes := nodes.push (← decodeNode nodes row)
  return nodes

initialize termCache : IO.Ref (Std.HashMap Name (Array Expr)) ← IO.mkRef {}

private def preservedTerm (dataName : Name) (i : Nat) : TermElabM Expr := do
  let nodes ← match (← termCache.get)[dataName]? with
    | some nodes => pure nodes
    | none =>
      let c ← getConstInfo dataName
      let some value := c.value? true | throwError "Missing literal data definition"
      let .lit (.strVal literal) := value.consumeMData
        | throwError "Recovered expression data must be a literal string definition"
      match decodeTerms literal with
      | .error e => throwError "{e}"
      | .ok nodes =>
        termCache.modify (fun cache ↦ cache.insert dataName nodes)
        pure nodes
  let some e := nodes[i]? | throwError "Missing preserved expression {i}"
  if e.hasMVar || e.hasFVar then throwError "Preserved declaration expression must be closed"
  return e

/-- Decode only literal syntax data; the ordinary declaration elaborator and kernel check it. -/
elab "recovered_closed_expr%" data:ident i:num : term => do
  let dataName ← realizeGlobalConstNoOverload data
  preservedTerm dataName i.getNat

end DaggerRecoveredClosedExpression
