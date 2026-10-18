import OriginalRecoveredClosedExpression

/-! Instantiate literal preserved Pi types using normally checked local arguments. -/

open Lean Elab Term

namespace DaggerRecoveredClosedExpressionApplication

private def instantiateParameters (data : TSyntax `ident) (i : TSyntax `num) (args : Array Syntax) :
    TermElabM Expr := do
  let originalSyntax ← `(recovered_closed_expr% $data:ident $i:num)
  let mut type ← elabTerm originalSyntax none
  for arg in args do
    let .forallE _ domain body _ := type.consumeMData
      | throwError "Too many arguments for the original closed Pi type"
    let value ← elabTermEnsuringType arg domain
    type := body.instantiate1 value
  return type

/-- Keep the next original binder domain after checking all preceding arguments. -/
elab "recovered_closed_binder_type%" data:ident i:num "[" args:term,* "]" : term => do
  let type ← instantiateParameters data i (args.getElems.map (·.raw))
  let .forallE _ domain _ _ := type.consumeMData
    | throwError "The original type has no next parameter"
  return domain

/-- Keep the original result type after ordinarily typed parameter substitution. -/
elab "recovered_closed_result_type%" data:ident i:num "[" args:term,* "]" : term => do
  instantiateParameters data i (args.getElems.map (·.raw))

end DaggerRecoveredClosedExpressionApplication
