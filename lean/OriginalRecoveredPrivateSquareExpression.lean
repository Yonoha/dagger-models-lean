import OriginalRecoveredClosedExpression

/-! Rename only the module-private square-index proof; every public type stays unchanged. -/

open Lean Elab Term

namespace DaggerRecoveredPrivateSquareExpression

def originalPrivateName : Name :=
  .str (.str (.num (.str (.str .anonymous "_private") "RLPSquares") 0)
    "DaggerRLPAccessibility") "squareIndex_eq"

def currentPrivateName : Name := `DaggerRecoveredRLPSquaresPrivate.squareIndexEq

def renamePrivateSquareExpr (e : Expr) : Expr :=
  e.replace fun sub ↦ match sub with
    | .const n ls =>
      if n == originalPrivateName then some (.const currentPrivateName ls) else none
    | _ => none

/-- Apply one fixed internal-name substitution before ordinary declaration checking. -/
elab "recovered_private_square_expr%" data:ident i:num : term => do
  let stx ← `(recovered_closed_expr% $data:ident $i:num)
  return renamePrivateSquareExpr (← elabTerm stx none)

end DaggerRecoveredPrivateSquareExpression
