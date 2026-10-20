import OriginalRecoveredClosedExpression

/-! Six fixed internal-name substitutions for finite relative cell proofs. -/

open Lean Elab Term
namespace DaggerRecoveredFinitePrivateExpression

def originalName0 : Name :=
  (.str (.str (.str (.str (.num (.str (.str .anonymous "_private") "FiniteDaggerOrientedPlacement")
    0) "DaggerFiniteDaggerExtension") "orientedBeta") "match_1") "splitter")

def currentName0 : Name := `DaggerRecoveredFinitePrivate.orientedBetaSplitter

def originalName1 : Name :=
  (.str (.str (.str (.str (.num (.str (.str .anonymous "_private") "FiniteDaggerOrientedPlacement")
    0) "DaggerFiniteDaggerExtension") "orientedBeta") "match_1") "eq_2")

def currentName1 : Name := `DaggerRecoveredFinitePrivate.orientedBetaEq2

def originalName2 : Name :=
  (.str (.str (.str (.str (.num (.str (.str .anonymous "_private") "FiniteDaggerOrientedPlacement")
    0) "DaggerFiniteDaggerExtension") "orientedBeta") "match_1") "eq_1")

def currentName2 : Name := `DaggerRecoveredFinitePrivate.orientedBetaEq1

def originalName3 : Name :=
  (.str (.str (.str (.str (.str (.num (.str (.str .anonymous "_private")
    "FiniteRelativeBoundaryFiltration") 0) "DaggerFiniteRelativeExtension") "BoundaryFiltration")
    "prependU") "match_1") "eq_2")

def currentName3 : Name := `DaggerRecoveredFinitePrivate.prependUEq2

def originalName4 : Name :=
  (.str (.str (.str (.str (.str (.num (.str (.str .anonymous "_private")
    "FiniteRelativeBoundaryFiltration") 0) "DaggerFiniteRelativeExtension") "BoundaryFiltration")
    "prependU") "match_1") "splitter")

def currentName4 : Name := `DaggerRecoveredFinitePrivate.prependUSplitter

def originalName5 : Name :=
  (.str (.str (.str (.str (.str (.num (.str (.str .anonymous "_private")
    "FiniteRelativeBoundaryFiltration") 0) "DaggerFiniteRelativeExtension") "BoundaryFiltration")
    "prependU") "match_1") "eq_1")

def currentName5 : Name := `DaggerRecoveredFinitePrivate.prependUEq1

def renameExpr (e : Expr) : Expr :=
  e.replace fun sub ↦ match sub with
    | .const n ls =>
      if n == originalName0 then some (.const currentName0 ls)
      else if n == originalName1 then some (.const currentName1 ls)
      else if n == originalName2 then some (.const currentName2 ls)
      else if n == originalName3 then some (.const currentName3 ls)
      else if n == originalName4 then some (.const currentName4 ls)
      else if n == originalName5 then some (.const currentName5 ls)
      else none
    | _ => none

/-- Fixed renaming only, followed by ordinary term checking. -/
elab "recovered_finite_private_expr%" data:ident i:num : term => do
  let stx ← `(recovered_closed_expr% $data:ident $i:num)
  return renameExpr (← elabTerm stx none)

end DaggerRecoveredFinitePrivateExpression
