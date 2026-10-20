import OriginalRecoveredClosedExpression

/-! Fixed internal-name substitutions for unitary proofs. -/

open Lean Elab Term
namespace DaggerRecoveredUnitaryPrivateExpression

def originalName0 : Name :=
  (.str (.str (.num (.str (.str .anonymous "_private") "UnitaryPiZeroCategory") 0)
    "DaggerUnitarySubgroupoid") "comp_right_piZero")

def currentName0 : Name := `DaggerRecoveredUnitaryPrivate.compRightPiZero

def originalName1 : Name :=
  (.str (.str (.num (.str (.str .anonymous "_private") "UnitaryPiZeroCategory") 0)
    "DaggerUnitarySubgroupoid") "comp_left_piZero")

def currentName1 : Name := `DaggerRecoveredUnitaryPrivate.compLeftPiZero

def originalName2 : Name :=
  (.str (.str (.str (.str (.num (.str (.str .anonymous "_private") "UnitaryIntervalCountability") 0)
    "DaggerUnitaryInterval") "pathCode") "match_1") "splitter")

def currentName2 : Name := `DaggerRecoveredUnitaryPrivate.pathCodeSplitter

def originalName3 : Name :=
  (.str (.str (.str (.str (.num (.str (.str .anonymous "_private") "UnitaryIntervalCountability") 0)
    "DaggerUnitaryInterval") "pathCode") "match_1") "eq_2")

def currentName3 : Name := `DaggerRecoveredUnitaryPrivate.pathCodeEq2

def originalName4 : Name :=
  (.str (.str (.str (.str (.num (.str (.str .anonymous "_private") "UnitaryIntervalCountability") 0)
    "DaggerUnitaryInterval") "pathCode") "match_1") "eq_1")

def currentName4 : Name := `DaggerRecoveredUnitaryPrivate.pathCodeEq1

def originalName5 : Name :=
  (.str (.str (.str (.str (.num (.str (.str .anonymous "_private") "UnitaryIntervalSOACountability")
    0) "DaggerFixedGraphGenerators") "placement") "match_1") "eq_2")

def currentName5 : Name := `DaggerRecoveredUnitaryPrivate.placementEq2

def originalName6 : Name :=
  (.str (.str (.str (.str (.num (.str (.str .anonymous "_private") "UnitaryIntervalSOACountability")
    0) "DaggerFixedGraphGenerators") "placement") "match_1") "splitter")

def currentName6 : Name := `DaggerRecoveredUnitaryPrivate.placementSplitter

def originalName7 : Name :=
  (.str (.str (.str (.str (.num (.str (.str .anonymous "_private") "UnitaryIntervalSOACountability")
    0) "DaggerFixedGraphGenerators") "placement") "match_1") "eq_1")

def currentName7 : Name := `DaggerRecoveredUnitaryPrivate.placementEq1

def renameExpr (e : Expr) : Expr :=
  e.replace fun sub ↦ match sub with
    | .const n ls =>
      if n == originalName0 then some (.const currentName0 ls)
      else if n == originalName1 then some (.const currentName1 ls)
      else if n == originalName2 then some (.const currentName2 ls)
      else if n == originalName3 then some (.const currentName3 ls)
      else if n == originalName4 then some (.const currentName4 ls)
      else if n == originalName5 then some (.const currentName5 ls)
      else if n == originalName6 then some (.const currentName6 ls)
      else if n == originalName7 then some (.const currentName7 ls)
      else none
    | _ => none

/-- Apply fixed internal-name substitutions before ordinary type checking. -/
elab "recovered_unitary_private_expr%" data:ident i:num : term => do
  let stx ← `(recovered_closed_expr% $data:ident $i:num)
  return renameExpr (← elabTerm stx none)

end DaggerRecoveredUnitaryPrivateExpression
