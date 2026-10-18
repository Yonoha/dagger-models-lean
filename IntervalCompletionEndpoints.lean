import IntervalCompletionFunctor

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerIntervalNecklaceCompletion

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

def endpointEdge (a b : (E.{u}).obj (op ⦋0⦌)) : Δ[1] ⟶ E.{u} :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₁
    (show nerveEquiv a ⟶ nerveEquiv b from Unit.unit))

theorem endpointEdge_first (a b : (E.{u}).obj (op ⦋0⦌)) :
    (endpointEdge a b).app _ (SSet.stdSimplex.obj₀Equiv.symm 0) = a := by
  apply nerveEquiv.injective
  rfl

theorem endpointEdge_last (a b : (E.{u}).obj (op ⦋0⦌)) :
    (endpointEdge a b).app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last 1)) = b := by
  apply nerveEquiv.injective
  rfl

/-- A positive edge exists for every pair, including equal endpoints. -/
def edgeObject (a b : (E.{u}).obj (op ⦋0⦌)) : NecklacesOver (E.{u}) a b where
  code := single 1
  map := (singleIso 1).hom ≫ endpointEdge a b
  first := by
    change (endpointEdge a b).app _ ((singleIso 1).hom.app _
      ((single 1).verticesEquiv.symm (ULift.up 0))) = a
    rw [singleIso_vertex_symm, endpointEdge_first]
  last := by
    change (endpointEdge a b).app _ ((singleIso 1).hom.app _
      ((single 1).verticesEquiv.symm (ULift.up (Fin.last 1)))) = b
    rw [singleIso_vertex_symm, endpointEdge_last]

/-- The zero-length necklace is a single Delta0, with its same supplied vertex. -/
def pointObject (a : (E.{u}).obj (op ⦋0⦌)) : NecklacesOver (E.{u}) a a where
  code := single 0
  map := (singleIso 0).hom ≫ SSet.yonedaEquiv.symm a
  first := by
    change (SSet.yonedaEquiv.symm a).app _ ((singleIso 0).hom.app _
      ((single 0).verticesEquiv.symm (ULift.up 0))) = a
    rw [singleIso_vertex_symm]
    apply nerveEquiv.injective
    rfl
  last := by
    change (SSet.yonedaEquiv.symm a).app _ ((singleIso 0).hom.app _
      ((single 0).verticesEquiv.symm (ULift.up (Fin.last 0)))) = a
    rw [singleIso_vertex_symm]
    apply nerveEquiv.injective
    rfl

theorem pointObject_len (a : (E.{u}).obj (op ⦋0⦌)) : (pointObject a).code.len = 0 := rfl

theorem edgeObject_len (a b : (E.{u}).obj (op ⦋0⦌)) : (edgeObject a b).code.len = 1 := rfl

end

end DaggerIntervalNecklaceCompletion
