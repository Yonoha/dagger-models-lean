import ActualRightConeSingularComparisonIso
import ActualQRealizationQuillen

/-! The literal cone evaluation has exactly the weakness of the original Q-adjunction counit. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory HomotopicalAlgebra
open DaggerModels DaggerModels.OrdinaryRigidification DaggerSSetGluing
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualRightConeSingularComparisonIso
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualRightConeEvaluationCounitReduction
noncomputable section

theorem evaluation_factor (D : SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    realization.{u}.map (coneSingularComparison D v w) ≫
      realizationSingularAdjunction.counit.app
        (NerveVertices.vertexEquiv D v ⟶[SSet.{u}] NerveVertices.vertexEquiv D w) =
      coneEvaluationMap D v w := by
  have h := realizationSingularAdjunction.homEquiv_counit
    (g := coneSingularComparison D v w)
  simpa only [coneSingularComparison, Equiv.symm_apply_apply] using h.symm

theorem evaluation_GW_iff_counit_GW (D : SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    GW (coneEvaluationMap.{u} D v w) ↔
      GW (realizationSingularAdjunction.{u}.counit.app
        (NerveVertices.vertexEquiv D v ⟶[SSet.{u}] NerveVertices.vertexEquiv D w)) := by
  have : IsIso (coneSingularComparison D v w) := comparison_isIso D v w
  have : WeakEquivalence (realization.map (coneSingularComparison D v w)) := inferInstance
  rw [← evaluation_factor]
  constructor
  · intro h
    have : WeakEquivalence (realization.map (coneSingularComparison D v w) ≫
        realizationSingularAdjunction.counit.app _) := (weakEquivalence_iff_GW _).2 h
    exact (weakEquivalence_iff_GW _).1 (weakEquivalence_of_precomp
      (realization.map (coneSingularComparison D v w))
      (realizationSingularAdjunction.counit.app _))
  · intro h
    have : WeakEquivalence (realizationSingularAdjunction.counit.app
      (NerveVertices.vertexEquiv D v ⟶[SSet.{u}] NerveVertices.vertexEquiv D w)) :=
        (weakEquivalence_iff_GW _).2 h
    exact (weakEquivalence_iff_GW _).1 inferInstance

end
end DaggerActualRightConeEvaluationCounitReduction
