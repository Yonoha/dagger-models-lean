import ActualRightConeFixedMapEquivalence
import OriginalCounitBNextConeRealizationFactorizationReconciled

/-! The literal original cone-to-Q-singular comparison is an isomorphism, in all degrees. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerActualRightConeFixedMapEquivalence
universe u

namespace DaggerActualRightConeSingularComparisonIso
noncomputable section

theorem comparison_app_bijective (D : SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) (q : SimplexCategoryᵒᵖ) :
    Function.Bijective ((coneSingularComparison.{u} D v w).app q) := by
  have he : (coneSingularComparison D v w).app q =
      fun σ ↦ ULift.up (rightConeEvaluation D v w q.unop.len σ) := by
    funext σ
    apply ULift.ext
    exact coneSingularComparison_app D v w q σ
  rw [he]
  have hb := evaluation_bijective D v w q.unop.len
  constructor
  · intro σ τ h
    exact hb.1 (congrArg ULift.down h)
  · intro f
    obtain ⟨σ, hσ⟩ := hb.2 f.down
    refine ⟨σ, ?_⟩
    apply ULift.ext
    exact hσ

theorem comparison_isIso (D : SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    IsIso (coneSingularComparison.{u} D v w) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  exact (isIso_iff_bijective _).2 (comparison_app_bijective D v w q)

def comparisonIso (D : SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    rightConeSimplices.{u} D v w ≅
      DaggerOriginalCounitRightConeQRealizationAdjunction.singular.{u}.obj
        (NerveVertices.vertexEquiv D v ⟶[SSet.{u}] NerveVertices.vertexEquiv D w) := by
  have : IsIso (coneSingularComparison D v w) := comparison_isIso D v w
  exact asIso (coneSingularComparison D v w)

theorem comparisonIso_hom (D : SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    (comparisonIso.{u} D v w).hom = coneSingularComparison.{u} D v w := rfl

end
end DaggerActualRightConeSingularComparisonIso
