import ActualQKanCounitWeakEquivalence
import ActualRightConeEvaluationCounitReduction
import ActualDaggerQuillenRightConeReduction

/-! The original right-cone evaluation is weak; only the rigidification comparison remains. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite Simplicial EnrichedCategory
open DaggerModels DaggerModels.OrdinaryRigidification DaggerSSetGluing
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerActualRightConeEvaluationCounitReduction
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualRightConeEvaluationWeak
noncomputable section

local instance : ModelCategory DaggerActualRigidificationQuillen.D.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}
local instance : ModelCategory DaggerActualRigidificationQuillen.G.{u} :=
  DaggerActualRigidificationQuillen.modelG.{u}

/-- The full locally Kan hypothesis supplies the exact target Hom's Kan structure. -/
theorem evaluation_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y))
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) : GW (coneEvaluationMap D v w) := by
  have := hD (NerveVertices.vertexEquiv D v) (NerveVertices.vertexEquiv D w)
  exact (evaluation_GW_iff_counit_GW D v w).mpr
    (DaggerActualQKanCounitWeakEquivalence.counit_GW _)

/-- The only remaining right-cone comparison is the unchanged literal rigidification leg. -/
def OrdinaryRightConeRigidificationWeak : Prop :=
  ∀ D : SimplicialCat.{u, u},
    (∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y)) →
    ∀ v w : (coherentNerve.obj D).obj (op ⦋0⦌), GW (coneRigidificationMap D v w)

/-- The actual evaluation leg is proved rather than included in the supplied premise. -/
theorem comparisons_of_rigidification (h : OrdinaryRightConeRigidificationWeak.{u}) :
    DaggerActualQuillenRightConeReduction.OrdinaryRightConeComparisonWeak.{u} := by
  intro D hD v w
  exact ⟨h D hD v w, evaluation_GW D hD v w⟩

/-- The original ordinary counit follows from precisely the remaining rigidification comparison. -/
theorem ordinary_counit_local_of_rigidification (h : OrdinaryRightConeRigidificationWeak.{u}) :
    DaggerActualFibrantCounitReduction.OrdinaryCounitLocalGW.{u} :=
  DaggerActualQuillenRightConeReduction.ordinary_counit_local_of_comparisons
    (comparisons_of_rigidification h)

/-- The full actual dagger Quillen equivalence still awaits that literal remaining comparison. -/
theorem isQuillenEquivalence_of_rigidification (h : OrdinaryRightConeRigidificationWeak.{u}) :
    DaggerActualRigidificationQuillen.adjunction.{u}.IsQuillenEquivalence :=
  DaggerActualQuillenRightConeReduction.isQuillenEquivalence_of_comparisons
    (comparisons_of_rigidification h)

end
end DaggerActualRightConeEvaluationWeak
