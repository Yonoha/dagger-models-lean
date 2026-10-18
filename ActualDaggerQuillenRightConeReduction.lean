import ActualDaggerFibrantCounitReduction
import OriginalCounitBNextConeRealizationFactorizationReconciled
import ActualQRealizationRepresentableWeakness

/-! The two literal right-cone comparisons suffice for the actual dagger Quillen equivalence. -/

set_option autoImplicit false
open CategoryTheory EnrichedCategory Opposite Simplicial HomotopicalAlgebra
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerChosenRigidificationNecklace hiding C RV
open DaggerOriginalCounitBNextConeCounitFactorization
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerOriginalEnrichedHomTransport DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQuillenRightConeReduction

noncomputable section
local instance : ModelCategory DaggerActualRigidificationQuillen.D.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}
local instance : ModelCategory DaggerActualRigidificationQuillen.G.{u} :=
  DaggerActualRigidificationQuillen.modelG.{u}

/-- Cancel the exact rigidification comparison in the original realized counit factorization. -/
theorem counitHom_GW_of_comparisons (D : DaggerModels.SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌))
    (hR : GW (coneRigidificationMap D v w))
    (hE : GW (coneEvaluationMap D v w)) : GW (counitHom D v w) := by
  have : WeakEquivalence (coneRigidificationMap D v w) := (weakEquivalence_iff_GW _).2 hR
  have : WeakEquivalence (coneEvaluationMap D v w) := (weakEquivalence_iff_GW _).2 hE
  exact (weakEquivalence_iff_GW _).1
    (weakEquivalence_of_precomp_of_fac (coneEvaluationMap_factor D v w))

/-- Remove only the actual original counit endpoint transports. -/
theorem counit_map_GW_of_comparisons (D : DaggerModels.SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌))
    (hR : GW (coneRigidificationMap D v w))
    (hE : GW (coneEvaluationMap D v w)) :
    GW ((rigidificationCoherentNerveAdjunction.counit.app D).map
      (vertexEquiv (coherentNerve.obj D) v) (vertexEquiv (coherentNerve.obj D) w)) := by
  have h := counitHom_GW_of_comparisons D v w hR hE
  change GW ((rigidificationCoherentNerveAdjunction.counit.app D).map
    (vertexEquiv (coherentNerve.obj D) v) (vertexEquiv (coherentNerve.obj D) w) ≫
      targetHomTransport (DaggerOriginalCounitObjects.counit_obj_vertex D v)
        (DaggerOriginalCounitObjects.counit_obj_vertex D w)) at h
  exact (GW_transport_iff _ _ _).1 h

/-- Exact outstanding ordinary comparison maps, with local Kan as the only fibrancy condition. -/
def OrdinaryRightConeComparisonWeak : Prop :=
  ∀ D : DaggerModels.SimplicialCat.{u, u},
    (∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y)) →
    ∀ v w : (coherentNerve.obj D).obj (op ⦋0⦌),
      GW (coneRigidificationMap D v w) ∧ GW (coneEvaluationMap D v w)

/-- The literal two-map comparison implies the unchanged original local counit statement. -/
theorem ordinary_counit_local_of_comparisons (h : OrdinaryRightConeComparisonWeak.{u}) :
    DaggerActualFibrantCounitReduction.OrdinaryCounitLocalGW.{u} := by
  intro D hD a b
  obtain ⟨v, rfl⟩ := (vertexEquiv (coherentNerve.obj D)).surjective a
  obtain ⟨w, rfl⟩ := (vertexEquiv (coherentNerve.obj D)).surjective b
  exact counit_map_GW_of_comparisons D v w (h D hD v w).1 (h D hD v w).2

/-- No model structure or replacement adjunction is supplied by the caller. -/
theorem isQuillenEquivalence_of_comparisons (h : OrdinaryRightConeComparisonWeak.{u}) :
    DaggerActualRigidificationQuillen.adjunction.{u}.IsQuillenEquivalence :=
  DaggerActualFibrantCounitReduction.isQuillenEquivalence_of_ordinary_local
    (ordinary_counit_local_of_comparisons h)

end
end DaggerActualQuillenRightConeReduction
