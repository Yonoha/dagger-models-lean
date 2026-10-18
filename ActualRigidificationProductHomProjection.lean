import OriginalProductHomComparisonReconciledRecovered
import SSetProductGeometric

/-! The actual Hom projection is weak when its second Hom factor is weakly contractible. -/

set_option autoImplicit false
open CategoryTheory EnrichedCategory MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualRigidificationProductHomProjection

noncomputable section

/-- Collapse of the exact second Hom factor suffices for the original first Hom projection. -/
theorem projection_GW {X Y : SSet.{u}}
    (z w : (rigidification.obj (X ⊗ Y)).Obj)
    (h : DaggerSSetGluing.GW
      (toUnit ((rigidification.map (snd X Y)).obj z ⟶[SSet.{u}]
        (rigidification.map (snd X Y)).obj w))) :
    DaggerSSetGluing.GW ((rigidification.map (fst X Y)).map z w) := by
  let A : SSet.{u} := ((rigidification.map (fst X Y)).obj z ⟶[SSet.{u}]
    (rigidification.map (fst X Y)).obj w)
  let B : SSet.{u} := ((rigidification.map (snd X Y)).obj z ⟶[SSet.{u}]
    (rigidification.map (snd X Y)).obj w)
  have : WeakEquivalence (DaggerOriginalProductProjection.sigma X Y z w) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (DaggerOriginalProductProjection.sigma_GW X Y z w)
  have : WeakEquivalence (A ◁ toUnit B) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (DaggerSSetProductGeometric.whiskerLeft_geometric _ h A)
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).1
  have hf : DaggerOriginalProductProjection.sigma X Y z w ≫
      (A ◁ toUnit B) ≫ (ρ_ A).hom = (rigidification.map (fst X Y)).map z w := by
    rw [CartesianMonoidalCategory.whiskerLeft_toUnit_comp_rightUnitor_hom]
    exact DaggerOriginalProductProjection.sigma_fst X Y z w
  rw [← hf]
  infer_instance

end
end DaggerActualRigidificationProductHomProjection
