import ActualDaggerRigidificationQuillen
import OriginalCounitObjects
import OriginalActualGlobalWeakPropertiesRecovered

/-! Exact remaining counit criterion for the actual rigidification Quillen adjunction. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.DaggerRigidification
open DaggerModels.OrdinaryRigidification.DaggerNerve
open DaggerActualRigidificationQuillen
universe u

namespace DaggerActualQuillenEquivalenceReduction

noncomputable section
local instance : ModelCategory D.{u} := modelD.{u}
local instance : ModelCategory G.{u} := modelG.{u}

/-- Rigidification detects precisely the weak equivalences of the actual source model. -/
theorem weakEquivalence_map_iff {X Y : D.{u}} (f : X ⟶ Y) :
    WeakEquivalence (daggerRigidification.map f) ↔ WeakEquivalence f := by
  rw [weakEquivalence_iff, weakEquivalence_iff, target_weak, source_weak]
  rfl

/-- The literal actual counit has a bijective object function without fibrancy assumptions. -/
theorem counit_obj_bijective (C : G.{u}) :
    Function.Bijective (adjunction.counit.app C).obj := by
  exact DaggerOriginalCounitObjects.dagger_counit_obj_bijective C

/-- Local geometric weakness is the only extra input needed for a weak actual counit. -/
theorem counit_weak_of_local (C : G.{u})
    (hlocal : DaggerGlobalDK.LocalGeometricWeakEquivalence (adjunction.counit.app C)) :
    WeakEquivalence (adjunction.counit.app C) := by
  apply (weakEquivalence_iff _).2
  rw [target_weak]
  exact DaggerGlobalDK.daggerDK_of_surjective_local
    DaggerUnitaryInvariance.standardReplacement _ (counit_obj_bijective C).2 hlocal

/-- This is a reduction theorem; its fibrant-counit premise remains a separate obligation. -/
theorem isQuillenEquivalence_of_counit
    (hcounit : ∀ C : G.{u}, IsFibrant C → WeakEquivalence (adjunction.counit.app C)) :
    adjunction.{u}.IsQuillenEquivalence := by
  refine { toIsQuillenAdjunction := isQuillen, weakEquivalence_homEquiv_iff := ?_ }
  intro X C _ _ f
  have : WeakEquivalence (adjunction.counit.app C) := hcounit C inferInstance
  let g : X ⟶ daggerCoherentNerve.obj C := adjunction.homEquiv X C f
  have htriangle : daggerRigidification.map g ≫ adjunction.counit.app C = f := by
    calc
      daggerRigidification.map g ≫ adjunction.counit.app C =
          (adjunction.homEquiv X C).symm g :=
        (adjunction.homEquiv_counit X C g).symm
      _ = f := Equiv.symm_apply_apply _ _
  calc
    WeakEquivalence g ↔ WeakEquivalence (daggerRigidification.map g) :=
      (weakEquivalence_map_iff g).symm
    _ ↔ WeakEquivalence (daggerRigidification.map g ≫ adjunction.counit.app C) :=
      (weakEquivalence_postcomp_iff _ _).symm
    _ ↔ WeakEquivalence f := by rw [htriangle]

/-- Full equivalence reduces to local geometric weakness of the actual fibrant counits. -/
theorem isQuillenEquivalence_of_local_counit
    (hlocal : ∀ C : G.{u}, IsFibrant C →
      DaggerGlobalDK.LocalGeometricWeakEquivalence (adjunction.counit.app C)) :
    adjunction.{u}.IsQuillenEquivalence := by
  apply isQuillenEquivalence_of_counit
  intro C hC
  exact counit_weak_of_local C (hlocal C hC)

end
end DaggerActualQuillenEquivalenceReduction
