import ActualQRealizationQuillen

/-! Weak-equivalence preservation for the unchanged original-Q realization. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalCounitRightConeQRealizationAdjunction DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQRealizationWeakEquivalences

noncomputable section

/-- Native Brown factorization applies to all simplicial sets, since they are cofibrant. -/
theorem realization_weakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (realization.{u}.map f) := by
  let h : CofibrantBrownFactorization f := Classical.choice inferInstance
  have hi := Functor.PreservesTrivialCofibrations.trivialCofibrations_le
    realization.{u} h.i (mem_trivialCofibrations h.i)
  have hs := Functor.PreservesTrivialCofibrations.trivialCofibrations_le
    realization.{u} h.s (mem_trivialCofibrations h.s)
  change trivialCofibrations SSet.{u} (realization.map h.i) at hi
  change trivialCofibrations SSet.{u} (realization.map h.s) at hs
  rw [mem_trivialCofibrations_iff] at hi hs
  have : WeakEquivalence (realization.map h.i) := hi.2
  have : WeakEquivalence (realization.map h.s) := hs.2
  have hsp : realization.map h.s ≫ realization.map h.p = 𝟙 (realization.obj Y) := by
    rw [← Functor.map_comp, h.s_p, realization.map_id]
  have : WeakEquivalence (realization.map h.p) := weakEquivalence_of_precomp_of_fac hsp
  have hw : WeakEquivalence (realization.map h.i ≫ realization.map h.p) := inferInstance
  rwa [← Functor.map_comp, h.fac] at hw

/-- No monomorphism, fibrancy, or finite-dimension hypothesis is imposed on the original map. -/
theorem realization_GW {X Y : SSet.{u}} (f : X ⟶ Y) (hf : GW f) :
    GW (realization.{u}.map f) := by
  have : WeakEquivalence f := (weakEquivalence_iff_GW f).2 hf
  exact (weakEquivalence_iff_GW _).1 (realization_weakEquivalence f)

end
end DaggerActualQRealizationWeakEquivalences
