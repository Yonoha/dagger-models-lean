import NativeAllCofibrantLocalizationSaturation
import ActualQDerivedAdjunction
import ActualQRealizationWeakEquivalences

/-! The original-Q realization creates the full native Kan weak-equivalence class. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
open DaggerOriginalCounitRightConeQRealizationAdjunction DaggerSSetGluing
open DaggerActualQDualFibrantDerived DaggerActualQDerivedEquivalence
open DaggerActualQDerivedAdjunction
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQRealizationWeakReflection
noncomputable section

/-- Derived equivalence and native localization saturation reflect every original weak map. -/
theorem realization_reflects_weakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    [WeakEquivalence (realization.map f)] : WeakEquivalence f := by
  let L := (weakEquivalences SSet.{u}).Q
  have : ∀ X : SSet.{u}, IsCofibrant X := fun X ↦ inferInstance
  have := doubleLocalization_isLocalization L
  have := rightDerived_isEquivalence L
  have := (derivedAdjunction L).isEquivalence_left_of_isEquivalence_right
  let e := leftDerivedComparisonIso L
  have : IsIso (doubleWeak.Q.map (doubleRealization.map f.op.op)) := by
    apply Localization.inverts doubleWeak.Q doubleWeak
    change weakEquivalences SSet.{u} (realization.map f)
    exact mem_weakEquivalences _
  have h : IsIso (e.inv.app _ ≫
      (doubleLocalization L ⋙ leftDerived L).map f.op.op) := by
    rw [← e.inv.naturality f.op.op]
    change IsIso (doubleWeak.Q.map (doubleRealization.map f.op.op) ≫ e.inv.app _)
    infer_instance
  have hi : IsIso ((leftDerived L).map ((doubleLocalization L).map f.op.op)) :=
    (isIso_comp_left_iff _ _).mp h
  have : IsIso ((doubleLocalization L).map f.op.op) :=
    isIso_of_reflects_iso _ (leftDerived L)
  have : IsIso (L.map f) := this
  exact DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_of_localization_isIso L f

/-- No fibrancy, monomorphism, or finite-dimension assumption is imposed on either original object. -/
theorem realization_weakEquivalence_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence (realization.map f) ↔ WeakEquivalence f := by
  constructor
  · intro hf
    have : WeakEquivalence (realization.map f) := hf
    exact realization_reflects_weakEquivalence f
  · intro hf
    have : WeakEquivalence f := hf
    exact DaggerActualQRealizationWeakEquivalences.realization_weakEquivalence f

/-- The original geometric weak predicate is created by the literal realization functor. -/
theorem realization_GW_iff {X Y : SSet.{u}} (f : X ⟶ Y) : GW (realization.map f) ↔ GW f := by
  rw [← weakEquivalence_iff_GW, ← weakEquivalence_iff_GW, realization_weakEquivalence_iff]

end
end DaggerActualQRealizationWeakReflection
