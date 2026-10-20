import NativeMonoRestrictionRelativeWalkingLifting

/-! Restriction by native Kan trivial cofibrations into Kan targets is Kan trivial. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Simplicial HomotopicalAlgebra
open DaggerNativeInnerJoyalMappingWeak DaggerNativeBoundaryJoyalMappingWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeKanTrivialCofibrationRestriction
noncomputable section

theorem trivial_anodyne {A B : SSet.{u}} (j : A ⟶ B) [Cofibration j] [WeakEquivalence j] :
    SSet.anodyneExtensions j := by
  intro E T p hp
  have : Fibration p := (HomotopicalAlgebra.fibration_iff p).mpr hp
  infer_instance

theorem restriction_boundary_lifting {A B : SSet.{u}} (j : A ⟶ B)
    [Cofibration j] [WeakEquivalence j] (Z : SSet.{u}) [Z.KanComplex] (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{u} n).ι ((MonoidalClosed.pre j).app Z) := by
  let sq : SSet.PushoutTensor j (SSet.boundary.{u} n).ι :=
    Functor.PushoutObjObj.ofHasPushout _ _ _
  have h := SSet.anodyneExtensions.pushoutTensorι₁ sq (trivial_anodyne j)
  have hp := h (terminal.from Z)
    ((HomotopicalAlgebra.fibration_iff _).mp (show Fibration (terminal.from Z) by infer_instance))
  have hh := (SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom sq
    (terminalPullback j Z)).mp hp
  simpa only [terminalPullback_π] using hh

theorem restriction_trivial_fibration {A B : SSet.{u}} (j : A ⟶ B)
    [Cofibration j] [WeakEquivalence j] (Z : SSet.{u}) [Z.KanComplex] :
    trivialFibrations SSet.{u} ((MonoidalClosed.pre j).app Z) :=
  (boundary_rlp_iff_trivialFibration _).mp (restriction_boundary_lifting j Z)

theorem restriction_mono_rlp {A B : SSet.{u}} (j : A ⟶ B)
    [Cofibration j] [WeakEquivalence j] (Z : SSet.{u}) [Z.KanComplex] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((MonoidalClosed.pre j).app Z) :=
  boundary_rlp_monomorphisms _ (restriction_boundary_lifting j Z)

end
end DaggerNativeKanTrivialCofibrationRestriction
