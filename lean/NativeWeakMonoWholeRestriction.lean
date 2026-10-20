import NativeOriginalWeakPushoutTensor
import NativeMonoRestrictionRelativeWalkingLifting

/-! The entire ambient restriction of every original weak mono is Kan trivial. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open DaggerNativeJoyalMappingTest DaggerNativeOriginalWeakPushoutTensor
open DaggerNativeWeakMonoQuasicategoryExtension DaggerNativeInnerJoyalMappingWeak
open DaggerNativeWalkingMonoPushout DaggerNativeMonoRestrictionRelativeWalkingLifting
open DaggerNativeBoundaryJoyalMappingWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeWeakMonoWholeRestriction
noncomputable section

theorem subcomplex_restriction_boundary {X : SSet.{u}} (A : X.Subcomplex)
    (hA : weakCategoricalEquivalences A.ι) (Z : SSet.{u}) [Z.Quasicategory] (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι ((MonoidalClosed.pre A.ι).app Z) := by
  let sq := SSet.PushoutTensor.unionProd A (SSet.boundary n)
  have hw : weakCategoricalEquivalences sq.ι := pushout_tensor_weak A.ι hA _ sq
  have : Mono sq.ι := by
    dsimp [sq]
    rw [SSet.PushoutTensor.ι_unionProd]
    infer_instance
  have hl := weak_mono_terminal_lifting sq.ι hw Z
  have hh := (SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom sq
    (terminalPullback A.ι Z)).mp hl
  simpa only [terminalPullback_π] using hh

theorem restriction_boundary {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : weakCategoricalEquivalences i) (Z : SSet.{u}) [Z.Quasicategory] (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι ((MonoidalClosed.pre i).app Z) := by
  let e : Arrow.mk i ≅ Arrow.mk (SSet.Subcomplex.range i).ι :=
    Arrow.isoMk (rangeIso i) (Iso.refl _) (by simpa using rangeIso_hom_ι i)
  have hR : weakCategoricalEquivalences (SSet.Subcomplex.range i).ι :=
    weakCategoricalEquivalences.of_retract (Retract.ofIso e.symm) hi
  exact (HasLiftingProperty.iff_of_arrow_iso_right _ (rangeRestrictionArrowIso i Z)).mp
    (subcomplex_restriction_boundary (SSet.Subcomplex.range i) hR Z n)

theorem restriction_Kan_trivial {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : weakCategoricalEquivalences i) (Z : SSet.{u}) [Z.Quasicategory] :
    trivialFibrations SSet.{u} ((MonoidalClosed.pre i).app Z) :=
  (boundary_rlp_iff_trivialFibration _).mp (restriction_boundary i hi Z)

theorem restriction_mono_right {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : weakCategoricalEquivalences i) (Z : SSet.{u}) [Z.Quasicategory] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((MonoidalClosed.pre i).app Z) :=
  boundary_rlp_monomorphisms _ (restriction_boundary i hi Z)

end
end DaggerNativeWeakMonoWholeRestriction
