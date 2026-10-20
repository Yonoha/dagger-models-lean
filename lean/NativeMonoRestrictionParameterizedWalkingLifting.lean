import NativeMonoRestrictionWalkingLifting
import NativeIhomTensorFirstNaturality

/-! Original mono restriction lifts the zero-J endpoint with every whole source parameter. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeMonoRestrictionWalkingLifting
open DaggerNativeIhomTensorComparison DaggerNativeIhomTensorFirstNaturality
universe u
namespace DaggerNativeMonoRestrictionParameterizedWalkingLifting
noncomputable section

theorem right_tensor_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (K : SSet.{u}) :
    Mono (i ▷ K) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro q
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y h
  change (i.app q x.1, x.2) = (i.app q y.1, y.2) at h
  exact Prod.ext
    ((CategoryTheory.mono_iff_injective (i.app q)).mp inferInstance
      (congrArg (fun z : B.obj q × K.obj q ↦ z.1) h))
    (congrArg (fun z : B.obj q × K.obj q ↦ z.2) h)

theorem restriction_ihom_zero_lifting {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (Z K : SSet.{u}) [Z.Quasicategory] :
    HasLiftingProperty zeroInclusion.{u} ((ihom K).map ((MonoidalClosed.pre i).app Z)) := by
  have : Mono (i ▷ K) := right_tensor_mono i K
  let g := (MonoidalClosed.pre (i ▷ K)).app Z
  let h := (ihom K).map ((MonoidalClosed.pre i).app Z)
  let eA := comparisonIso A K Z
  let eB := comparisonIso B K Z
  have hs : eB.inv ≫ g = h ≫ eA.inv := by
    apply (cancel_mono eA.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← pre_first_naturality K Z i]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let e : Arrow.mk h ≅ Arrow.mk g := Arrow.isoMk eB.symm eA.symm hs
  exact (HasLiftingProperty.iff_of_arrow_iso_right zeroInclusion.{u} e).mpr
    (restriction_zero_lifting (i ▷ K) Z)

theorem restriction_parameter_zero_lifting {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (Z K : SSet.{u}) [Z.Quasicategory] :
    HasLiftingProperty (K ◁ zeroInclusion.{u}) ((MonoidalClosed.pre i).app Z) :=
  ((ihom.adjunction K).hasLiftingProperty_iff zeroInclusion.{u}
    ((MonoidalClosed.pre i).app Z)).mpr (restriction_ihom_zero_lifting i Z K)

end
end DaggerNativeMonoRestrictionParameterizedWalkingLifting
