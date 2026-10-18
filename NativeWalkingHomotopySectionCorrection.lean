import NativeMonoRestrictionParameterizedWalkingLifting
import NativeJoyalWeakWholeWalkingInverse
import NativeJoyalWeakRestriction

/-! Correct the full original right J-inverse homotopy to a literal section. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeMonoRestrictionParameterizedWalkingLifting DaggerNativeIhomQuasicategories
open DaggerNativeJoyalMappingTest DaggerNativeJoyalWeakRestriction
universe u
namespace DaggerNativeWalkingHomotopySectionCorrection
noncomputable section

theorem zero_whisker_endpoint (K : SSet.{u}) :
    K ◁ zeroInclusion.{u} = fst K (Δ[0] : SSet.{u}) ≫ intervalEndpoint K false := by
  apply NatTrans.ext
  funext q t
  apply Prod.ext rfl
  exact DaggerNativeWalkingMonoPushout.zeroInclusion_app q t.2

theorem exists_section_of_right_homotopy {E B : SSet.{u}} (p : E ⟶ B) (s : B ⟶ E)
    (H : B ⊗ J.{u} ⟶ B)
    (h0 : intervalEndpoint B false ≫ H = s ≫ p)
    (h1 : intervalEndpoint B true ≫ H = 𝟙 B)
    (hp : HasLiftingProperty (B ◁ zeroInclusion.{u}) p) :
    ∃ r : B ⟶ E, r ≫ p = 𝟙 B := by
  have : HasLiftingProperty (B ◁ zeroInclusion.{u}) p := hp
  let sq : CommSq (fst B (Δ[0] : SSet.{u}) ≫ s) (B ◁ zeroInclusion.{u}) p H :=
    ⟨by simp only [zero_whisker_endpoint, Category.assoc, h0]⟩
  refine ⟨intervalEndpoint B true ≫ sq.lift, ?_⟩
  rw [Category.assoc, sq.fac_right, h1]

theorem weak_mono_restriction_section {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : weakCategoricalEquivalences i) (Z : SSet.{u}) [Z.Quasicategory] :
    ∃ s : (ihom A).obj Z ⟶ (ihom B).obj Z,
      s ≫ (MonoidalClosed.pre i).app Z = 𝟙 _ := by
  have : ((ihom A).obj Z).Quasicategory := ihom_quasicategory A Z
  have : ((ihom B).obj Z).Quasicategory := ihom_quasicategory B Z
  let p := (MonoidalClosed.pre i).app Z
  let d := DaggerNativeJoyalWeakWholeWalkingInverse.fromWeak p (restriction_weak i hi Z)
  exact exists_section_of_right_homotopy p d.inv d.rightCylinder d.right_zero d.right_one
    (restriction_parameter_zero_lifting i Z ((ihom A).obj Z))

end
end DaggerNativeWalkingHomotopySectionCorrection
