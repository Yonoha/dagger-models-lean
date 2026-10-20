import NativeIhomTensorComparison

/-!
# The full native closed comparison is natural in the first domain parameter

The comparison was previously proved natural in the second domain parameter.
Double uncurrying also identifies actual postcomposition by pre(f) exactly.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed
open DaggerNativeIhomTensorComparison
universe u
namespace DaggerNativeIhomTensorFirstNaturality
noncomputable section

theorem pre_first_naturality (K Z : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B) :
    (comparisonIso B K Z).hom ≫ (ihom K).map ((MonoidalClosed.pre f).app Z) =
      (MonoidalClosed.pre (f ▷ K)).app Z ≫ (comparisonIso A K Z).hom := by
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    comparison_uncurry, comparison_uncurry]
  rw [MonoidalCategory.associator_inv_naturality_right_assoc,
    MonoidalClosed.id_tensor_pre_app_comp_ev,
    ← MonoidalCategory.associator_inv_naturality_left_assoc]

end
end DaggerNativeIhomTensorFirstNaturality
