import FiniteSSetIhomAccessibility

/-! Whole tensor sources retain their presentability rank for every finite parameter. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory
open DaggerFiniteSSetIhomAccessibility
universe u
namespace DaggerFiniteTensorSourcePresentability
noncomputable section
local instance nativeBraiding : BraidedCategory SSet.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

theorem tensor_presentable (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (X K : SSet.{u}) [IsCardinalPresentable X κ] [K.Finite] :
    IsCardinalPresentable (X ⊗ K) κ := by
  have : (ihom K).IsCardinalAccessible κ := accessibleAtRegular K κ
  have : IsCardinalPresentable ((tensorLeft K).obj X) κ :=
    (ihom.adjunction K).isCardinalPresentable_leftAdjoint_obj κ X
  exact isCardinalPresentable_of_iso ((BraidedCategory.tensorLeftIsoTensorRight K).app X) κ

end
end DaggerFiniteTensorSourcePresentability
