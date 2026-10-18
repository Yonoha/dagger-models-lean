import NativeIhomParameterDiagonal

/-! The existing abstract closed-category parameter restriction has its native SSet formula. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite
universe u
namespace DaggerNativeIhomPreApply
noncomputable section

/-- Derived from the ORIGINAL adjunction restriction, not an alternative precomposition. -/
theorem pre_app_apply {K L X : SSet.{u}} (f : L ⟶ K)
    (q r : SimplexCategoryᵒᵖ) (F : ((ihom K).obj X).obj q) (a : q ⟶ r) (k : L.obj r) :
    ((((MonoidalClosed.pre f).app X).app q F).app r a k) = F.app r a (f.app r k) := by
  rw [← MonoidalClosed.curry_uncurry ((MonoidalClosed.pre f).app X),
    ← Category.id_comp ((MonoidalClosed.pre f).app X), MonoidalClosed.uncurry_pre_app]
  change F.app r (a ≫ 𝟙 r) (f.app r k) = F.app r a (f.app r k)
  rw [Category.comp_id]

end
end DaggerNativeIhomPreApply
