import NativeRealEdgewiseTargetWeak
import TopCatModelCategory.ModelCategorySSet

/-! Raw homotopies preserve native weakness without fibrancy assumptions on the original objects. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRawSSetHomotopyWeak

theorem weak_iff {X Y : SSet.{u}} {f g : X ⟶ Y} (h : SSet.Homotopy f g) :
    WeakEquivalence f ↔ WeakEquivalence g := by
  rw [SSet.modelCategoryQuillen.weakEquivalence_iff,
    SSet.modelCategoryQuillen.weakEquivalence_iff,
    TopCat.modelCategory.weakEquivalence_iff, TopCat.modelCategory.weakEquivalence_iff]
  exact SSet.KanComplex.W.iff_homotopy h.toTop.toSSet

end DaggerNativeRawSSetHomotopyWeak
