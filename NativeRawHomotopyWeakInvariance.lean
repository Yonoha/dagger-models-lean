import NativeStandardSimplexContraction

/-! Raw simplicial homotopy preserves the original native weak-equivalence class. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRawHomotopyWeakInvariance
noncomputable section

theorem weakEquivalence_iff_homotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : SSet.Homotopy f g) : WeakEquivalence f ↔ WeakEquivalence g := by
  rw [SSet.modelCategoryQuillen.weakEquivalence_iff,
    SSet.modelCategoryQuillen.weakEquivalence_iff,
    TopCat.modelCategory.weakEquivalence_iff, TopCat.modelCategory.weakEquivalence_iff]
  exact SSet.KanComplex.W.iff_homotopy h.toTop.toSSet

theorem collapse_weak_of_const_weak {X : SSet.{u}} (x : X _⦋0⦌)
    (hx : WeakEquivalence (SSet.const x : X ⟶ X)) :
    WeakEquivalence (SSet.const (DaggerNativeStandardSimplexContraction.firstVertex 0) :
      X ⟶ (Δ[0] : SSet.{u})) := by
  let p : X ⟶ (Δ[0] : SSet.{u}) :=
    SSet.const (DaggerNativeStandardSimplexContraction.firstVertex 0)
  let v : (Δ[0] : SSet.{u}) ⟶ X := SSet.const x
  have hpv : p ≫ v = SSet.const x := SSet.comp_const _ _
  have hvp : v ≫ p = 𝟙 _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have : WeakEquivalence (p ≫ v) := hpv ▸ hx
  let r : RetractArrow p (p ≫ v) :=
    { i := Arrow.homMk (𝟙 X) v (by simp)
      r := Arrow.homMk (𝟙 X) p (by simp [Category.assoc, hvp])
      retract := by ext <;> simp [hvp] }
  exact ⟨MorphismProperty.of_retract r (mem_weakEquivalences (p ≫ v))⟩

end
end DaggerNativeRawHomotopyWeakInvariance
