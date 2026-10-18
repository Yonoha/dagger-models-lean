import NativeRawHomotopyWeakInvariance

/-! Actual maps between simplicial sets with weak collapse maps are weak. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeWeaklyContractibleMaps
noncomputable section

def collapse (X : SSet.{u}) : X ⟶ (Δ[0] : SSet.{u}) :=
  SSet.const (DaggerNativeStandardSimplexContraction.firstVertex 0)

theorem map_weak {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : WeakEquivalence (collapse X)) (hY : WeakEquivalence (collapse Y)) :
    WeakEquivalence f := by
  have : WeakEquivalence (collapse Y) := hY
  have : WeakEquivalence (f ≫ collapse Y) := by
    have h : f ≫ collapse Y = collapse X := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    exact h ▸ hX
  exact weakEquivalence_of_postcomp_of_fac (f := f) (g := collapse Y)
    (fg := f ≫ collapse Y) rfl

theorem collapse_weak_of_const {X : SSet.{u}} (x : X _⦋0⦌)
    (hx : WeakEquivalence (SSet.const x : X ⟶ X)) : WeakEquivalence (collapse X) :=
  DaggerNativeRawHomotopyWeakInvariance.collapse_weak_of_const_weak x hx

end
end DaggerNativeWeaklyContractibleMaps
