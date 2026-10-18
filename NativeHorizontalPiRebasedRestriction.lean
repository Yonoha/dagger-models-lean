import NativeHorizontalPiFamilyLifting

/-! Actual restriction formulas with explicitly identified original target basepoints. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite SSet.KanComplex
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
open DaggerNativeHorizontalPiSections DaggerNativeHorizontalPiRestriction
open DaggerNativeHorizontalPiFamilyLifting
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeHorizontalPiRebasedRestriction
noncomputable section

variable {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u}) (t : ℕ)
  (a : (horizontalMapping L X) _⦋0⦌) (b : (horizontalMapping K X) _⦋0⦌)
  (hb : (horizontalPre i X).app _ a = b)

theorem familyMap_piComparison_restrict (s : π t (horizontalMapping L X) a) :
    familyMap K X t b
        (piComparison K X t b (mapπ (horizontalPre i X) t a b hb s)) =
      i ≫ familyMap L X t a (piComparison L X t a s) := by
  subst b
  exact (congrArg (familyMap K X t (restrictedVertex i X a))
    (piComparison_restrict i X t a s)).trans
      (familyMap_restrict i X t a (piComparison L X t a s))

theorem restriction_mapπ_surjective_rebased [Cofibration i] [WeakEquivalence i]
    [Fibration (C := SSet.{u}) (rowProjection X t)]
    (hL : Function.Surjective (piComparison L X t a))
    (hK : Function.Injective (piComparison K X t b)) :
    Function.Surjective (mapπ (horizontalPre i X) t a b hb) := by
  subst b
  exact restriction_mapπ_surjective i X t a hL hK

end
end DaggerNativeHorizontalPiRebasedRestriction
