import NativeOrdinaryCoherentRowFactorization
import NativeBisimplicialDiagonalWeak
import NativeDegreeCotensorDiagonal

/-! The SAME original ordinary diagonal comparison is weak, with no target hypothesis. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite DaggerModels
open DaggerNativeBisimplicialDiagonal DaggerNativeBisimplicialDiagonalWeak
open DaggerNativeBisimplicialHorizontalMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOrdinaryCoherentResolutionWeak
noncomputable section

/-- Native diagonal flip is natural for the ENTIRE original bisimplicial map. -/
theorem diagonalFlip_naturality {X Y : BiSSet.{u}} (f : X ⟶ Y) :
    (diagonalFlipIso X).hom ≫ diagonalFunctor.map f =
      diagonalFunctor.map ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map f) ≫
        (diagonalFlipIso Y).hom := by
  apply NatTrans.ext
  funext q p
  rfl

/-- Apply the ORIGINAL diagonal weak theorem to the actual flipped rows. -/
theorem diagonal_weak_of_flipped_rows {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hf : ∀ n, WeakEquivalence (C := SSet.{u})
      (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map f).app n)) :
    WeakEquivalence (diagonalFunctor.map f) := by
  have : WeakEquivalence (diagonalFunctor.map
      ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map f)) :=
    diagonal_map_weak _ hf
  have : WeakEquivalence (diagonalFunctor.map
      ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map f) ≫
        (diagonalFlipIso Y).hom) := inferInstance
  exact weakEquivalence_of_precomp_of_fac (diagonalFlip_naturality f)

/-- This is EXACTLY the original CP229 diagonalComparison, not a substitute map. -/
theorem diagonalComparison_weak (C : SimplicialCat.{u, u}) :
    WeakEquivalence (DaggerNativeDegreeCotensorDiagonal.diagonalComparison C) := by
  change WeakEquivalence (diagonalFunctor.map (DaggerNativeDegreeCotensorComparison.comparison C))
  exact diagonal_weak_of_flipped_rows _ (fun n ↦
    DaggerNativeOrdinaryCoherentRowFactorization.rowComparison_weak C n.unop)

end
end DaggerNativeOrdinaryCoherentResolutionWeak
