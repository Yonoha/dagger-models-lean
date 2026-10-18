import NativeBisimplicialDiagonal

/-! Native diagonal precomposition preserves the actual coproducts in the original universe. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialDiagonal
universe u
namespace DaggerNativeBisimplicialDiagonalColimits
noncomputable section

instance diagonal_preservesColimits : PreservesColimitsOfSize.{u, u} diagonalFunctor.{u} := by
  have hu : PreservesColimitsOfSize.{u, u} (Functor.currying (C := SimplexCategoryᵒᵖ)
      (D := SimplexCategoryᵒᵖ) (E := Type u)).functor := inferInstance
  have : PreservesColimitsOfSize.{u, u} (Functor.uncurry (C := SimplexCategoryᵒᵖ)
      (D := SimplexCategoryᵒᵖ) (E := Type u)) := hu
  have hw : PreservesColimitsOfSize.{u, u} ((Functor.whiskeringLeft SimplexCategoryᵒᵖ
      (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (Type u)).obj
        (Functor.diag SimplexCategoryᵒᵖ)) := inferInstance
  unfold diagonalFunctor
  exact comp_preservesColimits _ _

def diagonalSigmaIso {I : Type u} (X : I → BiSSet.{u}) :
    (∐ fun i ↦ diagonalFunctor.obj (X i)) ≅ diagonalFunctor.obj (∐ X) :=
  asIso (sigmaComparison diagonalFunctor X)

end
end DaggerNativeBisimplicialDiagonalColimits
