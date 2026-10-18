import NativeDiagonalHornMatrixExtension

/-! The matrix universal property retains the original target maps and face values. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialDiagonal
open DaggerNativeDiagonalHornMatrix DaggerNativeDiagonalHornMatrixFaces
open DaggerNativeDiagonalHornMatrixExtension
universe u
namespace DaggerNativeDiagonalHornMatrixNaturality
noncomputable section

theorem matrixRestriction_post (n : ℕ) (k : Fin (n + 1)) {X Y : BiSSet.{u}}
    (f : X ⟶ Y) (g : hornMatrix n k ⟶ X) :
    matrixRestriction n k Y (g ≫ f) =
      matrixRestriction n k X g ≫ diagonalFunctor.map f := by
  simp only [matrixRestriction, diagonalFunctor.map_comp, Category.assoc]

theorem matrixExtension_post {n : ℕ} (k : Fin (n + 1)) {X Y : BiSSet.{u}}
    (f : X ⟶ Y) (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X) :
    matrixExtension k X a ≫ f = matrixExtension k Y (a ≫ diagonalFunctor.map f) := by
  apply (matrixRestriction_bijective n k Y).injective
  rw [matrixRestriction_post, matrixExtension_restrict, matrixExtension_restrict]

theorem matrixExtension_face {n : ℕ} (k : Fin (n + 1)) (X : BiSSet.{u})
    (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X)
    (j : Fin (n + 1)) (hj : j ≠ k) :
    faceBox k j hj ≫ matrixExtension k X a = faceData k X a j hj := by
  apply NatTrans.ext
  funext h
  apply NatTrans.ext
  funext v p
  exact matrixValue_on_face k X a j hj h v p.1 p.2

theorem matrixHomEquiv_apply (n : ℕ) (k : Fin (n + 1)) (X : BiSSet.{u})
    (f : hornMatrix n k ⟶ X) : matrixHomEquiv n k X f = matrixRestriction n k X f := rfl

theorem matrixHomEquiv_symm_apply (n : ℕ) (k : Fin (n + 1)) (X : BiSSet.{u})
    (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X) :
    (matrixHomEquiv n k X).symm a = matrixExtension k X a := by
  apply (matrixRestriction_bijective n k X).injective
  rw [matrixExtension_restrict]
  exact (matrixHomEquiv n k X).apply_symm_apply a

end
end DaggerNativeDiagonalHornMatrixNaturality
