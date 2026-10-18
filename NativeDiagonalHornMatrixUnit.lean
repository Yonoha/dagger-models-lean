import NativeDiagonalHornMatrixRows
import NativeBisimplicialDiagonal

/-! The original horn enters the diagonal-face matrix by the literal pair (a,a). -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial Opposite
open DaggerNativeBisimplicialBox DaggerNativeBisimplicialDiagonal
open DaggerNativeDiagonalHornMatrix DaggerNativePartialFaceUnionGeometry
universe u
namespace DaggerNativeDiagonalHornMatrixUnit
noncomputable section

def diagonalHornUnit (n : ℕ) (k : Fin (n + 1)) :
    (SSet.horn.{u} n k : SSet.{u}) ⟶ diagonalFunctor.obj (hornMatrix.{u} n k) where
  app h a := ⟨(a, a.val), by
    obtain ⟨j, hj⟩ := missingFaces_nonempty k h a
    exact (mem_faceUnion (missingFaces k h a) h a.val).mpr
      ⟨j, hj, (Finset.mem_filter.mp hj).2.2⟩⟩
  naturality _ _ _ := by
    funext a
    apply Subtype.ext
    rfl

theorem diagonalHornUnit_value (n : ℕ) (k : Fin (n + 1)) (h : SimplexCategoryᵒᵖ)
    (a : (SSet.horn.{u} n k : SSet.{u}).obj h) :
    ((diagonalHornUnit n k).app h a).val = (a, a.val) := rfl

theorem diagonalHornUnit_projection (n : ℕ) (k : Fin (n + 1)) :
    diagonalHornUnit.{u} n k ≫ diagonalFunctor.map (matrixInclusion n k) ≫
        (diagonalBoxIso (SSet.horn.{u} n k) (Δ[n] : SSet.{u})).hom =
      lift (𝟙 (SSet.horn.{u} n k : SSet.{u})) (SSet.horn n k).ι := by
  apply NatTrans.ext
  rfl

theorem diagonalHornUnit_full_square (n : ℕ) (k : Fin (n + 1)) :
    diagonalHornUnit.{u} n k ≫
        diagonalFunctor.map (matrixInclusion n k ≫ boxMap (SSet.horn n k).ι (𝟙 Δ[n])) ≫
        (diagonalBoxIso (Δ[n] : SSet.{u}) Δ[n]).hom =
      (SSet.horn n k).ι ≫ lift (𝟙 (Δ[n] : SSet.{u})) (𝟙 Δ[n]) := by
  apply NatTrans.ext
  rfl

end
end DaggerNativeDiagonalHornMatrixUnit
