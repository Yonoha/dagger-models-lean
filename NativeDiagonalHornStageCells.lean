import NativeDiagonalHornSkeletonData
import NativeDiagonalHornCellLifting
import NativeReedyBoxExtension

/-! Extend each native skeleton cell while preserving all original matrix data. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeDiagonalHornMatrix DaggerNativeDiagonalHornCellGeometry
open DaggerNativeDiagonalHornCellVertical DaggerNativeDiagonalHornSkeletonData
open DaggerNativeDiagonalHornCellLifting DaggerNativeReedyBoxExtension
open DaggerNativePartialFaceUnionGeometry
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeDiagonalHornStageCells
noncomputable section

def GoodStage {n : ℕ} (k : Fin (n + 1)) {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (a : hornMatrix n k ⟶ X) (b : box (K n k) (Δ[n] : SSet.{u}) ⟶ Y) (d : ℕ)
    (g : box (stage k d : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X) : Prop :=
  g ≫ f = boxMap (stage k d).ι (𝟙 (Δ[n] : SSet.{u})) ≫ b ∧
    ∀ (h v : SimplexCategoryᵒᵖ) (x : (stage k d : SSet.{u}).obj h)
      (y : (Δ[n] : SSet.{u}).obj v) (hm : (x.val, y) ∈ (matrixRow k h).obj v),
      (g.app h).app v (x, y) = (a.app h).app v ⟨(x.val, y), hm⟩

theorem extend_cell {n : ℕ} (k : Fin (n + 1)) {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hf : ReedyFibration f) (a : hornMatrix n k ⟶ X)
    (b : box (K n k) (Δ[n] : SSet.{u}) ⟶ Y) (sq : CommSq a (matrixInclusion n k) f b)
    (d : ℕ) (g : box (stage k d : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X)
    (hg : GoodStage k f a b d g) (s : Cell k d) :
    ∃ z : box (Δ[d] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X,
      boxMap (𝟙 (Δ[d] : SSet.{u})) (faceUnion (cellFaces k (theta k d s))).ι ≫ z =
        verticalMatrixMap k (theta k d s) ≫ a ∧
      boxMap (SSet.boundary d).ι (𝟙 (Δ[n] : SSet.{u})) ≫ z =
        boxMap (oldFace k d s) (𝟙 (Δ[n] : SSet.{u})) ≫ g ∧
      z ≫ f = boxMap (theta k d s) (𝟙 (Δ[n] : SSet.{u})) ≫ b := by
  have : WeakEquivalence (faceUnion (cellFaces k (theta k d s))).ι :=
    ((mem_trivialCofibrations_iff _).mp (cell_vertical_anodyne k (theta k d s))).2
  have : Cofibration (faceUnion (cellFaces k (theta k d s))).ι :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  apply compatible_box_extension (SSet.boundary d).ι
    (faceUnion (cellFaces k (theta k d s))).ι f hf
  · apply NatTrans.ext
    funext h
    apply NatTrans.ext
    funext v p
    exact (hg.2 h v ((oldFace k d s).app h p.1) p.2.val
      (((verticalMatrixMap k (theta k d s)).app h).app v (p.1.val, p.2)).property).symm
  · apply NatTrans.ext
    funext h
    apply NatTrans.ext
    funext v p
    exact congrFun (NatTrans.congr_app (NatTrans.congr_app sq.w h) v)
      (((verticalMatrixMap k (theta k d s)).app h).app v p)
  · apply NatTrans.ext
    funext h
    apply NatTrans.ext
    funext v p
    exact congrFun (NatTrans.congr_app (NatTrans.congr_app hg.1 h) v)
      ((oldFace k d s).app h p.1, p.2)

end
end DaggerNativeDiagonalHornStageCells
