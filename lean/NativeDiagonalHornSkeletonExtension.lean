import NativeDiagonalHornStageCells
import NativeDiagonalHornSkeletonGluing

/-! The actual native successor extends the whole original matrix-compatible lifting data. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeDiagonalHornMatrix DaggerNativeDiagonalHornCellGeometry
open DaggerNativeDiagonalHornCellVertical DaggerNativeDiagonalHornSkeletonData
open DaggerNativeDiagonalHornStageCells DaggerNativeDiagonalHornSkeletonGluing
open DaggerNativePartialFaceUnionGeometry
universe u
namespace DaggerNativeDiagonalHornSkeletonExtension
noncomputable section

theorem successor {n : ℕ} (k : Fin (n + 1)) {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hf : ReedyFibration f) (a : hornMatrix n k ⟶ X)
    (b : box (K n k) (Δ[n] : SSet.{u}) ⟶ Y) (sq : CommSq a (matrixInclusion n k) f b)
    (d : ℕ) (g : box (stage k d : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X)
    (hg : GoodStage k f a b d g) :
    ∃ g' : box (stage k (d + 1) : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X,
      GoodStage k f a b (d + 1) g' ∧ boxMap (step k d) (𝟙 (Δ[n] : SSet.{u})) ≫ g' = g := by
  classical
  choose z hzv hzb hzf using (fun s : Cell k d ↦ extend_cell k f hf a b sq d g hg s)
  obtain ⟨g', hgo, hgn⟩ := glue_successor k d X g z hzb
  refine ⟨g', ⟨?_, ?_⟩, hgo⟩
  · apply NatTrans.ext
    funext h
    apply NatTrans.ext
    funext v p
    rcases p with ⟨x, y⟩
    rcases stage_cover k d h x with ⟨x₀, rfl⟩ | ⟨s, t, rfl⟩
    · have ho := congrFun (NatTrans.congr_app (NatTrans.congr_app hgo h) v) (x₀, y)
      change (g'.app h).app v ((step k d).app h x₀, y) = (g.app h).app v (x₀, y) at ho
      change (f.app h).app v ((g'.app h).app v ((step k d).app h x₀, y)) = _
      rw [ho]
      exact congrFun (NatTrans.congr_app (NatTrans.congr_app hg.1 h) v) (x₀, y)
    · have hn := congrFun (NatTrans.congr_app (NatTrans.congr_app (hgn s) h) v) (t, y)
      change (g'.app h).app v ((newFace k d s).app h t, y) = (z s |>.app h).app v (t, y)
        at hn
      change (f.app h).app v ((g'.app h).app v ((newFace k d s).app h t, y)) = _
      rw [hn]
      exact congrFun (NatTrans.congr_app (NatTrans.congr_app (hzf s) h) v) (t, y)
  · intro h v x y hm
    rcases stage_cover k d h x with ⟨x₀, rfl⟩ | ⟨s, t, rfl⟩
    · have ho := congrFun (NatTrans.congr_app (NatTrans.congr_app hgo h) v) (x₀, y)
      exact ho.trans (hg.2 h v x₀ y hm)
    · have hn := congrFun (NatTrans.congr_app (NatTrans.congr_app (hgn s) h) v) (t, y)
      refine hn.trans ?_
      by_cases ht : t ∈ (SSet.boundary d).obj h
      · let u : (SSet.boundary d : SSet.{u}).obj h := ⟨t, ht⟩
        have hb := congrFun (NatTrans.congr_app (NatTrans.congr_app (hzb s) h) v) (u, y)
        exact hb.trans (hg.2 h v ((oldFace k d s).app h u) y hm)
      · have hy := (cellMatrixRow_nonboundary k (theta k d s) h v t y ht).mp hm
        exact congrFun (NatTrans.congr_app (NatTrans.congr_app (hzv s) h) v)
          (t, ⟨y, hy⟩)

end
end DaggerNativeDiagonalHornSkeletonExtension
