import NativeDiagonalHornSkeletonExtension

/-! Finite native skeleton induction gives the full original matrix inclusion's Reedy lift. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeDiagonalHornMatrix DaggerNativeDiagonalHornSkeletonData
open DaggerNativeDiagonalHornStageCells DaggerNativeDiagonalHornSkeletonExtension
universe u
namespace DaggerNativeDiagonalHornMatrixLifting
noncomputable section

theorem zero_elim {n : ℕ} (k : Fin (n + 1)) (h : SimplexCategoryᵒᵖ)
    (x : (stage.{u} k 0 : SSet.{u}).obj h) : False := by
  have he : (stage.{u} k 0).obj h = ∅ :=
    congrArg (fun S : (K n k).Subcomplex ↦ S.obj h) (stage_zero k)
  have hx : x.val ∈ (∅ : Set ((K n k).obj h)) := he ▸ x.property
  exact hx

def zeroBoxMap {n : ℕ} (k : Fin (n + 1)) (X : BiSSet.{u}) :
    box (stage k 0 : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X where
  app h :=
    { app := fun _ p ↦ (zero_elim k h p.1).elim
      naturality := by intros; funext p; exact (zero_elim k _ p.1).elim }
  naturality _ _ _ := by
    apply NatTrans.ext
    funext v p
    exact (zero_elim k _ p.1).elim

theorem good_stage_exists {n : ℕ} (k : Fin (n + 1)) {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hf : ReedyFibration f) (a : hornMatrix n k ⟶ X)
    (b : box (K n k) (Δ[n] : SSet.{u}) ⟶ Y) (sq : CommSq a (matrixInclusion n k) f b)
    (d : ℕ) : ∃ g : box (stage k d : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X,
      GoodStage k f a b d g := by
  induction d with
  | zero =>
    refine ⟨zeroBoxMap k X, ?_, ?_⟩
    · apply NatTrans.ext
      funext h
      apply NatTrans.ext
      funext v p
      exact (zero_elim k h p.1).elim
    · intro h v x y hm
      exact (zero_elim k h x).elim
  | succ d ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨g', hg', _⟩ := successor k f hf a b sq d g hg
    exact ⟨g', hg'⟩

def fullToStage {n : ℕ} (k : Fin (n + 1)) :
    K.{u} n k ⟶ (stage k (n + 1) : SSet.{u}) where
  app _ a := ⟨a, by rw [stage_top k]; trivial⟩
  naturality _ _ _ := by funext a; apply Subtype.ext; rfl

theorem fullToStage_projection {n : ℕ} (k : Fin (n + 1)) :
    fullToStage.{u} k ≫ (stage k (n + 1)).ι = 𝟙 (K n k) := by
  apply NatTrans.ext
  rfl

theorem matrix_lifting (n : ℕ) (k : Fin (n + 1)) {X Y : BiSSet.{u}}
    (f : X ⟶ Y) (hf : ReedyFibration f) : HasLiftingProperty (matrixInclusion n k) f := by
  constructor
  intro a b sq
  obtain ⟨g, hg⟩ := good_stage_exists k f hf a b sq (n + 1)
  refine ⟨boxMap (fullToStage k) (𝟙 (Δ[n] : SSet.{u})) ≫ g, ?_, ?_⟩
  · apply NatTrans.ext
    funext h
    apply NatTrans.ext
    funext v p
    exact hg.2 h v ((fullToStage k).app h p.val.1) p.val.2 p.property
  · apply NatTrans.ext
    funext h
    apply NatTrans.ext
    funext v p
    exact congrFun (NatTrans.congr_app (NatTrans.congr_app hg.1 h) v)
      ((fullToStage k).app h p.1, p.2)

end
end DaggerNativeDiagonalHornMatrixLifting
