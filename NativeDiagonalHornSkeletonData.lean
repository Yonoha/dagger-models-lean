import NativeDiagonalHornCellVertical
import NativeSimplicialSkeletonStages

/-! Reuse the original native skeleton, its actual cells and its pointwise pushout coverage. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerNativeDiagonalHornMatrix DaggerNativeSimplicialSkeletonStages
universe u
namespace DaggerNativeDiagonalHornSkeletonData
noncomputable section

abbrev K (n : ℕ) (k : Fin (n + 1)) : SSet.{u} := SSet.horn n k
abbrev base {n : ℕ} (k : Fin (n + 1)) := (⊥ : (K.{u} n k).Subcomplex).ι
abbrev stage {n : ℕ} (k : Fin (n + 1)) (d : ℕ) := SSet.skeletonOfMono (base.{u} k) d
abbrev Cell {n : ℕ} (k : Fin (n + 1)) (d : ℕ) :=
  SSet.relativeCellComplexOfMono.ι (base.{u} k) d
abbrev theta {n : ℕ} (k : Fin (n + 1)) (d : ℕ) (s : Cell.{u} k d) :
    (Δ[d] : SSet.{u}) ⟶ K n k := SSet.yonedaEquiv.symm s.val.val
abbrev oldFace {n : ℕ} (k : Fin (n + 1)) (d : ℕ) (s : Cell.{u} k d) :=
  SSet.relativeCellComplexOfMono.τ s
abbrev newFace {n : ℕ} (k : Fin (n + 1)) (d : ℕ) (s : Cell.{u} k d) :=
  SSet.relativeCellComplexOfMono.β s
abbrev step {n : ℕ} (k : Fin (n + 1)) (d : ℕ) :=
  SSet.relativeCellComplexOfMono.r (base.{u} k) d

theorem oldFace_value {n : ℕ} (k : Fin (n + 1)) (d : ℕ) (s : Cell.{u} k d)
    (h : SimplexCategoryᵒᵖ) (a : (SSet.boundary d : SSet.{u}).obj h) :
    ((oldFace k d s).app h a).val = (theta k d s).app h a.val := rfl

theorem newFace_value {n : ℕ} (k : Fin (n + 1)) (d : ℕ) (s : Cell.{u} k d)
    (h : SimplexCategoryᵒᵖ) (a : (Δ[d] : SSet.{u}).obj h) :
    ((newFace k d s).app h a).val = (theta k d s).app h a := rfl

theorem stage_zero {n : ℕ} (k : Fin (n + 1)) :
    stage.{u} k 0 = (⊥ : (K n k).Subcomplex) := by
  simp [stage, SSet.skeletonOfMono, base]

theorem stage_cover {n : ℕ} (k : Fin (n + 1)) (d : ℕ) (h : SimplexCategoryᵒᵖ)
    (a : (stage.{u} k (d + 1) : SSet.{u}).obj h) :
    (∃ x : (stage k d : SSet.{u}).obj h, (step k d).app h x = a) ∨
      ∃ (s : Cell k d) (t : (Δ[d] : SSet.{u}).obj h), (newFace k d s).app h t = a := by
  cases h with
  | op h =>
    induction h using SimplexCategory.rec with
    | h q =>
      have hc := SSet.relativeCellComplexOfMono.range_r_app_union_range_b_app (base k) d
        (op ⦋q⦌)
      have ha : a ∈ Set.range ((step k d).app (op ⦋q⦌)) ∪
          Set.range ((SSet.relativeCellComplexOfMono.b (base k) d).app (op ⦋q⦌)) :=
        hc.symm ▸ Set.mem_univ a
      rcases ha with ha | ⟨b, hb⟩
      · exact Or.inl ha
      · obtain ⟨s, t, ht⟩ := SSet.relativeCellComplexOfMono.ιB_jointly_surjective b
        have he := congrFun (NatTrans.congr_app
          (SSet.relativeCellComplexOfMono.ιB_b s) (op ⦋q⦌)) t
        change (SSet.relativeCellComplexOfMono.b (base k) d).app (op ⦋q⦌)
          ((SSet.relativeCellComplexOfMono.ιB s).app (op ⦋q⦌) t) =
            (newFace k d s).app (op ⦋q⦌) t at he
        exact Or.inr ⟨s, t, he.symm.trans (ht ▸ hb)⟩

theorem stage_top {n : ℕ} (k : Fin (n + 1)) :
    stage.{u} k (n + 1) = (⊤ : (K n k).Subcomplex) := by
  apply top_unique
  have hsk : (K n k).skeleton (n + 1) = ⊤ := skeleton_eq_top (K n k) (n + 1)
  rw [← hsk]
  exact SSet.skeleton_le_skeletonOfMono (base k) (n + 1)

end
end DaggerNativeDiagonalHornSkeletonData
