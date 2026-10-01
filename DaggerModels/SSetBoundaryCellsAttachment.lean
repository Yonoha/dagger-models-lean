import DaggerModels.SSetBoundaryCellsCore
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
Actual ordinary boundary attachments. All new nondegenerate simplices are
individual cells, and the characteristic maps need not be monomorphisms.
Intersection, coverage and uniqueness use this project's checked ordinary
relative-cell boundary and Eilenberg--Zilber normal-form results.
-/

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra

universe u

namespace DaggerModels.SSetBoundaryCells

noncomputable section

variable {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]

theorem step_mem_range_iff {n : ℕ} {k : SimplexCategoryᵒᵖ}
    (x : (stage i (n + 1)).obj k) :
    x ∈ Set.range ((step i n).app k) ↔ x.1 ∈ (SSet.skeletonOfMono i n).obj k := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hx
    exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩

/-- A characteristic cell meets the old stage exactly in its literal boundary. -/
theorem cell_mem_step_range_iff {n : ℕ} (σ : Cells i n)
    (k : SimplexCategoryᵒᵖ) (a : (Δ[n] : SSet.{u}).obj k) :
    (cellLift i σ.1).app k a ∈ Set.range ((step i n).app k) ↔
      a ∈ (SSet.boundary n).obj k := by
  rw [step_mem_range_iff]
  change a ∈ ((SSet.skeletonOfMono i n).preimage
    (SSet.yonedaEquiv.symm σ.1.1)).obj k ↔ _
  rw [RelativeCellBoundary.characteristic_preimage_relativeSkeleton i n σ.1 σ.2]

/-- The old stage and all individual new cells cover the next stage. -/
theorem cell_coverage (n : ℕ) (k : SimplexCategoryᵒᵖ)
    (x : (stage i (n + 1)).obj k) :
    x ∈ Set.range ((step i n).app k) ∨
      ∃ (σ : Cells i n) (a : (Δ[n] : SSet.{u}).obj k), (cellLift i σ.1).app k a = x := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = op ⦋m⦌ := ⟨k.unop.len, by simp⟩
  by_cases hx : x.1 ∈ (SSet.skeletonOfMono i n).obj (op ⦋m⦌)
  · exact Or.inl ((step_mem_range_iff i x).2 hx)
  · obtain ⟨σ, hσ, α, _hα, he⟩ :=
      RelativeCellBoundary.relative_stage_normal_form i x.1 x.2 hx
    exact Or.inr ⟨⟨σ, hσ⟩, ULift.up α, Subtype.ext he.symm⟩

/-- Eilenberg--Zilber uniqueness separates interiors, even for nonmonic cell maps. -/
theorem cell_separation {n : ℕ} (σ τ : Cells i n) (k : SimplexCategoryᵒᵖ)
    (a b : (Δ[n] : SSet.{u}).obj k)
    (ha : a ∉ (SSet.boundary n).obj k) (hb : b ∉ (SSet.boundary n).obj k)
    (he : (cellLift i σ.1).app k a = (cellLift i τ.1).app k b) :
    σ = τ ∧ a = b := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = op ⦋m⦌ := ⟨k.unop.len, by simp⟩
  change ¬ ¬ Function.Surjective a.down.toOrderHom at ha
  change ¬ ¬ Function.Surjective b.down.toOrderHom at hb
  let : Epi a.down := SimplexCategory.epi_iff_surjective.mpr (not_not.mp ha)
  let : Epi b.down := SimplexCategory.epi_iff_surjective.mpr (not_not.mp hb)
  have hv : Y.map a.down.op σ.1.1 = Y.map b.down.op τ.1.1 :=
    congrArg Subtype.val he
  obtain ⟨hσ, hα⟩ := RelativeCellBoundary.relative_stage_normal_form_unique
    (Y.map a.down.op σ.1.1) σ.1 τ.1 a.down b.down rfl hv
  exact ⟨Subtype.ext hσ, ULift.ext _ _ hα⟩

/-- The actual coproduct of all boundary maps at the specified stage. -/
def boundarySumMap (n : ℕ) :
    copies (Cells i n) (SSet.boundary.{u} n).toSSet ⟶ copies (Cells i n) (Δ[n] : SSet.{u}) :=
  copiesMap (Cells i n) (SSet.boundary n).ι

def attachingMap (n : ℕ) : copies (Cells i n) (SSet.boundary.{u} n).toSSet ⟶ stage i n :=
  copiesDesc (boundaryLift i)

def characteristicSum (n : ℕ) : copies (Cells i n) (Δ[n] : SSet.{u}) ⟶ stage i (n + 1) :=
  copiesDesc (fun σ ↦ cellLift i σ.1)

theorem attachment_commutes (n : ℕ) :
    attachingMap i n ≫ step i n = boundarySumMap i n ≫ characteristicSum i n := by
  ext k a
  exact Subtype.ext rfl

/-- The evaluated square is an actual pullback, not merely a preimage inclusion. -/
theorem attachment_app_isPullback (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    IsPullback ((attachingMap i n).app k) ((boundarySumMap i n).app k)
      ((step i n).app k) ((characteristicSum i n).app k) := by
  rw [Types.isPullback_iff]
  refine ⟨NatTrans.congr_app (attachment_commutes i n) k, ?_, ?_⟩
  · rintro ⟨σ, a⟩ ⟨τ, b⟩ ⟨_ht, hl⟩
    have hσ : σ = τ := congrArg Sigma.fst hl
    subst τ
    have hab : a.1 = b.1 := eq_of_heq (Sigma.mk.inj_iff.mp hl).2
    exact congrArg (Sigma.mk σ) (Subtype.ext hab)
  · intro x y he
    have ha := (cell_mem_step_range_iff i y.1 k y.2).1 ⟨x, he⟩
    refine ⟨⟨y.1, ⟨y.2, ha⟩⟩, ?_, rfl⟩
    exact Subtype.ext (congrArg Subtype.val he).symm

/-- Intersection, coverage and unique interiors give the actual pointwise pushout. -/
theorem attachment_app_isPushout (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    IsPushout ((attachingMap i n).app k) ((boundarySumMap i n).app k)
      ((step i n).app k) ((characteristicSum i n).app k) := by
  let : Mono ((step i n).app k) := (mono_iff_injective _).2 (by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : (stage i (n + 1)).obj k ↦ z.1) h)
  apply Types.isPushout_of_isPullback_of_mono' (attachment_app_isPullback i n k)
  · apply Set.eq_univ_of_forall
    intro x
    obtain hx | ⟨σ, a, ha⟩ := cell_coverage i n k x
    · exact Or.inl hx
    · exact Or.inr ⟨⟨σ, a⟩, ha⟩
  · intro a b ha hb he
    have ha' : a.2 ∉ (SSet.boundary n).obj k := by
      intro h
      exact ha ⟨⟨a.1, ⟨a.2, h⟩⟩, rfl⟩
    have hb' : b.2 ∉ (SSet.boundary n).obj k := by
      intro h
      exact hb ⟨⟨b.1, ⟨b.2, h⟩⟩, rfl⟩
    obtain ⟨hσ, hab⟩ := cell_separation i a.1 b.1 k a.2 b.2 ha' hb' he
    cases a
    cases b
    dsimp at hσ hab
    subst hσ
    subst hab
    rfl

/-- Evaluation reflects the actual simplicial pushout of the entire coproduct of cells. -/
theorem attachment_isPushout (n : ℕ) :
    IsPushout (attachingMap i n) (boundarySumMap i n) (step i n) (characteristicSum i n) := by
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk (step i n) (characteristicSum i n) (attachment_commutes i n))
  apply evaluationJointlyReflectsColimits
  intro k
  exact (isColimitMapCoconePushoutCoconeEquiv ((evaluation _ (Type u)).obj k)
    (attachment_commutes i n)).symm (attachment_app_isPushout i n k).isColimit

/-- Every successor attaches all new nondegenerate cells by the original boundary generators. -/
def attachCells (n : ℕ) :
    AttachCells.{u} (fun m : ℕ ↦ (SSet.boundary.{u} m).ι) (step i n) where
  ι := Cells i n
  π _ := n
  cofan₁ := copiesCofan (Cells i n) (SSet.boundary.{u} n).toSSet
  cofan₂ := copiesCofan (Cells i n) (Δ[n] : SSet.{u})
  isColimit₁ := copiesIsColimit _ _
  isColimit₂ := copiesIsColimit _ _
  m := boundarySumMap i n
  hm _σ := rfl
  g₁ := attachingMap i n
  g₂ := characteristicSum i n
  isPushout := attachment_isPushout i n

end
end DaggerModels.SSetBoundaryCells
