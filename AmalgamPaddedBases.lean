import AmalgamPaddedSmallFaces

/-! Exact rank-zero bijections retain the original evaluation and both whole inverse laws. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms DaggerAmalgamRankFiltration

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def baseEquivOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) :
    RawOO C B x b q a d 0 ≃
      ((stage C B x b false 0 (leftObj C B x b a) (leftObj C B x b d)).toSSet.obj q) :=
  Equiv.ofBijective (fun h ↦ ⟨evalOO C B x b q a d 0 h,
    evalOO_mem_stage C B x b q a d 0 h⟩) (by
      constructor
      · intro h k he
        exact evalOO_interior_injective C B x b q a d 0
          ⟨h, by simp [criticalOO]⟩ ⟨k, by simp [criticalOO]⟩
          (congrArg Subtype.val he)
      · intro h
        have hr : rankOf C B x b false q h.val = 0 := by
          have hh := h.property
          change rankOf C B x b false q h.val ≤ 0 at hh
          omega
        obtain ⟨k, hk⟩ := evalOO_covers_rank C B x b q a d 0 h.val hr
        exact ⟨k.val, Subtype.ext hk⟩)

theorem baseEquivOO_val (q : SimplexCategoryᵒᵖ) (a d : C.Obj)
    (h : RawOO C B x b q a d 0) :
    (baseEquivOO C B x b q a d h).val = evalOO C B x b q a d 0 h := rfl

def baseEquivON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b) :
    RawON C B x b q a w 0 ≃
      ((stage C B x b true 0 (leftObj C B x b a) (rightObj C B x b w)).toSSet.obj q) :=
  Equiv.ofBijective (fun h ↦ ⟨evalON C B x b q a w 0 h,
    evalON_mem_stage C B x b q a w 0 h⟩) (by
      constructor
      · intro h k he
        exact evalON_interior_injective C B x b q a w hw 0
          ⟨h, by simp [criticalON]⟩ ⟨k, by simp [criticalON]⟩
          (congrArg Subtype.val he)
      · intro h
        have hr : rankOf C B x b true q h.val = 0 := by
          have hh := h.property
          change rankOf C B x b true q h.val ≤ 0 at hh
          omega
        obtain ⟨k, hk⟩ := evalON_covers_rank C B x b q a w hw 0 h.val hr
        exact ⟨k.val, Subtype.ext hk⟩)

theorem baseEquivON_val (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b)
    (h : RawON C B x b q a w 0) :
    (baseEquivON C B x b q a w hw h).val = evalON C B x b q a w 0 h := rfl

def baseEquivNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b) (d : C.Obj) :
    RawNO C B x b q z d 0 ≃
      ((stage C B x b true 0 (rightObj C B x b z) (leftObj C B x b d)).toSSet.obj q) :=
  Equiv.ofBijective (fun h ↦ ⟨evalNO C B x b q z d 0 h,
    evalNO_mem_stage C B x b q z d 0 h⟩) (by
      constructor
      · intro h k he
        exact evalNO_interior_injective C B x b q z d hz 0
          ⟨h, by simp [criticalNO]⟩ ⟨k, by simp [criticalNO]⟩
          (congrArg Subtype.val he)
      · intro h
        have hr : rankOf C B x b true q h.val = 0 := by
          have hh := h.property
          change rankOf C B x b true q h.val ≤ 0 at hh
          omega
        obtain ⟨k, hk⟩ := evalNO_covers_rank C B x b q z d hz 0 h.val hr
        exact ⟨k.val, Subtype.ext hk⟩)

theorem baseEquivNO_val (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b) (d : C.Obj)
    (h : RawNO C B x b q z d 0) :
    (baseEquivNO C B x b q z hz d h).val = evalNO C B x b q z d 0 h := rfl

def baseEquivNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) :
    RawNN C B x b q z w 0 ≃
      ((stage C B x b true 0 (rightObj C B x b z) (rightObj C B x b w)).toSSet.obj q) :=
  Equiv.ofBijective (fun h ↦ ⟨evalNN C B x b q z w 0 h,
    evalNN_mem_stage C B x b q z w 0 h⟩) (by
      constructor
      · intro h k he
        exact evalNN_interior_injective C B x b q z w hz hw 0
          ⟨h, by simp [criticalNN]⟩ ⟨k, by simp [criticalNN]⟩
          (congrArg Subtype.val he)
      · intro h
        have hr : rankOf C B x b true q h.val = 0 := by
          have hh := h.property
          change rankOf C B x b true q h.val ≤ 0 at hh
          omega
        obtain ⟨k, hk⟩ := evalNN_covers_rank C B x b q z w hz hw 0 h.val hr
        exact ⟨k.val, Subtype.ext hk⟩)

theorem baseEquivNN_val (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b)
    (h : RawNN C B x b q z w 0) :
    (baseEquivNN C B x b q z w hz hw h).val = evalNN C B x b q z w 0 h := rfl

end
end DaggerAmalgamPaddedClassifier
