import AmalgamPaddedUnits

/-! Exact original true-letter counts for every raw family, including rank zero.
The already proved actual reduction measure supplies normalization nonincrease. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamPathMeasure

universe u

namespace DaggerAmalgamPaddedClassifier

noncomputable section
set_option autoImplicit false

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem count_zig (q : SimplexCategoryᵒᵖ) (n : ℕ) :
    ∀ us vs, rightCount C B x b q (zig C B x b q n us vs) = n := by
  induction n with
  | zero => intro us vs; rfl
  | succ n ih => intro us vs; simp [zig, bLoop, ih]

theorem count_zag (q : SimplexCategoryᵒᵖ) (n : ℕ) :
    ∀ vs us, rightCount C B x b q (zag C B x b q n vs us) = n := by
  induction n with
  | zero => intro vs us; rfl
  | succ n ih => intro vs us; simp [zag, bLoop, ih]

theorem count_decodeOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) :
    rightCount C B x b q (decodeOO C B x b q a d r h) = r := by
  cases r with
  | zero => simp [decodeOO]
  | succ n => simp [decodeOO, bLoop, count_zig]

theorem count_decodeON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) :
    rightCount C B x b q (decodeON C B x b q a w r h) = r + 1 := by
  simp [decodeON, bEnd, count_zig]

theorem count_decodeNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) :
    rightCount C B x b q (decodeNO C B x b q z d r h) = r + 1 := by
  simp [decodeNO, bStart, count_zag]
  omega

theorem count_decodeNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z w r) :
    rightCount C B x b q (decodeNN C B x b q z w r h) = r + 1 := by
  cases r with
  | zero => simp [decodeNN]
  | succ n => simp [decodeNN, bStart, bEnd, count_zag]; omega

theorem count_normalize_le {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) :
    rightCount C B x b q (DaggerAmalgamNormalForms.normalize C B x b p).val ≤
      rightCount C B x b q p :=
  rightCount_reflTransGen_le C B x b
    (DaggerAmalgamNormalForms.normalForm_reduces C B x b p)

theorem rank_decodeOO_le (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) :
    rightCount C B x b q
      (DaggerAmalgamNormalForms.normalize C B x b (decodeOO C B x b q a d r h)).val ≤ r := by
  simpa only [count_decodeOO] using count_normalize_le C B x b (decodeOO C B x b q a d r h)

theorem rank_decodeON_le (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) :
    (rightCount C B x b q
      (DaggerAmalgamNormalForms.normalize C B x b (decodeON C B x b q a w r h)).val).pred ≤
        r := by
  have hle := count_normalize_le C B x b (decodeON C B x b q a w r h)
  rw [count_decodeON] at hle
  simpa only [Nat.pred_succ] using Nat.pred_le_pred hle

theorem rank_decodeNO_le (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) :
    (rightCount C B x b q
      (DaggerAmalgamNormalForms.normalize C B x b (decodeNO C B x b q z d r h)).val).pred ≤
        r := by
  have hle := count_normalize_le C B x b (decodeNO C B x b q z d r h)
  rw [count_decodeNO] at hle
  simpa only [Nat.pred_succ] using Nat.pred_le_pred hle

theorem rank_decodeNN_le (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z w r) :
    (rightCount C B x b q
      (DaggerAmalgamNormalForms.normalize C B x b (decodeNN C B x b q z w r h)).val).pred ≤
        r := by
  have hle := count_normalize_le C B x b (decodeNN C B x b q z w r h)
  rw [count_decodeNN] at hle
  simpa only [Nat.pred_succ] using Nat.pred_le_pred hle

end
end DaggerAmalgamPaddedClassifier
