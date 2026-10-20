import AmalgamPaddedCoordinateFaces

/-! Strict rank drop is equivalent to the ENTIRE critical union; cascades are allowed. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms DaggerAmalgamPathMeasure

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem criticalOO_count_lt (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) (hc : criticalOO C B x b q a d r h) :
    rightCount C B x b q (normalize C B x b (decodeOO C B x b q a d r h)).val < r := by
  cases r with
  | zero => cases hc
  | succ n =>
    rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
    · simpa only [count_decodeOO] using
        (faceOO_B C B x b q a d n h i hi).normal_count_lt C B x b
    · simpa only [count_decodeOO] using
        (faceOO_C C B x b q a d n h i hi).normal_count_lt C B x b

theorem criticalON_count_lt (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) (hc : criticalON C B x b q a w r h) :
    rightCount C B x b q (normalize C B x b (decodeON C B x b q a w r h)).val < r + 1 := by
  rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
  · simpa only [count_decodeON] using
      (faceON_B C B x b q a w r h i hi).normal_count_lt C B x b
  · simpa only [count_decodeON] using
      (faceON_C C B x b q a w r h i hi).normal_count_lt C B x b

theorem criticalNO_count_lt (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) (hc : criticalNO C B x b q z d r h) :
    rightCount C B x b q (normalize C B x b (decodeNO C B x b q z d r h)).val < r + 1 := by
  rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
  · simpa only [count_decodeNO] using
      (faceNO_C C B x b q z d r h i hi).normal_count_lt C B x b
  · simpa only [count_decodeNO] using
      (faceNO_B C B x b q z d r h i hi).normal_count_lt C B x b

theorem criticalNN_count_lt (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z w r) (hc : criticalNN C B x b q z w r h) :
    rightCount C B x b q (normalize C B x b (decodeNN C B x b q z w r h)).val < r + 1 := by
  cases r with
  | zero => cases hc
  | succ n =>
    rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
    · simpa only [count_decodeNN] using
        (faceNN_C C B x b q z w n h i hi).normal_count_lt C B x b
    · simpa only [count_decodeNN] using
        (faceNN_B C B x b q z w n h i hi).normal_count_lt C B x b

theorem criticalON_rank_lt (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) (hc : criticalON C B x b q a w r h) :
    (rightCount C B x b q (normalize C B x b (decodeON C B x b q a w r h)).val).pred <
      r := by
  cases r with
  | zero => simp [criticalON] at hc
  | succ n =>
    have hh := criticalON_count_lt C B x b q a w (n + 1) h hc
    have hle : rightCount C B x b q
        (normalize C B x b (decodeON C B x b q a w (n + 1) h)).val ≤ n + 1 := by omega
    have hp := Nat.pred_le_pred hle
    simpa only [Nat.pred_succ, Nat.lt_succ_iff] using hp

theorem criticalNO_rank_lt (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) (hc : criticalNO C B x b q z d r h) :
    (rightCount C B x b q (normalize C B x b (decodeNO C B x b q z d r h)).val).pred <
      r := by
  cases r with
  | zero => simp [criticalNO] at hc
  | succ n =>
    have hh := criticalNO_count_lt C B x b q z d (n + 1) h hc
    have hle : rightCount C B x b q
        (normalize C B x b (decodeNO C B x b q z d (n + 1) h)).val ≤ n + 1 := by omega
    have hp := Nat.pred_le_pred hle
    simpa only [Nat.pred_succ, Nat.lt_succ_iff] using hp

theorem criticalNN_rank_lt (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z w r) (hc : criticalNN C B x b q z w r h) :
    (rightCount C B x b q (normalize C B x b (decodeNN C B x b q z w r h)).val).pred <
      r := by
  cases r with
  | zero => cases hc
  | succ n =>
    have hh := criticalNN_count_lt C B x b q z w (n + 1) h hc
    have hle : rightCount C B x b q
        (normalize C B x b (decodeNN C B x b q z w (n + 1) h)).val ≤ n + 1 := by omega
    have hp := Nat.pred_le_pred hle
    simpa only [Nat.pred_succ, Nat.lt_succ_iff] using hp

theorem rank_lt_iff_criticalOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) :
    rightCount C B x b q (normalize C B x b (decodeOO C B x b q a d r h)).val < r ↔
      criticalOO C B x b q a d r h := by
  classical
  constructor
  · intro hh
    by_contra hc
    rw [count_normalize_OO C B x b q a d r h hc] at hh
    exact Nat.lt_irrefl _ hh
  · exact criticalOO_count_lt C B x b q a d r h

theorem rank_lt_iff_criticalON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj)
    (hw : w ≠ b) (r : ℕ) (h : RawON C B x b q a w r) :
    (rightCount C B x b q (normalize C B x b (decodeON C B x b q a w r h)).val).pred <
        r ↔ criticalON C B x b q a w r h := by
  classical
  constructor
  · intro hh
    by_contra hc
    rw [count_normalize_ON C B x b q a w hw r h hc, Nat.pred_succ] at hh
    exact Nat.lt_irrefl _ hh
  · exact criticalON_rank_lt C B x b q a w r h

theorem rank_lt_iff_criticalNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b)
    (d : C.Obj) (r : ℕ) (h : RawNO C B x b q z d r) :
    (rightCount C B x b q (normalize C B x b (decodeNO C B x b q z d r h)).val).pred <
        r ↔ criticalNO C B x b q z d r h := by
  classical
  constructor
  · intro hh
    by_contra hc
    rw [count_normalize_NO C B x b q z hz d r h hc, Nat.pred_succ] at hh
    exact Nat.lt_irrefl _ hh
  · exact criticalNO_rank_lt C B x b q z d r h

theorem rank_lt_iff_criticalNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj)
    (hz : z ≠ b) (hw : w ≠ b) (r : ℕ) (h : RawNN C B x b q z w r) :
    (rightCount C B x b q (normalize C B x b (decodeNN C B x b q z w r h)).val).pred <
        r ↔ criticalNN C B x b q z w r h := by
  classical
  constructor
  · intro hh
    by_contra hc
    rw [predCount_normalize_NN C B x b q z w hz hw r h hc] at hh
    exact Nat.lt_irrefl _ hh
  · exact criticalNN_rank_lt C B x b q z w r h

end
end DaggerAmalgamPaddedClassifier
