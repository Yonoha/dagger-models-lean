import AmalgamPaddedInteriorEncoding

/-! Exact normal-form ranks, not only upper bounds, on each full original interior. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms DaggerAmalgamPathMeasure

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def bCount {q : SimplexCategoryᵒᵖ} : List (Edge C B q) → ℕ
  | [] => 0
  | e :: l => (if e.1 then 1 else 0) + bCount l

theorem bCount_encode {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) : bCount C B (encode C B x b p) = rightCount C B x b q p := by
  induction p with
  | nil => rfl
  | cons p e ih => simpa only [encode, bCount, rightCount, ih] using Nat.add_comm _ _

theorem bCount_append {q : SimplexCategoryᵒᵖ} (l l' : List (Edge C B q)) :
    bCount C B (l ++ l') = bCount C B l + bCount C B l' := by
  induction l with
  | nil => simp [bCount]
  | cons e l ih => simp only [List.cons_append, bCount, ih, Nat.add_assoc]

theorem bCount_trimmed_C {q : SimplexCategoryᵒᵖ} {a d : C.Obj}
    (h : (a ⟶[SSet] d).obj q) : bCount C B (trimmedTag C B q false h) = 0 := by
  classical
  by_cases hi : IsIdentity C B q (tag C B q false h)
  · simp only [trimmedTag, if_pos hi, bCount]
  · simp only [trimmedTag, if_neg hi]
    simp [bCount, tag]

theorem count_normalize_OO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) (hi : ¬ criticalOO C B x b q a d r h) :
    rightCount C B x b q (normalize C B x b (decodeOO C B x b q a d r h)).val = r := by
  rw [← bCount_encode]
  cases r with
  | zero =>
    dsimp only [decodeOO]
    rw [normalize_factor_encode]
    exact bCount_trimmed_C C B h
  | succ n =>
    rw [normalize_decodeOO_encode C B x b q a d n h hi]
    simp only [bCount_append, bCount_trimmed_C, bCount, tag, if_true,
      bCount_encode, count_zig, Nat.zero_add, Nat.add_zero]
    omega

theorem count_normalize_ON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj)
    (hw : w ≠ b) (r : ℕ) (h : RawON C B x b q a w r)
    (hi : ¬ criticalON C B x b q a w r h) :
    rightCount C B x b q (normalize C B x b (decodeON C B x b q a w r h)).val = r + 1 := by
  rw [← bCount_encode, normalize_decodeON_encode C B x b q a w hw r h hi]
  simp only [bCount, tag, if_true, bCount_append, bCount_trimmed_C,
    bCount_encode, count_zig, Nat.add_zero, Nat.add_comm]

theorem count_normalize_NO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b)
    (d : C.Obj) (r : ℕ) (h : RawNO C B x b q z d r)
    (hi : ¬ criticalNO C B x b q z d r h) :
    rightCount C B x b q (normalize C B x b (decodeNO C B x b q z d r h)).val = r + 1 := by
  rw [← bCount_encode, normalize_decodeNO_encode C B x b q z hz d r h hi]
  simp only [bCount_append, bCount_trimmed_C, bCount_encode, count_zag, bCount,
    tag, if_true, Nat.add_zero, Nat.zero_add]

theorem predCount_normalize_NN (q : SimplexCategoryᵒᵖ) (z w : B.Obj)
    (hz : z ≠ b) (hw : w ≠ b) (r : ℕ) (h : RawNN C B x b q z w r)
    (hi : ¬ criticalNN C B x b q z w r h) :
    (rightCount C B x b q (normalize C B x b (decodeNN C B x b q z w r h)).val).pred = r := by
  classical
  cases r with
  | zero =>
    rw [← bCount_encode]
    dsimp only [decodeNN]
    rw [normalize_factor_encode]
    by_cases hh : IsIdentity C B q (tag C B q true h)
    · simp only [trimmedTag, if_pos hh, bCount, Nat.pred_zero]
    · simp only [trimmedTag, if_neg hh]
      simp [bCount, tag]
  | succ n =>
    rw [← bCount_encode, normalize_decodeNN_encode C B x b q z w hz hw n h hi,
      bCount_encode, count_decodeNN, Nat.pred_succ]

end
end DaggerAmalgamPaddedClassifier
