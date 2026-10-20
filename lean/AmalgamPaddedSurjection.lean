import AmalgamPaddedPadInterior
import AmalgamPaddedCritical
import AmalgamPaddedUnpadInjection

/-! Complete all-rank surjectivity from actual normal paths to the four original interiors.
The chosen tuple decodes to the literal canonically padded original path. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms DaggerAmalgamPathMeasure

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def criticalFamily (q : SimplexCategoryᵒᵖ) : (c d : Bool) →
    (a : At C B q c) → (z : At C B q d) → (r : ℕ) → RawFamily C B x b q c d a z r → Prop
  | false, false => criticalOO C B x b q
  | false, true => criticalON C B x b q
  | true, false => criticalNO C B x b q
  | true, true => criticalNN C B x b q

abbrev InteriorFamily (q : SimplexCategoryᵒᵖ) (c d : Bool)
    (a : At C B q c) (z : At C B q d) (r : ℕ) :=
  {h : RawFamily C B x b q c d a z r // ¬ criticalFamily C B x b q c d a z r h}

theorem middleFree_family_iff (q : SimplexCategoryᵒᵖ) (c d : Bool)
    (a : At C B q c) (z : At C B q d) (r : ℕ) (h : RawFamily C B x b q c d a z r) :
    MiddleFree C B (encode C B x b (decodeFamily C B x b q c d a z r h)) ↔
      ¬ criticalFamily C B x b q c d a z r h := by
  cases c <;> cases d
  · exact middleFree_decodeOO_iff C B x b q a z r h
  · exact middleFree_decodeON_iff C B x b q a z r h
  · exact middleFree_decodeNO_iff C B x b q a z r h
  · exact middleFree_decodeNN_iff C B x b q a z r h

theorem exists_interior_normal (q : SimplexCategoryᵒᵖ) (c d : Bool)
    (a : At C B q c) (z : At C B q d)
    (p : NormalPath C B x b q (label C B x b c a) (label C B x b d z)) :
    ∃ (r : ℕ) (h : InteriorFamily C B x b q c d a z r),
      decodeFamily C B x b q c d a z r h.val = padPath C B x b c d a z p.val ∧
        normalize C B x b (decodeFamily C B x b q c d a z r h.val) = p := by
  have hs := padPath_starts_ends C B x b c d a z p.val
  obtain ⟨r, h, he⟩ := exists_raw_path C B x b c d a z (padPath C B x b c d a z p.val)
    (padPath_alternating C B x b c d a z p.val (normal_alternating C B x b p.property))
    hs.1 hs.2
  have hi : ¬ criticalFamily C B x b q c d a z r h := by
    apply (middleFree_family_iff C B x b q c d a z r h).1
    rw [he]
    exact middleFree_padPath C B x b c d a z p.val (normal_identityFree C B x b p.property)
  refine ⟨r, ⟨h, hi⟩, he, ?_⟩
  rw [he]
  exact (normalize_padPath C B x b c d a z p.val).trans (normalize_of_normal C B x b p)

theorem exists_interior_OO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (p : NormalPath C B x b q (leftObj C B x b a) (leftObj C B x b d))
    (hr : rightCount C B x b q p.val = r) :
    ∃ h : InteriorOO C B x b q a d r,
      decodeOO C B x b q a d r h.val = padPath C B x b false false a d p.val ∧
        unpadOO C B x b q a d r h = p := by
  obtain ⟨r', h, hp, hn⟩ := exists_interior_normal C B x b q false false a d p
  have hc := congrArg (rightCount C B x b q) hp
  change rightCount C B x b q (decodeOO C B x b q a d r' h.val) = _ at hc
  rw [count_decodeOO, count_padPath_OO, hr] at hc
  cases hc
  exact ⟨h, hp, hn⟩

theorem exists_interior_ON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b)
    (r : ℕ) (p : NormalPath C B x b q (leftObj C B x b a) (rightObj C B x b w))
    (hr : (rightCount C B x b q p.val).pred = r) :
    ∃ h : InteriorON C B x b q a w r,
      decodeON C B x b q a w r h.val = padPath C B x b false true a w p.val ∧
        unpadON C B x b q a w r h = p := by
  obtain ⟨r', h, hp, hn⟩ := exists_interior_normal C B x b q false true a w p
  have hc := congrArg (rightCount C B x b q) hp
  change rightCount C B x b q (decodeON C B x b q a w r' h.val) = _ at hc
  rw [count_decodeON, count_padPath_ON C B x b a w hw] at hc
  have hpred : r' = r := by simpa only [Nat.pred_succ, hr] using congrArg Nat.pred hc
  cases hpred
  exact ⟨h, hp, hn⟩

theorem exists_interior_NO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b) (d : C.Obj)
    (r : ℕ) (p : NormalPath C B x b q (rightObj C B x b z) (leftObj C B x b d))
    (hr : (rightCount C B x b q p.val).pred = r) :
    ∃ h : InteriorNO C B x b q z d r,
      decodeNO C B x b q z d r h.val = padPath C B x b true false z d p.val ∧
        unpadNO C B x b q z d r h = p := by
  obtain ⟨r', h, hp, hn⟩ := exists_interior_normal C B x b q true false z d p
  have hc := congrArg (rightCount C B x b q) hp
  change rightCount C B x b q (decodeNO C B x b q z d r' h.val) = _ at hc
  rw [count_decodeNO, count_padPath_NO C B x b z hz d] at hc
  have hpred : r' = r := by simpa only [Nat.pred_succ, hr] using congrArg Nat.pred hc
  cases hpred
  exact ⟨h, hp, hn⟩

theorem exists_interior_NN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b)
    (r : ℕ) (p : NormalPath C B x b q (rightObj C B x b z) (rightObj C B x b w))
    (hr : (rightCount C B x b q p.val).pred = r) :
    ∃ h : InteriorNN C B x b q z w r,
      decodeNN C B x b q z w r h.val = padPath C B x b true true z w p.val ∧
        unpadNN C B x b q z w r h = p := by
  obtain ⟨r', h, hp, hn⟩ := exists_interior_normal C B x b q true true z w p
  have hc := congrArg (fun v ↦ (rightCount C B x b q v).pred) hp
  dsimp only at hc
  change (rightCount C B x b q (decodeNN C B x b q z w r' h.val)).pred = _ at hc
  rw [count_decodeNN, Nat.pred_succ, predCount_padPath_NN C B x b z w hz hw, hr] at hc
  cases hc
  exact ⟨h, hp, hn⟩

end
end DaggerAmalgamPaddedClassifier
