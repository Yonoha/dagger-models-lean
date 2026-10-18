import ChosenNecklaceOrderLift

open CategoryTheory Limits Opposite Simplicial

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode) (a b : Fin (T.len + 1)) (hab : a ≤ b)

def intervalEmbedding : Fin (b.val - a.val + 1) ↪o Fin (T.len + 1) where
  toFun i := ⟨a.val + i.val, by have hi := i.isLt; have hb := b.isLt; omega⟩
  inj' i j h := Fin.ext (by have hh := congrArg Fin.val h; dsimp at hh; omega)
  map_rel_iff' := by intro i j; change a.val + i.val ≤ a.val + j.val ↔ i.val ≤ j.val; omega

def intervalCode : NecklaceCode where
  len := b.val - a.val
  joints := {0, Fin.last (b.val - a.val)} ∪
    Finset.univ.filter (fun v ↦ intervalEmbedding T a b hab v ∈ T.joints)
  first_mem := Finset.mem_union_left _ (by simp)
  last_mem := Finset.mem_union_left _ (by simp)

theorem intervalEmbedding_first : intervalEmbedding T a b hab 0 = a := by
  apply Fin.ext
  change a.val + 0 = a.val
  omega

theorem intervalEmbedding_last :
    intervalEmbedding T a b hab (Fin.last (b.val - a.val)) = b := by
  apply Fin.ext
  change a.val + (b.val - a.val) = b.val
  have h : a.val ≤ b.val := hab
  omega

theorem intervalEmbedding_bounds (v : Fin ((intervalCode T a b hab).len + 1)) :
    a ≤ intervalEmbedding T a b hab v ∧ intervalEmbedding T a b hab v ≤ b := by
  constructor
  · change a.val ≤ a.val + v.val
    omega
  · have h := v.isLt
    have hh : a.val ≤ b.val := hab
    change v.val < b.val - a.val + 1 at h
    change a.val + v.val ≤ b.val
    omega

theorem intervalCode_joint (v : Fin ((intervalCode T a b hab).len + 1)) :
    v ∈ (intervalCode T a b hab).joints ↔
      v = 0 ∨ v = Fin.last (b.val - a.val) ∨ intervalEmbedding T a b hab v ∈ T.joints := by
  simp only [intervalCode, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_filter, Finset.mem_univ, true_and, or_assoc]

theorem intervalEmbedding_preimage (v : Fin (T.len + 1)) (ha : a ≤ v) (hb : v ≤ b) :
    ∃ w, intervalEmbedding T a b hab w = v := by
  refine ⟨⟨v.val - a.val, by
    have hh : v.val ≤ b.val := hb
    change v.val - a.val < b.val - a.val + 1
    omega⟩, ?_⟩
  apply Fin.ext
  change a.val + (v.val - a.val) = v.val
  have hh : a.val ≤ v.val := ha
  omega

/-- Cutting first/last beads retains every interior original joint and no artificial bead. -/
theorem interval_image :
    BeadImageCondition (T := intervalCode T a b hab) (U := T)
      (intervalEmbedding T a b hab).toOrderHom := by
  intro c
  have hp : (0 : Fin (T.len + 1)) < intervalEmbedding T a b hab c.right := by
    have h : c.left.val < c.right.val := c.lt
    change 0 < a.val + c.right.val
    omega
  obtain ⟨d, hd, hr⟩ := T.exists_bead_at (intervalEmbedding T a b hab c.right) hp
  have hl : d.left ≤ intervalEmbedding T a b hab c.left := by
    by_contra hn
    have hn' : intervalEmbedding T a b hab c.left < d.left := lt_of_not_ge hn
    obtain ⟨w, hw⟩ := intervalEmbedding_preimage T a b hab d.left
      ((intervalEmbedding_bounds T a b hab c.left).1.trans hn'.le)
      (hd.le.trans (intervalEmbedding_bounds T a b hab c.right).2)
    have hj : w ∈ (intervalCode T a b hab).joints := by
      apply (intervalCode_joint T a b hab w).mpr
      exact Or.inr (Or.inr (hw.symm ▸ d.left_mem))
    apply c.no_joint w hj
    · exact (intervalEmbedding T a b hab).lt_iff_lt.mp (hw.symm ▸ hn')
    · exact (intervalEmbedding T a b hab).lt_iff_lt.mp (hw.symm ▸ hd)
  left
  refine ⟨d, fun v hv ↦ ?_⟩
  obtain ⟨hvl, hvr⟩ := Finset.mem_Icc.mp hv
  exact Finset.mem_Icc.mpr ⟨hl.trans ((intervalEmbedding T a b hab).monotone hvl),
    ((intervalEmbedding T a b hab).monotone hvr).trans hr⟩

end

end DaggerChosenRigidificationNecklace.NecklaceCode
