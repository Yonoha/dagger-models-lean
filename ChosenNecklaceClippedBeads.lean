import ChosenNecklaceIntervalCode

open CategoryTheory Limits Opposite Simplicial

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode) (a b : Fin (T.len + 1)) (hab : a ≤ b) (d : T.Bead)
variable (hd : max a d.left < min b d.right)

def clippedLeft : Fin (b.val - a.val + 1) :=
  ⟨(max a d.left).val - a.val, by
    have h : (max a d.left).val < (min b d.right).val := hd
    have hb : (min b d.right).val ≤ b.val := min_le_left _ _
    omega⟩

def clippedRight : Fin (b.val - a.val + 1) :=
  ⟨(min b d.right).val - a.val, by
    have h : (min b d.right).val ≤ b.val := min_le_left _ _
    omega⟩

theorem clippedLeft_embedding :
    intervalEmbedding T a b hab (clippedLeft T a b hab d hd) = max a d.left := by
  apply Fin.ext
  change a.val + ((max a d.left).val - a.val) = (max a d.left).val
  have h : a.val ≤ (max a d.left).val := le_max_left _ _
  omega

include hd in
theorem clippedRight_embedding :
    intervalEmbedding T a b hab (clippedRight T a b hab d) = min b d.right := by
  apply Fin.ext
  change a.val + ((min b d.right).val - a.val) = (min b d.right).val
  have h : (max a d.left).val < (min b d.right).val := hd
  have hl : a.val ≤ (max a d.left).val := le_max_left _ _
  omega

def clippedBead : (intervalCode T a b hab).Bead where
  left := clippedLeft T a b hab d hd
  right := clippedRight T a b hab d
  left_mem := by
    apply (intervalCode_joint T a b hab _).mpr
    by_cases hl : d.left ≤ a
    · left
      apply Fin.ext
      dsimp [clippedLeft]
      have hl' : d.left.val ≤ a.val := hl
      rw [max_eq_left hl']
      omega
    · right
      right
      rw [clippedLeft_embedding, max_eq_right (le_of_not_ge hl)]
      exact d.left_mem
  right_mem := by
    apply (intervalCode_joint T a b hab _).mpr
    by_cases hr : b ≤ d.right
    · right
      left
      apply Fin.ext
      dsimp [clippedRight]
      have hr' : b.val ≤ d.right.val := hr
      rw [min_eq_left hr']
    · right
      right
      rw [clippedRight_embedding T a b hab d hd, min_eq_right (le_of_not_ge hr)]
      exact d.right_mem
  lt := by
    have h : (max a d.left).val < (min b d.right).val := hd
    have hl : a.val ≤ (max a d.left).val := le_max_left _ _
    change (max a d.left).val - a.val < (min b d.right).val - a.val
    omega
  no_joint k hk hl hr := by
    rcases (intervalCode_joint T a b hab k).mp hk with he | he | hj
    · subst k
      exact (not_lt_of_ge (Fin.zero_le _)) hl
    · subst k
      exact (not_lt_of_ge (Fin.le_last _)) hr
    · apply d.no_joint (intervalEmbedding T a b hab k) hj
      · have h := (intervalEmbedding T a b hab).strictMono hl
        rw [clippedLeft_embedding] at h
        exact (le_max_right _ _).trans_lt h
      · have h := (intervalEmbedding T a b hab).strictMono hr
        rw [clippedRight_embedding T a b hab d hd] at h
        exact h.trans_le (min_le_right _ _)

theorem clippedBead_preimage (v : Fin ((intervalCode T a b hab).len + 1))
    (hv : intervalEmbedding T a b hab v ∈ d.interval) :
    v ∈ (clippedBead T a b hab d hd).interval := by
  obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
  obtain ⟨hva, hvb⟩ := intervalEmbedding_bounds T a b hab v
  apply Finset.mem_Icc.mpr
  constructor
  · apply (intervalEmbedding T a b hab).le_iff_le.mp
    change intervalEmbedding T a b hab (clippedLeft T a b hab d hd) ≤ _
    rw [clippedLeft_embedding]
    exact max_le hva hl
  · apply (intervalEmbedding T a b hab).le_iff_le.mp
    change _ ≤ intervalEmbedding T a b hab (clippedRight T a b hab d)
    rw [clippedRight_embedding T a b hab d hd]
    exact le_min hvb hr

end

end DaggerChosenRigidificationNecklace.NecklaceCode
