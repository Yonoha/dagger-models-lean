import OriginalFlagBeadNormalizationLaws
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable (T : NecklaceCode)

/-- The number of positive original beads, not the dimension of their images in X. -/
def beadCount : ℕ := T.joints.card - 1

theorem joints_card : T.joints.card = beadCount T + 1 := by
  have h := Finset.card_pos.mpr ⟨0, T.first_mem⟩
  dsimp [beadCount]
  omega

def jointOrderIso : Fin (beadCount T + 1) ≃o T.joints :=
  T.joints.orderIsoOfFin (joints_card T)

def jointEmbedding : Fin (beadCount T + 1) ↪o Fin (T.len + 1) :=
  T.joints.orderEmbOfFin (joints_card T)

theorem jointEmbedding_mem (i : Fin (beadCount T + 1)) :
    jointEmbedding T i ∈ T.joints :=
  Finset.orderEmbOfFin_mem T.joints (joints_card T) i

theorem jointEmbedding_first : jointEmbedding T 0 = 0 := by
  have h := Finset.orderEmbOfFin_zero (joints_card T) (Nat.succ_pos _)
  have hz : jointEmbedding T 0 = T.joints.min' ⟨0, T.first_mem⟩ := by
    simpa only [jointEmbedding, Fin.mk_zero] using h
  rw [hz]
  exact le_antisymm (T.joints.min'_le 0 T.first_mem) (Fin.zero_le _)

theorem jointEmbedding_last :
    jointEmbedding T (Fin.last (beadCount T)) = Fin.last T.len := by
  have h := Finset.orderEmbOfFin_last (joints_card T) (Nat.succ_pos (beadCount T))
  change jointEmbedding T (Fin.last (beadCount T)) = _ at h
  rw [h]
  exact le_antisymm (Fin.le_last _) (T.joints.le_max' _ T.last_mem)

def jointIndex (v : Fin (T.len + 1)) (hv : v ∈ T.joints) :
    Fin (beadCount T + 1) := (jointOrderIso T).symm ⟨v, hv⟩

theorem jointEmbedding_jointIndex (v : Fin (T.len + 1)) (hv : v ∈ T.joints) :
    jointEmbedding T (jointIndex T v hv) = v :=
  congrArg Subtype.val ((jointOrderIso T).apply_symm_apply ⟨v, hv⟩)

/-- Beads are listed in the SAME original joint order, with both original endpoints. -/
def jointBead (i : Fin (beadCount T)) : T.Bead where
  left := jointEmbedding T i.castSucc
  right := jointEmbedding T i.succ
  left_mem := jointEmbedding_mem T i.castSucc
  right_mem := jointEmbedding_mem T i.succ
  lt := (jointEmbedding T).strictMono (Fin.castSucc_lt_succ (i := i))
  no_joint v hv hl hr := by
    let k := jointIndex T v hv
    have hk := jointEmbedding_jointIndex T v hv
    rw [← hk] at hl hr
    have hl' := (jointEmbedding T).lt_iff_lt.mp hl
    have hr' := (jointEmbedding T).lt_iff_lt.mp hr
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hl' hr'
    omega

theorem bead_left_index_lt (c : T.Bead) :
    (jointIndex T c.left c.left_mem).val < beadCount T := by
  have hc : jointIndex T c.left c.left_mem < jointIndex T c.right c.right_mem := by
    apply (jointEmbedding T).lt_iff_lt.mp
    simpa only [jointEmbedding_jointIndex] using c.lt
  have h := (jointIndex T c.right c.right_mem).isLt
  simp only [Fin.lt_def] at hc
  omega

def beadIndex (c : T.Bead) : Fin (beadCount T) :=
  ⟨(jointIndex T c.left c.left_mem).val, bead_left_index_lt T c⟩

theorem jointBead_left (c : T.Bead) : (jointBead T (beadIndex T c)).left = c.left := by
  change jointEmbedding T (beadIndex T c).castSucc = c.left
  convert jointEmbedding_jointIndex T c.left c.left_mem using 1

theorem bead_right_index (c : T.Bead) :
    jointIndex T c.right c.right_mem = (beadIndex T c).succ := by
  have hlt : jointIndex T c.left c.left_mem < jointIndex T c.right c.right_mem := by
    apply (jointEmbedding T).lt_iff_lt.mp
    simpa only [jointEmbedding_jointIndex] using c.lt
  have hle : (beadIndex T c).succ ≤ jointIndex T c.right c.right_mem := by
    simp only [Fin.le_def, Fin.val_succ, beadIndex]
    simp only [Fin.lt_def] at hlt
    omega
  apply le_antisymm
  · by_contra hn
    have hi := lt_of_not_ge hn
    have hleft : c.left < jointEmbedding T (beadIndex T c).succ := by
      rw [← jointBead_left T c]
      exact (jointBead T (beadIndex T c)).lt
    have hright : jointEmbedding T (beadIndex T c).succ < c.right := by
      rw [← jointEmbedding_jointIndex T c.right c.right_mem]
      exact (jointEmbedding T).strictMono hi
    exact c.no_joint _ (jointEmbedding_mem T _) hleft hright
  · exact hle

theorem jointBead_right (c : T.Bead) : (jointBead T (beadIndex T c)).right = c.right := by
  change jointEmbedding T (beadIndex T c).succ = c.right
  rw [← bead_right_index T c, jointEmbedding_jointIndex]

theorem bead_eq_of_endpoints {c d : T.Bead} (hl : c.left = d.left)
    (hr : c.right = d.right) : c = d := by
  cases c
  cases d
  cases hl
  cases hr
  rfl

theorem jointBead_beadIndex (c : T.Bead) : jointBead T (beadIndex T c) = c :=
  bead_eq_of_endpoints T (jointBead_left T c) (jointBead_right T c)

theorem beadIndex_jointBead (i : Fin (beadCount T)) : beadIndex T (jointBead T i) = i := by
  apply Fin.ext
  have h := (jointOrderIso T).symm_apply_apply (i.castSucc)
  change ((jointOrderIso T).symm ((jointOrderIso T) i.castSucc)).val = i.val
  exact congrArg (fun v : Fin (beadCount T + 1) ↦ v.val) h

def jointBeadEquiv : Fin (beadCount T) ≃ T.Bead where
  toFun := jointBead T
  invFun := beadIndex T
  left_inv := beadIndex_jointBead T
  right_inv := jointBead_beadIndex T

theorem jointBead_length (i : Fin (beadCount T)) :
    (jointBead T i).length = (jointEmbedding T i.succ).val -
      (jointEmbedding T i.castSucc).val := by
  have h := (jointBead T i).lt
  simp only [Bead.length, Bead.interval, Fin.card_Icc, jointBead]
  simp only [Fin.lt_def] at h
  omega

theorem beadCount_zero_iff : beadCount T = 0 ↔ T.len = 0 := by
  constructor
  · intro h
    have hz : (0 : Fin (beadCount T + 1)) = Fin.last (beadCount T) := by
      apply Fin.ext
      simp [h]
    have hv := congrArg (jointEmbedding T) hz
    rw [jointEmbedding_first, jointEmbedding_last] at hv
    exact (congrArg Fin.val hv).symm
  · intro h
    have hs : T.joints = {0} := by
      ext v
      have hv : v = 0 := by
        apply Fin.ext
        have hi := v.isLt
        simp [h] at hi
        omega
      simp [hv, T.first_mem]
    simp [beadCount, hs]

end

end DaggerOriginalFlagFlankification
