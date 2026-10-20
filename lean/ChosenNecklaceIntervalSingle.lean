import ChosenNecklaceIntervalMaps
import ChosenNecklaceSingleBead

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

theorem code_ext {T U : NecklaceCode} (h : T.len = U.len) (hj : HEq T.joints U.joints) : T = U := by
  cases T
  cases U
  dsimp only at h
  cases h
  have he := eq_of_heq hj
  cases he
  rfl

/-- A zero-length original code is the literal point code, with no missing bead choice. -/
theorem code_eq_point_of_zero (T : NecklaceCode) (h : T.len = 0) : T = point := by
  apply code_ext h
  cases T with | mk n J h0 hn
  dsimp only at h
  subst n
  apply heq_of_eq
  change J = {0}
  ext v
  have hv : v = (0 : Fin 1) := by
    apply Fin.ext
    have hlt := v.isLt
    change v.val < 1 at hlt
    change v.val = 0
    omega
  subst v
  exact ⟨fun _ ↦ by simp, fun _ ↦ h0⟩

theorem intervalCode_diagonal (T : NecklaceCode) (a : Fin (T.len + 1)) :
    intervalCode T a a le_rfl = point :=
  code_eq_point_of_zero _ (Nat.sub_self _)

/-- Cutting any two ordered vertices of a single bead retains that same single-bead code. -/
theorem intervalCode_single (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) :
    intervalCode (single n) a b hab = single (b.val - a.val) := by
  apply code_ext (T := intervalCode (single n) a b hab)
    (U := single (b.val - a.val)) rfl
  apply heq_of_eq
  ext k
  constructor
  · intro hk
    rcases (intervalCode_joint (single n) a b hab k).mp hk with h | h | h
    · exact (mem_single_joints _ k).mpr (Or.inl h)
    · exact (mem_single_joints _ k).mpr (Or.inr h)
    · rcases (mem_single_joints n _).mp h with h | h
      · apply (mem_single_joints _ k).mpr
        left
        apply Fin.ext
        have he := congrArg Fin.val h
        change a.val + k.val = 0 at he
        change k.val = 0
        omega
      · apply (mem_single_joints _ k).mpr
        right
        apply Fin.ext
        have he := congrArg Fin.val h
        change a.val + k.val = n at he
        have hk := k.isLt
        have hb := b.isLt
        change k.val < b.val - a.val + 1 at hk
        change k.val = b.val - a.val
        omega
  · intro hk
    rcases (mem_single_joints _ k).mp hk with h | h
    · exact (intervalCode_joint (single n) a b hab k).mpr (Or.inl h)
    · exact (intervalCode_joint (single n) a b hab k).mpr (Or.inr (Or.inl h))

end

end DaggerChosenRigidificationNecklace.NecklaceCode
