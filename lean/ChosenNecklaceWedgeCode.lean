import ChosenNecklaceCode

open CategoryTheory

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T U : NecklaceCode)

def wedgeLeft : Fin (T.len + 1) ↪o Fin (T.len + U.len + 1) where
  toFun i := ⟨i.val, by have hi := i.isLt; omega⟩
  inj' i j h := Fin.ext (congrArg (fun v : Fin (T.len + U.len + 1) ↦ v.val) h)
  map_rel_iff' := by intro i j; rfl

def wedgeRight : Fin (U.len + 1) ↪o Fin (T.len + U.len + 1) where
  toFun i := ⟨T.len + i.val, by have hi := i.isLt; omega⟩
  inj' i j h := Fin.ext (by have hh := congrArg Fin.val h; dsimp at hh; omega)
  map_rel_iff' := by intro i j; change T.len + i.val ≤ T.len + j.val ↔ i.val ≤ j.val; omega

def wedge : NecklaceCode where
  len := T.len + U.len
  joints := T.joints.image (wedgeLeft T U) ∪ U.joints.image (wedgeRight T U)
  first_mem := by
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨0, T.first_mem, Fin.ext rfl⟩
  last_mem := by
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨Fin.last U.len, U.last_mem, Fin.ext rfl⟩

theorem wedgeLeft_first : wedgeLeft T U 0 = (0 : Fin ((wedge T U).len + 1)) := Fin.ext rfl

theorem wedgeRight_last :
    wedgeRight T U (Fin.last U.len) = Fin.last (wedge T U).len := Fin.ext rfl

theorem wedge_joint : wedgeLeft T U (Fin.last T.len) = wedgeRight T U 0 := Fin.ext rfl

def wedgeLeftBead (b : T.Bead) : (wedge T U).Bead where
  left := wedgeLeft T U b.left
  right := wedgeLeft T U b.right
  left_mem := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b.left, b.left_mem, rfl⟩)
  right_mem := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b.right, b.right_mem, rfl⟩)
  lt := (wedgeLeft T U).strictMono b.lt
  no_joint v hv hl hr := by
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      exact b.no_joint k hk ((wedgeLeft T U).lt_iff_lt.mp hl)
        ((wedgeLeft T U).lt_iff_lt.mp hr)
    · obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp h
      have hb := b.right.isLt
      change T.len + k.val < b.right.val at hr
      omega

def wedgeRightBead (b : U.Bead) : (wedge T U).Bead where
  left := wedgeRight T U b.left
  right := wedgeRight T U b.right
  left_mem := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b.left, b.left_mem, rfl⟩)
  right_mem := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b.right, b.right_mem, rfl⟩)
  lt := (wedgeRight T U).strictMono b.lt
  no_joint v hv hl hr := by
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp h
      have hk := k.isLt
      change T.len + b.left.val < k.val at hl
      omega
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      exact b.no_joint k hk ((wedgeRight T U).lt_iff_lt.mp hl)
        ((wedgeRight T U).lt_iff_lt.mp hr)

theorem wedgeLeftBead_interval (b : T.Bead) (v : Fin (T.len + 1))
    (hv : v ∈ b.interval) : wedgeLeft T U v ∈ (wedgeLeftBead T U b).interval := by
  obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
  exact Finset.mem_Icc.mpr ⟨(wedgeLeft T U).monotone hl, (wedgeLeft T U).monotone hr⟩

theorem wedgeRightBead_interval (b : U.Bead) (v : Fin (U.len + 1))
    (hv : v ∈ b.interval) : wedgeRight T U v ∈ (wedgeRightBead T U b).interval := by
  obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
  exact Finset.mem_Icc.mpr ⟨(wedgeRight T U).monotone hl, (wedgeRight T U).monotone hr⟩

end

end DaggerChosenRigidificationNecklace.NecklaceCode
