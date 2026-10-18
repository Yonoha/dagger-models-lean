import ChosenNecklaceWedgeCode
import ChosenNecklaceIntersections

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T U : NecklaceCode)

def wedgeLeftDown (v : Fin ((wedge T U).len + 1)) (hv : v.val ≤ T.len) :
    Fin (T.len + 1) := ⟨v.val, by omega⟩

def wedgeRightDown (v : Fin ((wedge T U).len + 1)) (hv : T.len ≤ v.val) :
    Fin (U.len + 1) := ⟨v.val - T.len, by have h := v.isLt; dsimp [wedge] at h; omega⟩

theorem wedgeLeftDown_joint (v : Fin ((wedge T U).len + 1))
    (hv : v.val ≤ T.len) (hj : v ∈ (wedge T U).joints) :
    wedgeLeftDown T U v hv ∈ T.joints := by
  rcases Finset.mem_union.mp hj with h | h
  · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
    have e : wedgeLeftDown T U v hv = k := Fin.ext (congrArg Fin.val he).symm
    exact e.symm ▸ hk
  · obtain ⟨k, _hk, he⟩ := Finset.mem_image.mp h
    have ee := congrArg Fin.val he
    change T.len + k.val = v.val at ee
    have e : wedgeLeftDown T U v hv = Fin.last T.len := Fin.ext (by
      change v.val = T.len
      omega)
    exact e.symm ▸ T.last_mem

theorem wedgeRightDown_joint (v : Fin ((wedge T U).len + 1))
    (hv : T.len ≤ v.val) (hj : v ∈ (wedge T U).joints) :
    wedgeRightDown T U v hv ∈ U.joints := by
  rcases Finset.mem_union.mp hj with h | h
  · obtain ⟨k, _hk, he⟩ := Finset.mem_image.mp h
    have ee := congrArg Fin.val he
    change k.val = v.val at ee
    have hk := k.isLt
    have e : wedgeRightDown T U v hv = 0 := Fin.ext (by
      change v.val - T.len = 0
      omega)
    exact e.symm ▸ U.first_mem
  · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
    have ee := congrArg Fin.val he
    change T.len + k.val = v.val at ee
    have e : wedgeRightDown T U v hv = k := Fin.ext (by
      change v.val - T.len = k.val
      omega)
    exact e.symm ▸ hk

def leftDownBead (b : (wedge T U).Bead) (hb : b.right.val ≤ T.len) : T.Bead where
  left := wedgeLeftDown T U b.left
    ((show b.left.val ≤ b.right.val from b.lt.le).trans hb)
  right := wedgeLeftDown T U b.right hb
  left_mem := wedgeLeftDown_joint T U b.left _ b.left_mem
  right_mem := wedgeLeftDown_joint T U b.right hb b.right_mem
  lt := b.lt
  no_joint k hk hl hr :=
    b.no_joint (wedgeLeft T U k)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)) hl hr

def rightDownBead (b : (wedge T U).Bead) (hb : T.len ≤ b.left.val) : U.Bead where
  left := wedgeRightDown T U b.left hb
  right := wedgeRightDown T U b.right (hb.trans b.lt.le)
  left_mem := wedgeRightDown_joint T U b.left hb b.left_mem
  right_mem := wedgeRightDown_joint T U b.right _ b.right_mem
  lt := by
    have h : b.left.val < b.right.val := b.lt
    change b.left.val - T.len < b.right.val - T.len
    omega
  no_joint k hk hl hr := by
    apply b.no_joint (wedgeRight T U k)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩))
    · have h := b.lt
      change b.left.val - T.len < k.val at hl
      change b.left.val < T.len + k.val
      omega
    · change k.val < b.right.val - T.len at hr
      change T.len + k.val < b.right.val
      omega

theorem wedgeLeft_leftDown (b : (wedge T U).Bead) (hb : b.right.val ≤ T.len) :
    wedgeLeftBead T U (leftDownBead T U b hb) = b :=
  Bead.ext_endpoints _ _ (Fin.ext rfl) (Fin.ext rfl)

theorem wedgeRight_rightDown (b : (wedge T U).Bead) (hb : T.len ≤ b.left.val) :
    wedgeRightBead T U (rightDownBead T U b hb) = b := by
  apply Bead.ext_endpoints
  · apply Fin.ext
    dsimp [wedgeRightBead, rightDownBead, wedgeRightDown, wedgeRight]
    omega
  · apply Fin.ext
    have h := b.lt
    change b.left.val < b.right.val at h
    dsimp [wedgeRightBead, rightDownBead, wedgeRightDown, wedgeRight]
    omega

theorem wedge_bead_cases (b : (wedge T U).Bead) :
    (∃ c : T.Bead, wedgeLeftBead T U c = b) ∨
      (∃ c : U.Bead, wedgeRightBead T U c = b) := by
  by_cases hb : b.right.val ≤ T.len
  · exact Or.inl ⟨leftDownBead T U b hb, wedgeLeft_leftDown T U b hb⟩
  · have hl : T.len ≤ b.left.val := by
      by_contra hn
      have hg : wedgeRight T U 0 ∈ (wedge T U).joints :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0, U.first_mem, rfl⟩)
      apply b.no_joint (wedgeRight T U 0) hg
      · change b.left.val < T.len + 0; omega
      · change T.len + 0 < b.right.val; omega
    exact Or.inr ⟨rightDownBead T U b hl, wedgeRight_rightDown T U b hl⟩

end

end DaggerChosenRigidificationNecklace.NecklaceCode
