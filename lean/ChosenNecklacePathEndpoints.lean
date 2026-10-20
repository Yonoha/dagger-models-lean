import ChosenNecklacePaths

open CategoryTheory

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening.JointPath

variable {T : NecklaceCode} {a b : NecklaceCode.Vertices.{u} T}

theorem diagonal_I (P : JointPath a a) : P.I = {a} := by
  ext v
  constructor
  · intro hv
    exact Set.mem_singleton_iff.mpr (le_antisymm (P.le_right v hv) (P.left_le v hv))
  · intro hv
    exact (Set.mem_singleton_iff.mp hv) ▸ P.left

instance diagonalSubsingleton : Subsingleton (JointPath a a) :=
  ⟨fun P Q ↦ JointPath.ext (P.diagonal_I.trans Q.diagonal_I.symm)⟩

def diagonal (a : NecklaceCode.Vertices.{u} T) : JointPath a a :=
  𝟙 (NecklaceThickening.mk a)

instance diagonalUnique : Unique (JointPath a a) where
  default := diagonal a
  uniq _ := Subsingleton.elim _ _

def isEmpty_of_not_le (h : ¬a ≤ b) : IsEmpty (JointPath a b) :=
  ⟨fun P ↦ h P.le⟩

theorem not_nonempty_of_gt (h : b < a) : ¬Nonempty (JointPath a b) :=
  fun ⟨P⟩ ↦ (not_le_of_gt h) P.le

end DaggerChosenRigidificationNecklace.NecklaceThickening.JointPath
