import ChosenNecklaceJointImages

open CategoryTheory SimplicialThickening

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode

/-- The actual vertices, as a fresh object type for the necklace thickening. -/
structure NecklaceThickening (T : NecklaceCode) : Type u where
  as : NecklaceCode.Vertices.{u} T

namespace NecklaceThickening

/-- Original Mathlib paths, with precisely the additional interior-joint requirement. -/
structure JointPath {T : NecklaceCode} (a b : NecklaceCode.Vertices.{u} T)
    extends SimplicialThickening.Path a b where
  joints : ∀ j ∈ T.joints, a ≤ ULift.up j → ULift.up j ≤ b → ULift.up j ∈ I

namespace JointPath

variable {T : NecklaceCode} {a b : NecklaceCode.Vertices.{u} T}

@[ext] theorem ext {P Q : JointPath a b} (h : P.I = Q.I) : P = Q := by
  have hh : P.toPath = Q.toPath := SimplicialThickening.Path.ext h
  cases P
  cases Q
  cases hh
  rfl

theorem le (P : JointPath a b) : a ≤ b := P.toPath.le

instance : Category (JointPath a b) :=
  inferInstanceAs (Category (InducedCategory _ (fun P : JointPath a b ↦ P.I)))

end JointPath

instance (T : NecklaceCode) : CategoryStruct (NecklaceThickening.{u} T) where
  Hom a b := JointPath a.as b.as
  id a :=
    { I := {a.as}
      left := by simp
      right := by simp
      left_le v h := (Set.mem_singleton_iff.mp h).ge
      le_right v h := (Set.mem_singleton_iff.mp h).le
      joints j _ hl hr := Set.mem_singleton_iff.mpr (le_antisymm hr hl) }
  comp {a b c} P Q :=
    { I := P.I ∪ Q.I
      left := Or.inl P.left
      right := Or.inr Q.right
      left_le v h := h.elim (P.left_le v) (fun hv ↦ P.le.trans (Q.left_le v hv))
      le_right v h := h.elim (fun hv ↦ (P.le_right v hv).trans Q.le) (Q.le_right v)
      joints j hj hl hr := by
        by_cases hm : ULift.up j ≤ b.as
        · exact Or.inl (P.joints j hj hl hm)
        · exact Or.inr (Q.joints j hj (le_of_not_ge hm) hr) }

instance (T : NecklaceCode) : Category (NecklaceThickening.{u} T) where
  id_comp P := by
    apply JointPath.ext
    ext v
    exact ⟨fun h ↦ h.elim (fun hv ↦ (Set.mem_singleton_iff.mp hv) ▸ P.left) id, Or.inr⟩
  comp_id P := by
    apply JointPath.ext
    ext v
    exact ⟨fun h ↦ h.elim id (fun hv ↦ (Set.mem_singleton_iff.mp hv) ▸ P.right), Or.inl⟩
  assoc P Q R := JointPath.ext (Set.union_assoc _ _ _)

end NecklaceThickening

end

end DaggerChosenRigidificationNecklace
