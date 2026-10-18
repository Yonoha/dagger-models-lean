import ChosenNecklacePaths

open CategoryTheory

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T U : NecklaceCode}

def vertexOrderMap (f : NecklaceCode.Hom.{u} T U) :
    NecklaceCode.Vertices.{u} T →o NecklaceCode.Vertices.{u} U :=
  (NecklaceCode.orderMap f.map).uliftMap

def mapPath (f : NecklaceCode.Hom.{u} T U)
    {a b : NecklaceCode.Vertices.{u} T} (P : JointPath a b) :
      JointPath (vertexOrderMap f a) (vertexOrderMap f b) where
  I := vertexOrderMap f '' P.I
  left := Set.mem_image_of_mem _ P.left
  right := Set.mem_image_of_mem _ P.right
  left_le v h := by
    obtain ⟨w, hw, rfl⟩ := h
    exact (vertexOrderMap f).monotone (P.left_le w hw)
  le_right v h := by
    obtain ⟨w, hw, rfl⟩ := h
    exact (vertexOrderMap f).monotone (P.le_right w hw)
  joints j hj hl hr := by
    by_cases ha : ULift.up j = vertexOrderMap f a
    · exact ha.symm ▸ Set.mem_image_of_mem _ P.left
    by_cases hb : ULift.up j = vertexOrderMap f b
    · exact hb.symm ▸ Set.mem_image_of_mem _ P.right
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp (NecklaceCode.joints_subset_image f hj)
    have heq : vertexOrderMap f (ULift.up v) = ULift.up j := ULift.ext _ _ he
    have hleft : a ≤ ULift.up v := by
      by_contra h
      have hm := (vertexOrderMap f).monotone (le_of_lt (lt_of_not_ge h))
      have hh : ULift.up j ≤ vertexOrderMap f a := heq ▸ hm
      exact ha (le_antisymm hh hl)
    have hright : ULift.up v ≤ b := by
      by_contra h
      have hm := (vertexOrderMap f).monotone (le_of_lt (lt_of_not_ge h))
      have hh : vertexOrderMap f b ≤ ULift.up j := heq ▸ hm
      exact hb (le_antisymm hr hh)
    exact ⟨ULift.up v, P.joints v hv hleft hright, heq⟩

def mapPathFunctor (f : NecklaceCode.Hom.{u} T U)
    (a b : NecklaceCode.Vertices.{u} T) :
      JointPath a b ⥤ JointPath (vertexOrderMap f a) (vertexOrderMap f b) where
  obj := mapPath f
  map h := ⟨⟨⟨Set.image_mono h.1.1.1⟩⟩⟩

theorem mapPath_I (f : NecklaceCode.Hom.{u} T U)
    {a b : NecklaceCode.Vertices.{u} T} (P : JointPath a b) :
      (mapPath f P).I = vertexOrderMap f '' P.I := rfl

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
