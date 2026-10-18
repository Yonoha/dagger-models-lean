import ChosenNecklaceGeneralJointImages
import ChosenNecklaceForget

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T U : NecklaceCode}

def generalOrderMap (f : toSSet.{u} T ⟶ toSSet.{u} U) : Vertices.{u} T →o Vertices.{u} U :=
  (orderMap f).uliftMap

/-- Same direct-image path formula for an arbitrary actual necklace SSet map. -/
def generalMapPath (f : toSSet.{u} T ⟶ toSSet.{u} U) {a b : Vertices.{u} T}
    (P : JointPath a b) : JointPath (generalOrderMap f a) (generalOrderMap f b) where
  I := generalOrderMap f '' P.I
  left := Set.mem_image_of_mem _ P.left
  right := Set.mem_image_of_mem _ P.right
  left_le v hv := by
    obtain ⟨w, hw, rfl⟩ := hv
    exact (generalOrderMap f).monotone (P.left_le w hw)
  le_right v hv := by
    obtain ⟨w, hw, rfl⟩ := hv
    exact (generalOrderMap f).monotone (P.le_right w hw)
  joints j hj hl hr := by
    obtain ⟨v, hv, he⟩ := joint_between_image f j hj
      (((orderMap f).monotone (Fin.zero_le a.down)).trans hl)
      (hr.trans ((orderMap f).monotone (Fin.le_last b.down)))
    have heq : generalOrderMap f (ULift.up v) = ULift.up j := ULift.ext _ _ he
    by_cases ha : ULift.up j = generalOrderMap f a
    · exact ha.symm ▸ Set.mem_image_of_mem _ P.left
    by_cases hb : ULift.up j = generalOrderMap f b
    · exact hb.symm ▸ Set.mem_image_of_mem _ P.right
    have hleft : a ≤ ULift.up v := by
      by_contra h
      have hm := (generalOrderMap f).monotone (le_of_lt (lt_of_not_ge h))
      exact ha (le_antisymm (heq ▸ hm) hl)
    have hright : ULift.up v ≤ b := by
      by_contra h
      have hm := (generalOrderMap f).monotone (le_of_lt (lt_of_not_ge h))
      exact hb (le_antisymm hr (heq ▸ hm))
    exact ⟨ULift.up v, P.joints v hv hleft hright, heq⟩

def generalPathFunctor (f : toSSet.{u} T ⟶ toSSet.{u} U) (a b : Vertices.{u} T) :
    JointPath a b ⥤ JointPath (generalOrderMap f a) (generalOrderMap f b) where
  obj := generalMapPath f
  map h := ⟨⟨⟨Set.image_mono h.1.1.1⟩⟩⟩

def generalNCMap (f : toSSet.{u} T ⟶ toSSet.{u} U) : NC.{u} T ⟶ NC.{u} U where
  obj a := ⟨generalOrderMap f a.as⟩
  map a b := nerveMap (generalPathFunctor f a.as b.as)
  map_id a := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext Set.image_singleton)
  map_comp a b c := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext (Set.image_union _ _ _))

theorem generalNCMap_of_hom (f : NecklaceCode.Hom.{u} T U) : generalNCMap f.map = NCMap f := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro a b
  ext q F
  exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext rfl)

theorem generalNCMap_forget (f : toSSet.{u} T ⟶ toSSet.{u} U) :
    generalNCMap f ≫ forgetNC U = forgetNC T ≫ DaggerChosenRigidificationNecklace.T.map
      (SimplexCategory.Hom.mk (orderMap f) : ⦋T.len⦌ ⟶ ⦋U.len⦌) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro a b
  ext q F
  exact CategoryTheory.Functor.ext (fun _ ↦ SimplicialThickening.Path.ext rfl)

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
