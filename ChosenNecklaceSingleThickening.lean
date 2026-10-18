import ChosenNecklaceSingleBead
import ChosenNecklaceEnrichedFunctor
import ChosenRigidificationSimplexColimit

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable (n : ℕ) (a b : Vertices.{u} (single n))

def singleForgetPath : JointPath a b ⥤ SimplicialThickening.Path a b where
  obj P := P.toPath
  map h := ⟨⟨⟨h.1.1.1⟩⟩⟩

def singleRestorePath : SimplicialThickening.Path a b ⥤ JointPath a b where
  obj P :=
    { toPath := P
      joints k hk hl hr := by
        rcases (mem_single_joints n k).mp hk with h | h
        · subst k
          have he : a = ULift.up 0 := le_antisymm hl (Fin.zero_le a.down)
          exact he ▸ P.left
        · subst k
          have he : b = ULift.up (Fin.last n) := le_antisymm (Fin.le_last b.down) hr
          exact he ▸ P.right }
  map h := ⟨⟨⟨h.1.1.1⟩⟩⟩

def singlePathIso : nerve (JointPath a b) ≅ nerve (SimplicialThickening.Path a b) where
  hom := nerveMap (singleForgetPath n a b)
  inv := nerveMap (singleRestorePath n a b)
  hom_inv_id := by
    ext q F
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext rfl)
  inv_hom_id := by
    ext q F
    exact CategoryTheory.Functor.ext (fun _ ↦ SimplicialThickening.Path.ext rfl)

def singleNCToThickening : NC.{u} (single n) ⟶ T.obj ⦋n⦌ where
  obj a := ⟨a.as⟩
  map a b := nerveMap (singleForgetPath n a.as b.as)
  map_id a := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ SimplicialThickening.Path.ext rfl)
  map_comp a b c := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ SimplicialThickening.Path.ext rfl)

def singleNCFromThickening : T.obj ⦋n⦌ ⟶ NC.{u} (single n) where
  obj a := ⟨a.as⟩
  map a b := nerveMap (singleRestorePath n a.as b.as)
  map_id a := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext rfl)
  map_comp a b c := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext rfl)

def singleNCIso : NC.{u} (single n) ≅ T.obj ⦋n⦌ where
  hom := singleNCToThickening n
  inv := singleNCFromThickening n
  hom_inv_id := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro a b
    simp only [DaggerModels.SimplicialCat.comp_map, eqToHom_refl, Category.comp_id]
  inv_hom_id := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro a b
    simp only [DaggerModels.SimplicialCat.comp_map, eqToHom_refl, Category.comp_id]

theorem singleNCIso_hom_obj (a : (NC.{u} (single n)).Obj) :
    (singleNCIso n).hom.obj a = ⟨a.as⟩ := rfl

theorem singleNCIso_inv_obj (a : (T.{u}.obj ⦋n⦌).Obj) :
    (singleNCIso n).inv.obj a = ⟨a.as⟩ := rfl

theorem singleNCIso_hom_app (a b : (NC.{u} (single n)).Obj)
    (k : ℕ) (P : (pathHom a b).obj (op ⦋k⦌)) (i : Fin (k + 1)) :
    ((((singleNCIso n).hom.map a b).app _ P).obj i).I = (P.obj i).I := rfl

theorem singleNCIso_naturality {n m : ℕ}
    (f : NecklaceCode.Hom.{u} (single n) (single m)) :
    NCMap f ≫ (singleNCIso m).hom =
      (singleNCIso n).hom ≫ SimplicialThickening.functor (vertexOrderMap f) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro a b
  simp only [DaggerModels.SimplicialCat.comp_map, eqToHom_refl, Category.comp_id]

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
