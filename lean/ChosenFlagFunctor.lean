import ChosenFlagEnrichment
import ChosenFlagHomMaps
import ChosenNecklacesOverPostcomp

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode

variable {X Y Z : SSet.{u}}

def EMap (f : X ⟶ Y) : E X ⟶ E Y where
  obj := f.app (op ⦋0⦌)
  map _ _ := flagHomMap f
  map_id a := by
    ext q x
    exact Quot.sound ⟨NecklacesOver.postcompPointHom f a,
      (NecklaceCode.Flag.map_id (NecklaceCode.Flag.pointFlag q.unop.len)).symm⟩
  map_comp a b c := by
    ext q x
    rcases x with ⟨x,y⟩
    induction x using Quot.ind with | _ p
    induction y using Quot.ind with | _ r
    exact Quot.sound ⟨NecklacesOver.postcompWedgeHom f p.1 r.1,
      (NecklaceCode.Flag.map_id (NecklaceCode.Flag.wedge p.2 r.2)).symm⟩

theorem EMap_obj (f : X ⟶ Y) (a : (E X).Obj) : (EMap f).obj a = f.app _ a := rfl

theorem EMap_hom (f : X ⟶ Y) (a b : (E X).Obj) : (EMap f).map a b = flagHomMap f := rfl

theorem EMap_id (X : SSet.{u}) : EMap (𝟙 X) = 𝟙 (E X) := by
  have ho : ∀ a : (E X).Obj, (EMap (𝟙 X)).obj a = a := fun _ ↦ rfl
  apply EnrichedFunctor.ext SSet ho
  intro a b
  change flagHomMap (a := a) (b := b) (𝟙 X) ≫ eqToHom rfl = 𝟙 _
  rw [eqToHom_refl, Category.comp_id, flagHomMap_id]

theorem EMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) : EMap (f ≫ g) = EMap f ≫ EMap g := by
  have ho : ∀ a : (E X).Obj, (EMap (f ≫ g)).obj a = (EMap f ≫ EMap g).obj a :=
    fun _ ↦ rfl
  apply EnrichedFunctor.ext SSet ho
  intro a b
  change flagHomMap (a := a) (b := b) (f ≫ g) ≫ eqToHom rfl =
    flagHomMap f ≫ flagHomMap g
  rw [eqToHom_refl, Category.comp_id, flagHomMap_comp]

def flagCategoryFunctor : SSet.{u} ⥤ DaggerModels.SimplicialCat.{u,u} where
  obj := E
  map := EMap
  map_id := EMap_id
  map_comp := EMap_comp

end

end DaggerChosenRigidificationNecklace
