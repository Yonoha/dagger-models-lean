import ChosenNecklaceEnrichedMaps

open CategoryTheory EnrichedCategory MonoidalCategory Opposite

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T U V : NecklaceCode}

def castHom {a b c d : NecklaceThickening.{u} T} (ha : a = c) (hb : b = d) :
    pathHom a b ⟶ pathHom c d := eqToHom (by rw [ha, hb])

theorem castHom_I {a b c d : NecklaceThickening.{u} T} (ha : a = c) (hb : b = d)
    (q : SimplexCategoryᵒᵖ) (F : (pathHom a b).obj q) (i : Fin (q.unop.len + 1)) :
    (((castHom ha hb).app q F).obj i).I = (F.obj i).I := by
  cases ha
  cases hb
  rfl

theorem pathHom_eqToHom_I {a b c d : NecklaceThickening.{u} T}
    (ha : a = c) (hb : b = d) (h : pathHom a b = pathHom c d)
    (q : SimplexCategoryᵒᵖ) (F : (pathHom a b).obj q) (i : Fin (q.unop.len + 1)) :
    (((eqToHom h).app q F).obj i).I = (F.obj i).I := by
  cases ha
  cases hb
  rfl

theorem vertexOrderMap_id : vertexOrderMap (NecklaceCode.Hom.id.{u} T) =
    OrderHom.id := by
  apply DFunLike.ext
  intro v
  exact congrFun mapVertices_id v

theorem vertexOrderMap_comp (f : NecklaceCode.Hom.{u} T U)
    (g : NecklaceCode.Hom.{u} U V) :
    vertexOrderMap (NecklaceCode.Hom.comp f g) = (vertexOrderMap g).comp (vertexOrderMap f) := by
  apply DFunLike.ext
  intro v
  exact congrFun (mapVertices_comp f.map g.map) v

theorem NCMap_id (T : NecklaceCode) : NCMap (NecklaceCode.Hom.id.{u} T) = 𝟙 (NC.{u} T) := by
  have ho : ∀ a : (NC.{u} T).Obj, (NCMap (NecklaceCode.Hom.id T)).obj a = a := by
    intro a
    cases a
    simp only [NCMap, vertexOrderMap_id, OrderHom.id_coe]
    rfl
  apply EnrichedFunctor.ext SSet ho
  intro a b
  ext q F
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change (((castHom (ho a) (ho b)).app q
      (((NCMap (NecklaceCode.Hom.id T)).map a b).app q F)).obj
      i).I = (F.obj i).I
    rw [castHom_I]
    change vertexOrderMap (NecklaceCode.Hom.id T) '' (F.obj i).I = (F.obj i).I
    rw [vertexOrderMap_id]
    exact Set.image_id _))

theorem NCMap_comp (f : NecklaceCode.Hom.{u} T U) (g : NecklaceCode.Hom.{u} U V) :
    NCMap (NecklaceCode.Hom.comp f g) = NCMap f ≫ NCMap g := by
  have ho : ∀ a : (NC.{u} T).Obj,
      (NCMap (NecklaceCode.Hom.comp f g)).obj a = (NCMap f ≫ NCMap g).obj a := by
    intro a
    simp only [NCMap, DaggerModels.SimplicialCat.comp_obj, vertexOrderMap_comp,
      OrderHom.comp_coe, Function.comp_apply]
  apply EnrichedFunctor.ext SSet ho
  intro a b
  ext q F
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change (((castHom (ho a) (ho b)).app q
      (((NCMap (NecklaceCode.Hom.comp f g)).map a b).app
      q F)).obj i).I =
        ((((NCMap g).map ((NCMap f).obj a) ((NCMap f).obj b)).app q
          (((NCMap f).map a b).app q F)).obj i).I
    rw [castHom_I]
    change vertexOrderMap (NecklaceCode.Hom.comp f g) '' (F.obj i).I =
      vertexOrderMap g '' (vertexOrderMap f '' (F.obj i).I)
    rw [vertexOrderMap_comp, Set.image_image]
    rfl))

def NCFunctor : NecklaceCode ⥤ DaggerModels.SimplicialCat.{u, u} where
  obj := NC
  map := NCMap
  map_id := NCMap_id
  map_comp := NCMap_comp

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
