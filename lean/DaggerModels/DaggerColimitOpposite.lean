import DaggerModels.DaggerStructureFromOpposite
import DaggerModels.SimplicialObjectAdjunctions
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-! The involutive opposite functor induced on an arbitrary ordinary colimit
of a dagger diagram. Fixing objects and lifting the colimit are separate steps. -/

open CategoryTheory Limits

universe o v w w'

namespace DaggerModels.DaggerSimplicialCat.OrdinaryColimit

variable {J : Type w} [Category.{w'} J] (K : J ⥤ DaggerSimplicialCat.{o, v})
  (c : Cocone (K ⋙ forget))

noncomputable def oppositeCocone : Cocone (K ⋙ forget) where
  pt := SimplicialCat.opposite c.pt
  ι :=
    { app := fun j ↦ daggerNatural.app (K.obj j) ≫
        SimplicialCat.oppositeFunctor.map (c.ι.app j)
      naturality := by
        intro i j a
        change forget.map (K.map a) ≫ daggerNatural.app (K.obj j) ≫
            SimplicialCat.oppositeFunctor.map (c.ι.app j) =
          (daggerNatural.app (K.obj i) ≫
            SimplicialCat.oppositeFunctor.map (c.ι.app i)) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, daggerNatural.naturality, Functor.comp_map,
          Category.assoc, ← SimplicialCat.oppositeFunctor.map_comp]
        rw [show forget.map (K.map a) ≫ c.ι.app j = c.ι.app i from c.w a] }

noncomputable def toOpposite (hc : IsColimit c) : c.pt ⟶ SimplicialCat.opposite c.pt :=
  hc.desc (oppositeCocone K c)

theorem toOpposite_fac (hc : IsColimit c) (j : J) :
    c.ι.app j ≫ toOpposite K c hc = daggerNatural.app (K.obj j) ≫
      SimplicialCat.oppositeFunctor.map (c.ι.app j) := hc.fac _ j

/-- The induced opposite functor is involutive through the actual double-opposite map. -/
theorem toOpposite_square (hc : IsColimit c) :
    toOpposite K c hc ≫ SimplicialCat.oppositeFunctor.map (toOpposite K c hc) ≫
      SimplicialCat.doubleOppositeHom c.pt = 𝟙 c.pt := by
  apply hc.hom_ext
  intro j
  calc
    c.ι.app j ≫ toOpposite K c hc ≫
        SimplicialCat.oppositeFunctor.map (toOpposite K c hc) ≫
        SimplicialCat.doubleOppositeHom c.pt =
      (c.ι.app j ≫ toOpposite K c hc) ≫
        SimplicialCat.oppositeFunctor.map (toOpposite K c hc) ≫
        SimplicialCat.doubleOppositeHom c.pt := by simp only [Category.assoc]
    _ = daggerNatural.app (K.obj j) ≫
        SimplicialCat.oppositeFunctor.map (c.ι.app j ≫ toOpposite K c hc) ≫
        SimplicialCat.doubleOppositeHom c.pt := by
      rw [Functor.map_comp, toOpposite_fac]
      simp only [Category.assoc]
    _ = daggerNatural.app (K.obj j) ≫
        SimplicialCat.oppositeFunctor.map (daggerNatural.app (K.obj j) ≫
          SimplicialCat.oppositeFunctor.map (c.ι.app j)) ≫
        SimplicialCat.doubleOppositeHom c.pt := by rw [toOpposite_fac]
    _ = (daggerNatural.app (K.obj j) ≫
        SimplicialCat.oppositeFunctor.map (daggerNatural.app (K.obj j))) ≫
        (SimplicialCat.oppositeFunctor.map
          (SimplicialCat.oppositeFunctor.map (c.ι.app j)) ≫
            SimplicialCat.doubleOppositeHom c.pt) := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = (daggerNatural.app (K.obj j) ≫
        SimplicialCat.oppositeFunctor.map (daggerNatural.app (K.obj j))) ≫
        (SimplicialCat.doubleOppositeHom (forget.obj (K.obj j)) ≫ c.ι.app j) := by
      exact congrArg (fun a ↦ (daggerNatural.app (K.obj j) ≫
        SimplicialCat.oppositeFunctor.map (daggerNatural.app (K.obj j))) ≫ a)
        (SimplicialCat.doubleOppositeNatIso.hom.naturality (c.ι.app j))
    _ = c.ι.app j := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun f : forget.obj (K.obj j) ⟶ forget.obj (K.obj j) ↦ f ≫ c.ι.app j)
          (daggerNatural_square (K.obj j))

/-- Object-colimit uniqueness forces the induced dagger to fix every object. -/
theorem toOpposite_obj (hc : IsColimit c) (X : c.pt.Obj) :
    (toOpposite K c hc).obj X = Opposite.op X := by
  letI : PreservesColimitsOfSize.{w', w} SimplicialCat.objects.{o, v} :=
    SimplicialCat.objectsPreservesColimitsOfSize
  have he : SimplicialCat.objects.map (toOpposite K c hc) ≫
      SimplicialCat.oppositeObjectsIso.hom.app c.pt = 𝟙 (SimplicialCat.objects.obj c.pt) := by
    apply (isColimitOfPreserves SimplicialCat.objects hc).hom_ext
    intro j
    funext x
    have h := congrArg (fun F : forget.obj (K.obj j) ⟶ SimplicialCat.opposite c.pt ↦
      F.obj x) (toOpposite_fac K c hc j)
    exact congrArg Opposite.unop h
  exact congrArg Opposite.op (congrFun he X)

end DaggerModels.DaggerSimplicialCat.OrdinaryColimit
