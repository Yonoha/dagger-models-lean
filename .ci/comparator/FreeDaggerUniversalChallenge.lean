import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Opposite

/-! The genuine free-construction universal property in Part I `bg.lem.presentable`. -/
set_option warningAsError false
open CategoryTheory MonoidalCategory
universe o v u
namespace DaggerModels

noncomputable instance sSetBraidedCategory : BraidedCategory SSet.{v} :=
  .ofCartesianMonoidalCategory

structure SimplicialCat where
  Obj : Type o
  enriched : EnrichedCategory SSet.{v} Obj
attribute [instance] SimplicialCat.enriched

class DaggerSimplicialStructure (C : Type o) [EnrichedCategory SSet.{v} C] where
  dagger (X Y : C) : (X ⟶[SSet.{v}] Y) ⟶ (Y ⟶[SSet.{v}] X)
  dagger_involutive (X Y : C) : dagger X Y ≫ dagger Y X = 𝟙 _
  dagger_id (X : C) : eId SSet X ≫ dagger X X = eId SSet X
  dagger_comp (X Y Z : C) :
    eComp SSet X Y Z ≫ dagger X Z =
      (dagger X Y ⊗ₘ dagger Y Z) ≫
        (β_ (Y ⟶[SSet.{v}] X) (Z ⟶[SSet.{v}] Y)).hom ≫ eComp SSet Z Y X

structure DaggerSimplicialCat where
  toSimplicialCat : SimplicialCat.{o, v}
  daggerStructure : DaggerSimplicialStructure toSimplicialCat.Obj

namespace DaggerSimplicialCat
abbrev Obj (C : DaggerSimplicialCat.{o, v}) := C.toSimplicialCat.Obj
instance enriched (C : DaggerSimplicialCat.{o, v}) : EnrichedCategory SSet.{v} C.Obj :=
  C.toSimplicialCat.enriched
instance daggerStructureInstance (C : DaggerSimplicialCat.{o, v}) :
    DaggerSimplicialStructure C.Obj := C.daggerStructure

structure Hom (C D : DaggerSimplicialCat.{o, v}) extends
    EnrichedFunctor SSet.{v} C.Obj D.Obj where
  map_dagger (X Y : C.Obj) :
    map X Y ≫ DaggerSimplicialStructure.dagger (obj X) (obj Y) =
      DaggerSimplicialStructure.dagger X Y ≫ map Y X
end DaggerSimplicialCat

structure DaggerSimplicialGraph where
  Obj : Type u
  Hom : Obj → Obj → SSet.{u}
  dagger : ∀ x y, Hom x y ⟶ Hom y x
  dagger_involutive : ∀ x y, dagger x y ≫ dagger y x = 𝟙 (Hom x y)

namespace DaggerSimplicialGraph
structure Map (G H : DaggerSimplicialGraph.{u}) where
  obj : G.Obj → H.Obj
  map : ∀ x y, G.Hom x y ⟶ H.Hom (obj x) (obj y)
  map_dagger : ∀ x y, map x y ≫ H.dagger (obj x) (obj y) = G.dagger x y ≫ map y x
end DaggerSimplicialGraph

namespace DaggerSimplicialCat
def underlyingGraph (C : DaggerSimplicialCat.{u, u}) : DaggerSimplicialGraph.{u} where
  Obj := C.Obj
  Hom X Y := X ⟶[SSet.{u}] Y
  dagger := DaggerSimplicialStructure.dagger
  dagger_involutive := DaggerSimplicialStructure.dagger_involutive

/-- Restriction along the specified unit, on all objects and all mapping spaces. -/
def restrictGraph {G : DaggerSimplicialGraph.{u}} {C D : DaggerSimplicialCat.{u, u}}
    (eta : DaggerSimplicialGraph.Map G (underlyingGraph C)) (F : Hom C D) :
    DaggerSimplicialGraph.Map G (underlyingGraph D) where
  obj x := F.obj (eta.obj x)
  map x y := eta.map x y ≫ F.map (eta.obj x) (eta.obj y)
  map_dagger x y := by
    dsimp only [underlyingGraph]
    rw [Category.assoc, F.map_dagger, ← Category.assoc]
    exact congrArg (fun h ↦ h ≫ F.map (eta.obj y) (eta.obj x)) (eta.map_dagger x y)
end DaggerSimplicialCat

theorem exists_freeDaggerSimplicialCategory (G : DaggerSimplicialGraph.{u}) :
    ∃ (C : DaggerSimplicialCat.{u, u})
      (eta : DaggerSimplicialGraph.Map G (DaggerSimplicialCat.underlyingGraph C)),
      ∀ D : DaggerSimplicialCat.{u, u},
        Function.Bijective (DaggerSimplicialCat.restrictGraph eta (D := D)) := by sorry

end DaggerModels
