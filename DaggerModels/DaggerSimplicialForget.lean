import DaggerModels.DaggerSimplicialCategory
import DaggerModels.DaggerSimplicialGraph

/-!
# Forgetting enriched composition

The functor `UCatDag` preceding Part I `bg.lem.presentable` keeps the original
objects, mapping simplicial sets, and dagger, and forgets composition and units.
Here objects and mapping spaces share an arbitrary universe `u`.
-/

open CategoryTheory

universe u

namespace DaggerModels.DaggerSimplicialCat

/-- The actual underlying dagger simplicial graph. -/
def underlyingGraph (C : DaggerSimplicialCat.{u, u}) : DaggerSimplicialGraph.{u} where
  Obj := C.Obj
  Hom X Y := X ⟶[SSet.{u}] Y
  dagger := DaggerSimplicialStructure.dagger
  dagger_involutive := DaggerSimplicialStructure.dagger_involutive

/-- A dagger simplicial functor induces its original map on the underlying graphs. -/
def underlyingGraphMap {C D : DaggerSimplicialCat.{u, u}} (F : Hom C D) :
    DaggerSimplicialGraph.Map (underlyingGraph C) (underlyingGraph D) where
  obj := F.obj
  map := F.map
  map_dagger := F.map_dagger

/-- The forgetful functor used in the free-category adjunction. -/
def forgetGraph : DaggerSimplicialCat.{u, u} ⥤ DaggerSimplicialGraph.{u} where
  obj := underlyingGraph
  map := underlyingGraphMap
  map_id _ := rfl
  map_comp _ _ := rfl

instance : forgetGraph.{u}.Faithful where
  map_injective {C D} F G h := by
    cases F with
    | mk F hF =>
      cases G with
      | mk G hG =>
        cases F with
        | mk Fo Fm Fi Fc =>
          cases G with
          | mk Go Gm Gi Gc =>
            change (⟨Fo, Fm, _⟩ : DaggerSimplicialGraph.Map
              (underlyingGraph C) (underlyingGraph D)) = ⟨Go, Gm, _⟩ at h
            cases h
            rfl

/-- Restrict a dagger simplicial functor along a specified graph map. -/
def restrictGraph {G : DaggerSimplicialGraph.{u}} {C D : DaggerSimplicialCat.{u, u}}
    (eta : DaggerSimplicialGraph.Map G (underlyingGraph C)) (F : Hom C D) :
    DaggerSimplicialGraph.Map G (underlyingGraph D) where
  obj x := F.obj (eta.obj x)
  map x y := eta.map x y ≫ F.map (eta.obj x) (eta.obj y)
  map_dagger x y := by
    dsimp only [underlyingGraph]
    rw [Category.assoc, F.map_dagger, ← Category.assoc]
    exact congrArg (fun h ↦ h ≫ F.map (eta.obj y) (eta.obj x)) (eta.map_dagger x y)

end DaggerModels.DaggerSimplicialCat
