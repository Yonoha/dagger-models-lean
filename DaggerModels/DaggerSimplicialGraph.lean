import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Dagger simplicial graphs

Part I `bg.def.dagger-graph`: the dagger on an edge space is an ordinary
map of simplicial sets, with source and target exchanged. Objects and edge
spaces share the arbitrary universe `u`; this is the small-graph setting
in which the free path construction stays in the same universe.
-/

open CategoryTheory

universe u

namespace DaggerModels

/-- A small simplicial graph with an involution exchanging edge endpoints. -/
structure DaggerSimplicialGraph where
  Obj : Type u
  Hom : Obj → Obj → SSet.{u}
  dagger : ∀ x y, Hom x y ⟶ Hom y x
  dagger_involutive : ∀ x y, dagger x y ≫ dagger y x = 𝟙 (Hom x y)

namespace DaggerSimplicialGraph

/-- A map of dagger simplicial graphs. -/
structure Map (G H : DaggerSimplicialGraph.{u}) where
  obj : G.Obj → H.Obj
  map : ∀ x y, G.Hom x y ⟶ H.Hom (obj x) (obj y)
  map_dagger : ∀ x y, map x y ≫ H.dagger (obj x) (obj y) = G.dagger x y ≫ map y x

@[ext] theorem Map.ext {G H : DaggerSimplicialGraph.{u}} {f g : Map G H}
    (hobj : f.obj = g.obj) (hmap : HEq f.map g.map) : f = g := by
  cases f
  cases g
  cases hobj
  cases hmap
  rfl

instance : Category (DaggerSimplicialGraph.{u}) where
  Hom := Map
  id G :=
    { obj := id
      map := fun x y ↦ 𝟙 (G.Hom x y)
      map_dagger := fun x y ↦ by simp }
  comp f g :=
    { obj := g.obj ∘ f.obj
      map := fun x y ↦ f.map x y ≫ g.map (f.obj x) (f.obj y)
      map_dagger := fun x y ↦ by
        dsimp only [Function.comp_apply]
        rw [Category.assoc, g.map_dagger, ← Category.assoc, f.map_dagger,
          Category.assoc] }
  id_comp f := by
    apply Map.ext rfl
    apply heq_of_eq
    funext x y
    simp
  comp_id f := by
    apply Map.ext rfl
    apply heq_of_eq
    funext x y
    simp
  assoc f g h := by
    apply Map.ext rfl
    apply heq_of_eq
    funext x y
    simp [Category.assoc]

@[simp] theorem id_obj (G : DaggerSimplicialGraph.{u}) : (𝟙 G : G ⟶ G).obj = id := rfl

@[simp] theorem id_map (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    (𝟙 G : G ⟶ G).map x y = 𝟙 (G.Hom x y) := rfl

@[simp] theorem comp_obj {G H K : DaggerSimplicialGraph.{u}} (f : G ⟶ H) (g : H ⟶ K) :
    (f ≫ g).obj = g.obj ∘ f.obj := rfl

@[simp] theorem comp_map {G H K : DaggerSimplicialGraph.{u}} (f : G ⟶ H) (g : H ⟶ K)
    (x y : G.Obj) : (f ≫ g).map x y = f.map x y ≫ g.map (f.obj x) (f.obj y) := rfl

@[simp] theorem dagger_app_involutive (G : DaggerSimplicialGraph.{u}) (x y : G.Obj)
    (n : SimplexCategoryᵒᵖ) (e : (G.Hom x y).obj n) :
    (G.dagger y x).app n ((G.dagger x y).app n e) = e := by
  have h := congrArg (fun f : G.Hom x y ⟶ G.Hom x y ↦ f.app n e)
    (G.dagger_involutive x y)
  exact h

end DaggerSimplicialGraph
end DaggerModels
