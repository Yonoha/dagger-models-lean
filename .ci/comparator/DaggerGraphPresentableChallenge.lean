import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Presentable.Adjunction

/-! Part I `bg.lem.presentable`: the actual graph category is locally finitely presentable.
The graph, all graph maps, and the complete category structure are explicit. -/
set_option warningAsError false
open CategoryTheory Limits
universe u
namespace DaggerModels

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

end DaggerSimplicialGraph

theorem exists_daggerGraphPresheafEquivalence :
    ∃ (I : Type) (hI : SmallCategory I),
      letI := hI
      Nonempty (DaggerSimplicialGraph.{u} ≌ (Iᵒᵖ ⥤ Type u)) := by sorry

theorem daggerGraphHasLimits : HasLimits DaggerSimplicialGraph.{u} := by sorry

theorem daggerGraphHasColimits : HasColimits DaggerSimplicialGraph.{u} := by sorry

theorem daggerGraphLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} DaggerSimplicialGraph.{u} := by sorry

theorem daggerGraphLocallyPresentable :
    IsLocallyPresentable.{u} DaggerSimplicialGraph.{u} := by sorry

end DaggerModels
