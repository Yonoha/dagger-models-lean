import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Opposite
import Mathlib.CategoryTheory.Monad.Monadicity
import Mathlib.CategoryTheory.Presentable.Basic

/-! Part I `bg.lem.presentable`: the exact graph forgetful functor is monadic.
All underlying data and both category structures are explicit in this specification. -/
set_option warningAsError false
open CategoryTheory MonoidalCategory
attribute [local instance] Cardinal.fact_isRegular_aleph0
universe o v u
namespace DaggerModels

structure SimplicialCat where
  Obj : Type o
  enriched : EnrichedCategory SSet.{v} Obj
attribute [instance] SimplicialCat.enriched

noncomputable instance sSetBraidedCategory : BraidedCategory SSet.{v} :=
  .ofCartesianMonoidalCategory

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
instance : CoeSort (DaggerSimplicialCat.{o, v}) (Type o) := ⟨Obj⟩
instance enriched (C : DaggerSimplicialCat.{o, v}) : EnrichedCategory SSet.{v} C.Obj :=
  C.toSimplicialCat.enriched
instance daggerStructureInstance (C : DaggerSimplicialCat.{o, v}) :
    DaggerSimplicialStructure C.Obj := C.daggerStructure

structure Hom (C D : DaggerSimplicialCat.{o, v}) extends
    EnrichedFunctor SSet.{v} C.Obj D.Obj where
  map_dagger (X Y : C.Obj) :
    map X Y ≫ DaggerSimplicialStructure.dagger (obj X) (obj Y) =
      DaggerSimplicialStructure.dagger X Y ≫ map Y X
@[ext]
theorem Hom.ext {C D : DaggerSimplicialCat.{o, v}} {F G : Hom C D}
    (h : F.toEnrichedFunctor = G.toEnrichedFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl
def Hom.id (C : DaggerSimplicialCat.{o, v}) : Hom C C where
  toEnrichedFunctor := EnrichedFunctor.id SSet C.Obj
  map_dagger X Y := by simp
def Hom.comp {C D E : DaggerSimplicialCat.{o, v}} (F : Hom C D) (G : Hom D E) :
    Hom C E where
  toEnrichedFunctor := F.toEnrichedFunctor.comp SSet G.toEnrichedFunctor
  map_dagger X Y := by
    dsimp
    rw [Category.assoc, G.map_dagger, ← Category.assoc, F.map_dagger, Category.assoc]
instance : Category DaggerSimplicialCat.{o, v} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp F := by
    apply Hom.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [Hom.id, Hom.comp, EnrichedFunctor.id, EnrichedFunctor.comp]
  comp_id F := by
    apply Hom.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [Hom.id, Hom.comp, EnrichedFunctor.id, EnrichedFunctor.comp]
  assoc F G H := by
    apply Hom.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [Hom.comp, EnrichedFunctor.comp, Category.assoc]

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
namespace DaggerSimplicialCat

def underlyingGraph (C : DaggerSimplicialCat.{u, u}) : DaggerSimplicialGraph.{u} where
  Obj := C.Obj
  Hom X Y := X ⟶[SSet.{u}] Y
  dagger := DaggerSimplicialStructure.dagger
  dagger_involutive := DaggerSimplicialStructure.dagger_involutive
def underlyingGraphMap {C D : DaggerSimplicialCat.{u, u}} (F : Hom C D) :
    DaggerSimplicialGraph.Map (underlyingGraph C) (underlyingGraph D) where
  obj := F.obj
  map := F.map
  map_dagger := F.map_dagger
def forgetGraph : DaggerSimplicialCat.{u, u} ⥤ DaggerSimplicialGraph.{u} where
  obj := underlyingGraph
  map := underlyingGraphMap
  map_id _ := rfl
  map_comp _ _ := rfl

theorem forgetGraph_reflectsIsomorphisms : forgetGraph.{u}.ReflectsIsomorphisms := by sorry

theorem forgetGraph_monadic : Nonempty (MonadicRightAdjoint forgetGraph.{u}) := by sorry

theorem exists_finitary_freeDaggerSimplicialCategoryAdjunction :
    ∃ F : DaggerSimplicialGraph.{u} ⥤ DaggerSimplicialCat.{u, u},
      Nonempty (F ⊣ forgetGraph) ∧
        (F ⋙ forgetGraph).IsCardinalAccessible Cardinal.aleph0.{u} := by sorry

end DaggerSimplicialCat
end DaggerModels
