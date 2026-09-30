import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Basic

/-!
# The category of simplicial categories

This bundles actual categories enriched in simplicial sets and their enriched
functors. Object and mapping-space universes remain independent. It supplies
the underlying category in Part I `bg.def.dagger-scat`, without assuming a
model structure or imposing any fibrancy condition on the mapping spaces.
-/

open CategoryTheory MonoidalCategory

universe o v

namespace DaggerModels

/-- A simplicial category, with its full simplicial mapping spaces. -/
structure SimplicialCat where
  Obj : Type o
  enriched : EnrichedCategory SSet.{v} Obj

attribute [instance] SimplicialCat.enriched

namespace SimplicialCat

instance : CoeSort (SimplicialCat.{o, v}) (Type o) := ⟨Obj⟩

/-- Bundle an existing simplicial enrichment. -/
def of (C : Type o) [EnrichedCategory SSet.{v} C] : SimplicialCat.{o, v} :=
  ⟨C, inferInstance⟩

instance : Category (SimplicialCat.{o, v}) where
  Hom C D := EnrichedFunctor SSet.{v} C.Obj D.Obj
  id C := EnrichedFunctor.id SSet C.Obj
  comp F G := EnrichedFunctor.comp SSet F G
  id_comp F := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [EnrichedFunctor.comp, EnrichedFunctor.id]
  comp_id F := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [EnrichedFunctor.comp, EnrichedFunctor.id]
  assoc F G H := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [EnrichedFunctor.comp, Category.assoc]

@[simp] theorem id_obj (C : SimplicialCat.{o, v}) (X : C.Obj) :
    (𝟙 C : EnrichedFunctor SSet C.Obj C.Obj).obj X = X := rfl

@[simp] theorem comp_obj {C D E : SimplicialCat.{o, v}} (F : C ⟶ D) (G : D ⟶ E)
    (X : C.Obj) : (F ≫ G).obj X = G.obj (F.obj X) := rfl

@[simp] theorem id_map (C : SimplicialCat.{o, v}) (X Y : C.Obj) :
    (𝟙 C : EnrichedFunctor SSet C.Obj C.Obj).map X Y = 𝟙 (X ⟶[SSet.{v}] Y) := rfl

@[simp] theorem comp_map {C D E : SimplicialCat.{o, v}} (F : C ⟶ D) (G : D ⟶ E)
    (X Y : C.Obj) : (F ≫ G).map X Y = F.map X Y ≫ G.map (F.obj X) (F.obj Y) := rfl

end SimplicialCat
end DaggerModels
