import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Opposite
import Mathlib.CategoryTheory.Adjunction.Basic

/-! `dj.not.adjunctions`: free dagger completion of already composed simplicial categories.
The full enrichment, arbitrary object maps, dagger laws, and actual forgetful functor are explicit.
The theorem proof marker is a specification; there are no definition holes. -/
open CategoryTheory MonoidalCategory BraidedCategory Opposite Simplicial
universe o v u
namespace DaggerModels

structure SimplicialCat where
  Obj : Type o
  enriched : EnrichedCategory SSet.{v} Obj
attribute [instance] SimplicialCat.enriched

namespace SimplicialCat
instance : CoeSort (SimplicialCat.{o, v}) (Type o) := ⟨Obj⟩
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
end SimplicialCat

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

def forget : DaggerSimplicialCat.{o, v} ⥤ SimplicialCat.{o, v} where
  obj C := C.toSimplicialCat
  map F := F.toEnrichedFunctor

end DaggerSimplicialCat

set_option warningAsError false in
theorem exists_ordinaryFreeDaggerAdjunction :
    ∃ L : SimplicialCat.{u, u} ⥤ DaggerSimplicialCat.{u, u},
      ∃ A : L ⊣ DaggerSimplicialCat.forget,
        ∀ C : SimplicialCat.{u, u}, (L.obj C).Obj = C.Obj ∧
          HEq (A.unit.app C).obj (id : C.Obj → C.Obj) := by sorry

end DaggerModels
