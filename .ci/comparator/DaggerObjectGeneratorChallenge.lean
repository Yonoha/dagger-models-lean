import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-! Part I `bg.not.cells` and the object-generator step of `bg.lem.I-inj`.
An actual initial-to-terminal dagger functor detects exactly object surjectivity.
This is not the boundary-generator or trivial Kan fibration characterization. -/
set_option warningAsError false
open CategoryTheory MonoidalCategory Limits
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

theorem exists_daggerObjectGenerator :
    ∃ (E T : DaggerSimplicialCat.{u, u}) (j : E ⟶ T),
      Nonempty (IsInitial E) ∧ Nonempty (IsTerminal T) ∧
      (∀ (C D : DaggerSimplicialCat.{u, u}) (p : C ⟶ D),
        HasLiftingProperty j p ↔ Function.Surjective p.obj) := by sorry

end DaggerModels
