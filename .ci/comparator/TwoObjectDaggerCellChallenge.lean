import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Opposite

/-! Part I `bg.eq.A-univ`: existence of the two-object dagger cell representing an edge map.
All target object pairs are allowed. The representing object is specified up to isomorphism;
this obligation does not assert finite presentability or a model structure. -/
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

def classifyTwoObjectCell {K : SSet.{u}} {C D : DaggerSimplicialCat.{u, u}}
    (x y : C.Obj) (i : K ⟶ (x ⟶[SSet.{u}] y)) (F : Hom C D) :
    Σ a : D.Obj, Σ b : D.Obj, (K ⟶ (a ⟶[SSet.{u}] b)) :=
  ⟨F.obj x, F.obj y, i ≫ F.map x y⟩
end DaggerSimplicialCat

theorem exists_twoObjectDaggerCell (K : SSet.{u}) :
    ∃ (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj)
      (i : K ⟶ (x ⟶[SSet.{u}] y)), ∀ D : DaggerSimplicialCat.{u, u},
      Function.Bijective (DaggerSimplicialCat.classifyTwoObjectCell x y i (D := D)) := by sorry

end DaggerModels
