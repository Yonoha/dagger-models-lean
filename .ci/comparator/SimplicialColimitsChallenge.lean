import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Limits.HasLimits

/-! Ordinary colimit existence needed for the attachments in Part I `bg.lem.reduction`.
The original simplicial categories and all enriched functors are explicit.
This assertion does not assume a model structure or any existing ordinary colimits. -/
set_option warningAsError false
open CategoryTheory Limits MonoidalCategory
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

theorem simplicialCatHasColimits : HasColimits.{u} SimplicialCat.{u, u} := by sorry

end DaggerModels
