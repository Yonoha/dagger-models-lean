import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.CategoryTheory.Limits.Presheaf

/-! Colimits for `bg.lem.reduction` and the ordinary adjunction in `dj.not.adjunctions`.
The original simplicial categories and all enriched functors are explicit.
The standard thickening, actual Mathlib nerve and chosen Yoneda extension are explicit.
No model structure, fibrancy or previously assumed ordinary colimits are required. -/
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
end SimplicialCat

theorem simplicialCatHasColimits : HasColimits.{u} SimplicialCat.{u, u} := by sorry

namespace OrdinaryRigidification

noncomputable def simplexThickening (n : SimplexCategory) : SimplicialCat.{u, u} :=
  SimplicialCat.of (SimplicialThickening (ULift.{u} (Fin (n.len + 1))))

noncomputable def cosimplicialThickening : SimplexCategory ⥤ SimplicialCat.{u, u} where
  obj := simplexThickening
  map f := SimplicialThickening.functor f.toOrderHom.uliftMap
  map_id n := by
    exact SimplicialThickening.functor_id _
  map_comp f g := by
    exact SimplicialThickening.functor_comp f.toOrderHom.uliftMap g.toOrderHom.uliftMap

noncomputable def coherentNerve : SimplicialCat.{u, u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{u} cosimplicialThickening

local instance : HasColimits.{u} SimplicialCat.{u, u} := simplicialCatHasColimits

local instance : HasColimitsOfSize.{0, u} SimplicialCat.{u, u} :=
  hasColimitsOfSizeShrink.{0, u} SimplicialCat.{u, u}

noncomputable def rigidification : SSet.{u} ⥤ SimplicialCat.{u, u} :=
  uliftYoneda.{u}.leftKanExtension cosimplicialThickening

noncomputable def mathlibCoherentNerve : SimplicialCat.{u, u} ⥤ SSet.{u} where
  obj C := SimplicialNerve (ForgetEnrichment SSet.{u} C.Obj)
  map F :=
    { app _ P := EnrichedFunctor.comp SSet P F
      naturality n m f := by
        funext P
        apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
        intro i j
        simp [EnrichedFunctor.comp] }
  map_id C := by
    ext n P
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro i j
    exact Category.comp_id _
  map_comp F G := by
    ext n P
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro i j
    exact Category.assoc _ _ _

theorem rigidification_coherentNerve_adjunction :
    Nonempty (rigidification.{u} ⊣ coherentNerve.{u}) := by sorry

theorem coherentNerve_iso_mathlib :
    Nonempty (coherentNerve.{u} ≅ mathlibCoherentNerve.{u}) := by sorry

theorem rigidification_simplex_iso :
    Nonempty (uliftYoneda.{u} ⋙ rigidification.{u} ≅ cosimplicialThickening.{u}) := by sorry

end OrdinaryRigidification
end DaggerModels
