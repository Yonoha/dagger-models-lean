import OriginalOrdinaryLocalKanReplacement
import DaggerModels.OrdinaryRigidification

/-! The actual functorial local Kan gadget and its maps, before any weakness claims. -/

set_option autoImplicit false
open CategoryTheory DaggerModels
open OrdinaryRigidification OriginalOrdinaryLocalKanReplacement
universe u

namespace DaggerActualFibrantGadgetData
noncomputable section

/-- Apply the chosen ordinary local Kan replacement to the original rigidification. -/
def gadget : SSet.{u} ⥤ SSet.{u} := rigidification ⋙ replacement ⋙ coherentNerve

/-- The original adjunction unit followed by the nerve of the actual replacement unit. -/
def unit : 𝟭 SSet.{u} ⟶ gadget where
  app X := rigidificationCoherentNerveAdjunction.unit.app X ≫
    coherentNerve.map (OriginalOrdinaryLocalKanReplacement.unit.app (rigidification.obj X))
  naturality {X Y} f := by
    have hη : f ≫ rigidificationCoherentNerveAdjunction.unit.app Y =
        rigidificationCoherentNerveAdjunction.unit.app X ≫
          coherentNerve.map (rigidification.map f) :=
      rigidificationCoherentNerveAdjunction.unit.naturality f
    have hu : rigidification.map f ≫
        OriginalOrdinaryLocalKanReplacement.unit.app (rigidification.obj Y) =
      OriginalOrdinaryLocalKanReplacement.unit.app (rigidification.obj X) ≫
        replacement.map (rigidification.map f) :=
      OriginalOrdinaryLocalKanReplacement.unit.naturality (rigidification.map f)
    change f ≫ (rigidificationCoherentNerveAdjunction.unit.app Y ≫ _) =
      (rigidificationCoherentNerveAdjunction.unit.app X ≫ _) ≫
        coherentNerve.map (replacement.map (rigidification.map f))
    rw [← Category.assoc, hη, Category.assoc, ← coherentNerve.map_comp,
      hu, coherentNerve.map_comp,
      Category.assoc]

/-- The original adjoint of the entire simplicial map, with no endpoint projection. -/
def adjunct (D : SimplicialCat.{u, u}) {X : SSet.{u}}
    (σ : X ⟶ coherentNerve.obj D) : rigidification.obj X ⟶ D :=
  (rigidificationCoherentNerveAdjunction.homEquiv X D).symm σ

/-- Extend the whole adjoint through replacement and a given enriched retraction. -/
def extension (D : SimplicialCat.{u, u}) (r : replacement.obj D ⟶ D)
    {X : SSet.{u}} (σ : X ⟶ coherentNerve.obj D) : gadget.obj X ⟶ coherentNerve.obj D :=
  coherentNerve.map (replacement.map (adjunct D σ) ≫ r)

end
end DaggerActualFibrantGadgetData
