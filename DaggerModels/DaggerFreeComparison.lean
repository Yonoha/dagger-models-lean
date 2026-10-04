import DaggerModels.DaggerAdjunction
import DaggerModels.FreeDagger
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Comparing the actual composites of free and rigidification adjunctions

Mathlib's uniqueness of left adjoints supplies the mate of the identity of the
literal common right functor. This helper applies to any actual free dagger
adjunction on simplicial categories; it does not postulate existence of one.
-/

open CategoryTheory

universe u

noncomputable section

namespace DaggerModels.OrdinaryRigidification.DaggerFreeComparison

open DaggerNerve DaggerRigidification DaggerAdjunction

/-- Compose the two existing actual adjunctions; the right functor agrees literally. -/
def sourceAdjunction :
    freeDagger.{u} ⋙ daggerRigidification ⊣ DaggerSimplicialCat.forget ⋙ coherentNerve :=
  freeDaggerAdjunction.comp daggerRigidificationCoherentNerveAdjunction

variable {L : SimplicialCat.{u, u} ⥤ DaggerSimplicialCat.{u, u}}
  (freeAdjunction : L ⊣ DaggerSimplicialCat.forget)

/-- Compose the original ordinary rigidification with the specified actual free adjunction. -/
def targetAdjunction :
    rigidification ⋙ L ⊣ DaggerSimplicialCat.forget ⋙ coherentNerve :=
  rigidificationCoherentNerveAdjunction.comp freeAdjunction

/-- The comparison is the existing canonical mate of the identity common right functor. -/
def freeComparison : freeDagger ⋙ daggerRigidification ≅ rigidification ⋙ L :=
  Adjunction.leftAdjointUniq sourceAdjunction (targetAdjunction freeAdjunction)

/-- The canonical comparison respects the actual units of the two composite adjunctions. -/
theorem freeComparison_unit (X : SSet.{u}) :
    sourceAdjunction.unit.app X ≫
        (DaggerSimplicialCat.forget ⋙ coherentNerve).map
          ((freeComparison freeAdjunction).hom.app X) =
      (targetAdjunction freeAdjunction).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app sourceAdjunction
    (targetAdjunction freeAdjunction) X

/-- It also respects the actual counits as full dagger enriched functors. -/
theorem freeComparison_counit (C : DaggerSimplicialCat.{u, u}) :
    (freeComparison freeAdjunction).hom.app (coherentNerve.obj C.toSimplicialCat) ≫
        (targetAdjunction freeAdjunction).counit.app C =
      sourceAdjunction.counit.app C :=
  Adjunction.leftAdjointUniq_hom_app_counit sourceAdjunction
    (targetAdjunction freeAdjunction) C

/-- The original composite Hom correspondence sends the comparison to the other unit. -/
theorem freeComparison_mate (X : SSet.{u}) :
    sourceAdjunction.homEquiv X ((rigidification ⋙ L).obj X)
        ((freeComparison freeAdjunction).hom.app X) =
      (targetAdjunction freeAdjunction).unit.app X :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app sourceAdjunction
    (targetAdjunction freeAdjunction) X

end DaggerModels.OrdinaryRigidification.DaggerFreeComparison
