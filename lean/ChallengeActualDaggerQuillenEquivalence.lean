import ChallengeActualWeightedConeComposite
import ActualDaggerRigidificationQuillen

/-! Independently fix the old augmentation, literal cone/counit maps and exact standard-model adjunction. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerActualWeightedConeCompositeChallenge
universe u
namespace DaggerActualDaggerQuillenEquivalenceChallenge
noncomputable section

local instance : ModelCategory DaggerActualRigidificationQuillen.D.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}
local instance : ModelCategory DaggerActualRigidificationQuillen.G.{u} :=
  DaggerActualRigidificationQuillen.modelG.{u}

/-- Require the exact old weighted augmentation to be weak for every original X. -/
def augmentationStatement : Prop :=
  ∀ X : SSet.{u}, geometric (toRealization X)

/-- Require weakness of the literal old cone map, with only the original local Kan hypothesis. -/
def coneStatement : Prop :=
  ∀ D : SimplicialCat.{u, u},
    (∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y)) →
    ∀ v w : (coherentNerve.obj D).obj (op ⦋0⦌), geometric (coneRigidificationMap D v w)

/-- Require every actual ordinary counit Hom map at every locally Kan target. -/
def counitStatement : Prop :=
  ∀ D : SimplicialCat.{u, u},
    (∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y)) →
    ∀ a b : (rigidification.obj (coherentNerve.obj D)).Obj,
      geometric ((rigidificationCoherentNerveAdjunction.counit.app D).map a b)

/-- The exact old adjunction between the exact two standard models must be a Quillen equivalence. -/
def quillenStatement : Prop :=
  DaggerActualRigidificationQuillen.adjunction.{u}.IsQuillenEquivalence

end
end DaggerActualDaggerQuillenEquivalenceChallenge
