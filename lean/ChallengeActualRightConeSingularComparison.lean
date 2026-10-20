import DaggerModels.OrdinaryTwoObjectCell
import OriginalCounitBNextConeRealizationFactorizationReconciled

/-! The two literal original comparison isomorphisms, without fibrancy hypotheses. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitBNextConeRealizationFactorization
universe u

namespace DaggerActualRightConeSingularComparisonChallenge

def statement : Prop :=
  (∀ n : ℕ, Nonempty (OrdinaryTwoObjectCell.cell (Q.{u} n) ≅
    rigidification.{u}.obj (cone.{u} n))) ∧
  (∀ D : SimplicialCat.{u, u},
    ∀ v w : (coherentNerve.{u}.obj D).obj (op ⦋0⦌),
      IsIso (coneSingularComparison.{u} D v w))

end DaggerActualRightConeSingularComparisonChallenge
