import ProofActualMainTheoremB
import ActualTaggedWalkingIsoSourceHomotopyReconciled
import OriginalTaggedRightAdjunctionQuillenObstruction

/-! Apply the actual constructed dagger model to the original tagged Quillen obstructions. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerUnitaryInvariance DaggerActualRigidificationQuillen
open DaggerActualTaggedWalkingIsoImageDKObstruction
open DaggerModels.OriginalTaggedReverseAdjunctions
universe u
namespace DaggerActualTaggedObstructionsForStandardDaggerModel
noncomputable section

local instance : ModelCategory DaggerSSet.{u} := modelD.{u}

/-- The constructed standard model has the literal original free cofibrations. -/
theorem dagger_cofibration_iff {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    Cofibration f ↔ DaggerSSet.FreeCofibration f := by
  rw [cofibration_iff, source_cof]

/-- Its actual weak class is created by the exact original dagger rigidification. -/
theorem dagger_weakEquivalence_iff {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ DaggerGlobalDK.daggerDK standardReplacement
      (OrdinaryRigidification.DaggerRigidification.daggerRigidification.map f) := by
  rw [weakEquivalence_iff, source_weak]
  rfl

/-- The literal original left Kan image fails weakness in the actual standard dagger model. -/
theorem imageGenerator_not_weak : ¬ WeakEquivalence imageGenerator.{u} :=
  imageGenerator_not_weakEquivalence standardReplacement dagger_weakEquivalence_iff

variable [ModelCategory AntiInvolutiveSSet.{u}]

/-- Only the exact outstanding DCH walking-generator fact remains as an input. -/
theorem left_not_quillen
    (hgenerator : trivialCofibrations AntiInvolutiveSSet.{u} taggedGenerator.{u}) :
    ¬ leftAdjunction.{u}.IsQuillenAdjunction :=
  leftAdjunction_not_isQuillenAdjunction standardReplacement
    dagger_weakEquivalence_iff hgenerator

/-- The right obstruction uses the proved dagger class and the exact DCH normal class. -/
theorem right_not_quillen
    (hanti : ∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
      Cofibration f ↔ AntiInvolutiveSSet.NormalMono f) :
    ¬ rightAdjunction.{u}.IsQuillenAdjunction :=
  DaggerOriginalTaggedRightAdjunctionQuillenObstruction.rightAdjunction_not_isQuillenAdjunction
    dagger_cofibration_iff hanti

end
end DaggerActualTaggedObstructionsForStandardDaggerModel
