import ChallengeActualDaggerQuillenEquivalence
import ActualRightConeRigidificationWeak

/-! Match each independently fixed original map and the original standard-model adjunction. -/
set_option autoImplicit false
open HomotopicalAlgebra
universe u
namespace DaggerActualDaggerQuillenEquivalenceProof
noncomputable section

local instance : ModelCategory DaggerActualRigidificationQuillen.D.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}
local instance : ModelCategory DaggerActualRigidificationQuillen.G.{u} :=
  DaggerActualRigidificationQuillen.modelG.{u}

/-- The original old-data augmentation statement is proved without a weak-comparison premise. -/
theorem augmentation_verified :
    DaggerActualDaggerQuillenEquivalenceChallenge.augmentationStatement.{u} :=
  DaggerActualQWeightedAugmentationSkeletonInduction.augmentation_GW

/-- The original cone statement uses only its original local Kan hypothesis. -/
theorem cone_verified : DaggerActualDaggerQuillenEquivalenceChallenge.coneStatement.{u} :=
  DaggerActualRightConeRigidificationWeak.ordinaryRightConeRigidificationWeak

/-- Verify the unchanged ordinary counit on every original pair of rigidification objects. -/
theorem counit_verified : DaggerActualDaggerQuillenEquivalenceChallenge.counitStatement.{u} :=
  DaggerActualRightConeRigidificationWeak.ordinary_counit_local

/-- Verify the actual Quillen equivalence between the independently fixed standard models. -/
theorem quillen_verified : DaggerActualDaggerQuillenEquivalenceChallenge.quillenStatement.{u} :=
  DaggerActualRightConeRigidificationWeak.isQuillenEquivalence

end
end DaggerActualDaggerQuillenEquivalenceProof
