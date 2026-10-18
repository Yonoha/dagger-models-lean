import ActualInnerGadgetHomAugmentationWeakness
import ActualGeneralRightConeRigidificationComparison
import ActualQWeightedAugmentationSkeletonInduction

/-! The EXISTING original-Q to original-RigHom comparison is weak for EVERY original quasi X.
The new inner-horn gadgets supply actual cofinality; the original full Q augmentation is reused.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualGeneralRightConeMapping DaggerActualGeneralRightConeRigidificationComparison
open DaggerActualInnerGadgetHomAugmentation DaggerActualInnerGadgetWeightedReindex
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualGeneralRightConeRigidificationWeak
noncomputable section

theorem weighted_factor (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    DaggerActualWeightedConeCompositeChallenge.toRealization (rightMapping X a b) ≫
        DaggerActualGeneralRightConeRigidificationComparison.toRealization X a b =
      coneMap X a b ≫ toOriginalHom X a b := by
  apply NatTrans.ext
  funext q x
  rcases x with ⟨c, t⟩
  let σ := ULiftHom.down.{0, u, u}.obj (c.obj 0)
  change ((realizationUnit.app σ.left ≫ realization.map σ.hom) ≫
      DaggerActualGeneralRightConeRigidificationComparison.toRealization X a b).app q t =
    (leg X a b ((DaggerActualInnerIteratedRightConeIndex.index X a b).obj σ)).app q t
  rw [Category.assoc, toRealization_leg]
  rfl

theorem toRealization_weak (X : SSet.{u}) [X.Quasicategory]
    (a b : X.obj (op ⦋0⦌)) : WeakEquivalence
    (DaggerActualGeneralRightConeRigidificationComparison.toRealization X a b) := by
  let A := DaggerActualWeightedConeCompositeChallenge.toRealization (rightMapping X a b)
  let E := DaggerActualGeneralRightConeRigidificationComparison.toRealization X a b
  have : WeakEquivalence A := (weakEquivalence_iff_GW _).mpr
    (DaggerActualQWeightedAugmentationSkeletonInduction.augmentation_GW (rightMapping X a b))
  have : WeakEquivalence (A ≫ E) := by
    change WeakEquivalence
      (DaggerActualWeightedConeCompositeChallenge.toRealization (rightMapping X a b) ≫
        DaggerActualGeneralRightConeRigidificationComparison.toRealization X a b)
    rw [weighted_factor]
    exact (weakEquivalence_iff_GW _).mpr
      (DaggerActualInnerGadgetHomAugmentationWeakness.cone_augmentation_GW X a b)
  exact weakEquivalence_of_precomp A E

end
end DaggerActualGeneralRightConeRigidificationWeak
