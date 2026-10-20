import ActualQWeightedAugmentationSkeletonInduction
import ActualRightConeEvaluationWeak
import ActualConeWeightedRealizationFactorization

/-! Cancel the exact weighted augmentation to prove the actual ordinary counit and dagger equivalence. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite Simplicial
open DaggerModels DaggerModels.OrdinaryRigidification DaggerSSetGluing
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerActualRightConeEvaluationWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualRightConeRigidificationWeak
noncomputable section

local instance : ModelCategory DaggerActualRigidificationQuillen.D.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}
local instance : ModelCategory DaggerActualRigidificationQuillen.G.{u} :=
  DaggerActualRigidificationQuillen.modelG.{u}

/-- The full original cone-weighted augmentation is weak for every unchanged cone object. -/
theorem toRealization_GW (D : SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    GW (DaggerActualConeWeightedRealizationFactorization.toRealization D v w) := by
  exact DaggerActualQWeightedAugmentationSkeletonInduction.augmentation_GW
    (DaggerOriginalCounitBNextConeEvaluationIndex.rightConeSimplices D v w)

/-- The literal rigidification comparison is weak, with only the original local Kan hypothesis. -/
theorem coneRigidificationMap_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y))
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) : GW (coneRigidificationMap D v w) := by
  have : WeakEquivalence
      (DaggerActualConeWeightedRealizationFactorization.toRealization D v w) :=
    (weakEquivalence_iff_GW _).2 (toRealization_GW D v w)
  have : WeakEquivalence
      (DaggerActualConeWeightedRealizationFactorization.toRealization D v w ≫
        coneRigidificationMap D v w) :=
    (weakEquivalence_iff_GW _).2
      (DaggerActualConeWeightedRealizationFactorization.composite_GW D v w hD)
  exact (weakEquivalence_iff_GW _).1 (weakEquivalence_of_precomp
    (DaggerActualConeWeightedRealizationFactorization.toRealization D v w)
    (coneRigidificationMap D v w))

/-- The exact formerly outstanding comparison statement now has a proof without extra premises. -/
theorem ordinaryRightConeRigidificationWeak : OrdinaryRightConeRigidificationWeak.{u} :=
  coneRigidificationMap_GW

/-- Every original ordinary counit Hom map is geometrically weak at a locally Kan target. -/
theorem ordinary_counit_local :
    DaggerActualFibrantCounitReduction.OrdinaryCounitLocalGW.{u} :=
  ordinary_counit_local_of_rigidification ordinaryRightConeRigidificationWeak

/-- The unchanged actual dagger rigidification/coherent-nerve adjunction is a Quillen equivalence. -/
theorem isQuillenEquivalence :
    DaggerActualRigidificationQuillen.adjunction.{u}.IsQuillenEquivalence :=
  isQuillenEquivalence_of_rigidification ordinaryRightConeRigidificationWeak

end
end DaggerActualRightConeRigidificationWeak
