import ActualInnerNecklaceWeightNaturality

/-! The exact original Hom augmentation is weak for the native family and ALL simplicial X. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerNativeSimplicialReplacement
open DaggerActualInnerGadgetHomAugmentation DaggerActualInnerNecklaceWeightNaturality
open DaggerActualInnerGadgetWeightedReindex DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerGadgetHomAugmentationWeakness
noncomputable section

theorem toOriginalHom_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    GW (toOriginalHom X a b) := by
  have : WeakEquivalence (barMap X a b) := (weakEquivalence_iff_GW _).mpr (barMap_GW X a b)
  have : WeakEquivalence (diagonalAugmentation (NecklacesOver.flagDiagram X a b)
      (DaggerActualNecklaceFlagAugmentation.augmentation X a b)) :=
    (weakEquivalence_iff_GW _).mpr (DaggerActualNecklaceFlagAugmentation.augmentation_GW X a b)
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff (barMap X a b) (toOriginalHom X a b)).mp
  rw [augmentation_square]
  infer_instance

theorem cone_augmentation_GW (X : SSet.{u}) [X.Quasicategory]
    (a b : X.obj (op ⦋0⦌)) : GW (coneMap X a b ≫ toOriginalHom X a b) := by
  have : WeakEquivalence (coneMap X a b) :=
    (weakEquivalence_iff_GW _).mpr (coneMap_GW X a b)
  have : WeakEquivalence (toOriginalHom X a b) :=
    (weakEquivalence_iff_GW _).mpr (toOriginalHom_GW X a b)
  exact (weakEquivalence_iff_GW _).mp inferInstance

end
end DaggerActualInnerGadgetHomAugmentationWeakness
