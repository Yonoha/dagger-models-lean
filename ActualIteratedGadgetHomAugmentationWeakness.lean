import ActualNecklaceGadgetWeightNaturality

/-! Original P2 proves the exact augmentation of the actual Hom-weighted gadget replacement weak. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerChosenRigidificationNecklace DaggerNativeSimplicialReplacement
open DaggerActualIteratedGadgetHomAugmentation DaggerActualNecklaceGadgetWeightNaturality
open DaggerActualIteratedGadgetWeightedReindex DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualIteratedGadgetHomAugmentationWeakness
noncomputable section

/-- The exact augmentation to C(X)'s original Hom is weak for every X and endpoint pair. -/
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

/-- The original cone-weighted augmentation is weak under only the exact local Kan hypothesis. -/
theorem cone_augmentation_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    GW (coneMap D a b ≫ toOriginalHom (coherentNerve.obj D) a b) := by
  have : WeakEquivalence (coneMap D a b) :=
    (weakEquivalence_iff_GW _).mpr (coneMap_GW D hD a b)
  have : WeakEquivalence (toOriginalHom (coherentNerve.obj D) a b) :=
    (weakEquivalence_iff_GW _).mpr (toOriginalHom_GW _ a b)
  exact (weakEquivalence_iff_GW _).mp inferInstance

end
end DaggerActualIteratedGadgetHomAugmentationWeakness
