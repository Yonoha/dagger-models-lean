import NativeSimplexIndexResolutionColumnComparison

/-! The original standard-simplex resolution is weak on both legs, with no Kan hypothesis. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open DaggerNativeSimplexIndexResolution DaggerNativeSimplicialReplacement
open DaggerNativeSimplexIndexResolutionColumnComparison DaggerSSetGluing
open DaggerOriginalProductGadget DaggerBisimplicialDiagonal
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSimplexIndexNerveWeakContractibility
noncomputable section

/-- The column comparison is the literal original augmentation, not a replacement map. -/
theorem augmentation_column_GW (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) :
    GW (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map (augmentation (diagram X) (diagramAugmentation X))).app k) :=
  columnAugmentation_GW X k

/-- Native columnwise diagonalization proves weakness of the full original augmentation. -/
theorem toOriginal_GW (X : SSet.{u}) : GW (toOriginal X) :=
  DaggerOriginalDiagonalGeometric.diagMap_geometric_column
    (augmentation (diagram X) (diagramAugmentation X)) (augmentation_column_GW X)

/-- Weak contractibility transfers to the full original simplex-index nerve without fibrancy. -/
theorem index_toUnit_GW (X : SSet.{u}) (hX : GW (toUnit X)) :
    GW (toUnit (nerve (Index X))) := by
  have : WeakEquivalence (toOriginal X) :=
    (weakEquivalence_iff_GW _).mpr (toOriginal_GW X)
  have : WeakEquivalence (toUnit X) := (weakEquivalence_iff_GW _).mpr hX
  have : WeakEquivalence (toNerve X) := (weakEquivalence_iff_GW _).mpr (toNerve_GW X)
  have he : toNerve X ≫ toUnit (nerve (Index X)) = toOriginal X ≫ toUnit X :=
    (isTerminalTensorUnit (C := SSet.{u})).hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  exact weakEquivalence_of_precomp_of_fac he

/-- The native point formulation required by Theorem A is the same terminal comparison. -/
theorem index_point_GW (X : SSet.{u}) (hX : GW (toUnit X)) :
    GW (pointMap (nerve (Index X))) := by
  let e := pointIsTerminal.{u}.uniqueUpToIso (isTerminalTensorUnit (C := SSet.{u}))
  have : WeakEquivalence (toUnit (nerve (Index X))) :=
    (weakEquivalence_iff_GW _).mpr (index_toUnit_GW X hX)
  have he : toUnit (nerve (Index X)) ≫ e.inv = pointMap (nerve (Index X)) :=
    pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerNativeSimplexIndexNerveWeakContractibility
