import NativeDualTheoremAColumnComparison
import NativeOverNerveWeakContractibility

/-! The unconditional source projection and hypothesis-controlled target of dual Theorem A. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalProductGadget DaggerNativeDualTheoremACells DaggerSSetGluing
open DaggerNativeDualTheoremAProjections DaggerNativeDualTheoremAColumnComparison
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeDualTheoremAWeakProjections
noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

theorem columnFamily_point_GW (k : SimplexCategoryᵒᵖ) (c : (nerve C).obj k) :
    GW (pointMap (columnFamily F k c)) :=
  DaggerNativeOverNerveWeakContractibility.point_GW (F.obj (c.obj 0))

/-- The entire original source projection is exactly the original over-family projection. -/
theorem sourceProjection_column (k : SimplexCategoryᵒᵖ) :
    ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map
      (sourceProjection F)).app k =
    (columnIso F k).hom ≫ familyProjection (columnFamily F k) := rfl

theorem sourceProjection_column_GW (k : SimplexCategoryᵒᵖ) :
    GW (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map
      (sourceProjection F)).app k) := by
  have : WeakEquivalence (familyProjection (columnFamily F k)) :=
    (weakEquivalence_iff_GW _).mpr
      (familyProjection_GW (columnFamily F k) (columnFamily_point_GW F k))
  apply (weakEquivalence_iff_GW _).mp
  rw [sourceProjection_column]
  infer_instance

/-- The native columnwise diagonalization gives the full source projection without a hypothesis. -/
theorem sourceDiagonal_GW : GW (sourceDiagonal F) :=
  DaggerOriginalDiagonalGeometric.diagMap_geometric_column
    (sourceProjection F) (sourceProjection_column_GW F)

end
end DaggerNativeDualTheoremAWeakProjections
