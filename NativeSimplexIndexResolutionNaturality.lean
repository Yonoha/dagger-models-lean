import NativeSimplexIndexNerveWeakContractibility
import NativeSimplicialReplacementReindex

/-! Naturality of both exact standard-simplex resolution maps. -/
set_option autoImplicit false
open CategoryTheory Opposite HomotopicalAlgebra
open DaggerNativeSimplexIndexResolution DaggerNativeSimplicialReplacement
open DaggerNativeSimplicialReplacementReindex DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSimplexIndexResolutionNaturality
noncomputable section

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-- Postcompose every whole original simplex map with f, preserving each simplex operator. -/
def indexMap : LiftedIndex X ⥤ LiftedIndex Y :=
  ULiftHom.down.{0, u, u} ⋙ CostructuredArrow.map f ⋙ ULiftHom.up.{0, u, u}

/-- The standard-simplex weights are unchanged by this full index functor. -/
theorem diagram_comp : indexMap f ⋙ diagram Y = diagram X := rfl

/-- Reindex entire chains and retain the entire original parameter simplex. -/
def resolutionMap : DaggerBisimplicialDiagonal.diag (resolution X) ⟶
    DaggerBisimplicialDiagonal.diag (resolution Y) :=
  diagonalReindex (indexMap f) (diagram Y)

/-- The projection square uses the nerve of the literal postcomposition index map. -/
theorem projection_square : resolutionMap f ≫ toLiftedNerve Y =
    toLiftedNerve X ≫ nerveMap (indexMap f) :=
  DaggerNativeSimplicialReplacementReindex.projection_square (indexMap f) (diagram Y)

/-- The augmentation square applies f to the entire original parameter. -/
theorem augmentation_square : resolutionMap f ≫ toOriginal Y = toOriginal X ≫ f := by
  apply NatTrans.ext
  rfl

/-- The exact index nerve map is weak precisely when the original simplicial map is weak. -/
theorem nerveMap_GW_iff : GW (nerveMap (indexMap f)) ↔ GW f := by
  have : WeakEquivalence (toLiftedNerve X) :=
    (weakEquivalence_iff_GW _).mpr (toLiftedNerve_GW X)
  have : WeakEquivalence (toLiftedNerve Y) :=
    (weakEquivalence_iff_GW _).mpr (toLiftedNerve_GW Y)
  have : WeakEquivalence (toOriginal X) := (weakEquivalence_iff_GW _).mpr
    (DaggerNativeSimplexIndexNerveWeakContractibility.toOriginal_GW X)
  have : WeakEquivalence (toOriginal Y) := (weakEquivalence_iff_GW _).mpr
    (DaggerNativeSimplexIndexNerveWeakContractibility.toOriginal_GW Y)
  rw [← weakEquivalence_iff_GW, ← weakEquivalence_iff_GW]
  calc
    WeakEquivalence (nerveMap (indexMap f)) ↔
        WeakEquivalence (toLiftedNerve X ≫ nerveMap (indexMap f)) :=
      (weakEquivalence_precomp_iff _ _).symm
    _ ↔ WeakEquivalence (resolutionMap f ≫ toLiftedNerve Y) := by
      rw [projection_square]
    _ ↔ WeakEquivalence (resolutionMap f) := weakEquivalence_postcomp_iff _ _
    _ ↔ WeakEquivalence (resolutionMap f ≫ toOriginal Y) :=
      (weakEquivalence_postcomp_iff _ _).symm
    _ ↔ WeakEquivalence (toOriginal X ≫ f) := by rw [augmentation_square]
    _ ↔ WeakEquivalence f := weakEquivalence_precomp_iff _ _

end
end DaggerNativeSimplexIndexResolutionNaturality
