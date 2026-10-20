import NativeRelativeReedyBisimplicialFibres
import NativeReedyRowFibrations
import NativeBisimplicialDiagonalWeak

/-! Original row fibrations give weak comparison on exact diagonal fibres at bisimplicial points. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeReedyRelativeReplacement
open DaggerNativeRelativeReedyBisimplicialFibres DaggerNativeReedyRowFibrations
open DaggerNativeSSetFibrationSquareFibreWeak DaggerNativeBisimplicialDiagonal
open DaggerNativeBisimplicialDiagonalWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRelativeReedyFibreComparisonWeak
noncomputable section

theorem biComparison_row_weak (f : Arrow BiSSet.{u})
    (hf : ∀ h, Fibration (f.hom.app h)) {K : BiSSet.{u}} (b : K ⟶ f.right)
    (h : SimplexCategoryᵒᵖ) : WeakEquivalence ((biComparison f b).app h) := by
  let E := (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj h
  have : Fibration (E.map f.hom) := hf h
  have : Fibration (E.map (relativeReplacement.obj f).hom) :=
    row_fibration _ (projection_reedy f) h
  have : WeakEquivalence (E.map (totalUnit f)) :=
    ((mem_trivialCofibrations_iff _).mp (totalUnit_row_trivial f h)).2
  have : WeakEquivalence (E.map (baseUnit f)) :=
    ((mem_trivialCofibrations_iff _).mp (baseUnit_row_trivial f h)).2
  have hw : WeakEquivalence (imageComparison E f b) :=
    fibreMap_weakEquivalence _ _ _ _ _ _ _ _
  have : WeakEquivalence
      ((PreservesPullback.iso E f.hom b).hom ≫ imageComparison E f b) := inferInstance
  exact weakEquivalence_of_postcomp_of_fac (imageComparison_square E f b)

theorem diagonalComparison_weak (f : Arrow BiSSet.{u})
    (hf : ∀ h, Fibration (f.hom.app h)) {K : BiSSet.{u}} (b : K ⟶ f.right) :
    WeakEquivalence (imageComparison diagonalFunctor f b) := by
  have : WeakEquivalence (diagonalFunctor.map (biComparison f b)) :=
    diagonal_map_weak _ (biComparison_row_weak f hf b)
  have : WeakEquivalence (diagonalFunctor.map (biComparison f b) ≫
      (PreservesPullback.iso diagonalFunctor (relativeReplacement.obj f).hom
        (b ≫ baseUnit f)).hom) := inferInstance
  exact weakEquivalence_of_precomp_of_fac (imageComparison_square diagonalFunctor f b).symm

end
end DaggerNativeRelativeReedyFibreComparisonWeak
