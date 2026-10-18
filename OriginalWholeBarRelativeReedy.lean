import OriginalWholeBarBisimplicial
import NativeReedyReplacementFibres

/-! Apply genuine relative Reedy replacement to the entire original bar and original base. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite DaggerModels
open DaggerOriginalWholeBarBisimplicial DaggerNativeReedyRelativeReplacement
open DaggerNativeReedyReplacementFibres DaggerNativeBisimplicialDiagonal
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeReedyFibrantHorizontalMapping
open DaggerOriginalSimplicialCategoryDiagonalNerve DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFunctor DaggerOriginalNerveRowChainData
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeBarRelativeReedy
noncomputable section

def barArrow (C : SimplicialCat.{u, u}) := Arrow.mk (wholeProjection C)
def barArrowMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) : barArrow C ⟶ barArrow D :=
  Arrow.homMk (wholeRowsMap F) (baseRowsMap F) (wholeProjection_natural F)
def replacedBar (C : SimplicialCat.{u, u}) := relativeReplacement.obj (barArrow C)
def replacedBarMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) : replacedBar C ⟶ replacedBar D :=
  relativeReplacement.map (barArrowMap F)

theorem totalUnit_row_trivial (C : SimplicialCat.{u, u}) (h : SimplexCategoryᵒᵖ) :
    trivialCofibrations SSet.{u} ((totalUnit (barArrow C)).app h) :=
  DaggerNativeReedyRelativeReplacement.totalUnit_row_trivial (barArrow C) h

theorem baseUnit_row_trivial (C : SimplicialCat.{u, u}) (h : SimplexCategoryᵒᵖ) :
    trivialCofibrations SSet.{u} ((baseUnit (barArrow C)).app h) :=
  DaggerNativeReedyRelativeReplacement.baseUnit_row_trivial (barArrow C) h

theorem bar_projection_reedy (C : SimplicialCat.{u, u}) :
    ReedyFibration (replacedBar C).hom := projection_reedy (barArrow C)
theorem bar_total_reedy (C : SimplicialCat.{u, u}) :
    ReedyFibrant (replacedBar C).left := total_reedy (barArrow C)
theorem bar_base_reedy (C : SimplicialCat.{u, u}) :
    ReedyFibrant (replacedBar C).right := base_reedy (barArrow C)
theorem bar_total_rows_Kan (C : SimplicialCat.{u, u}) (h : SimplexCategoryᵒᵖ) :
    IsFibrant ((replacedBar C).left.obj h) := total_rows_Kan (barArrow C) h
theorem bar_base_rows_Kan (C : SimplicialCat.{u, u}) (h : SimplexCategoryᵒᵖ) :
    IsFibrant ((replacedBar C).right.obj h) := base_rows_Kan (barArrow C) h

def totalComparison (C : SimplicialCat.{u, u}) :
    bar C ⟶ diagonalFunctor.obj (replacedBar C).left :=
  (wholeDiagonalIso C).inv ≫ diagonalFunctor.map (totalUnit (barArrow C))
def baseComparison (C : SimplicialCat.{u, u}) :
    diagonalNerveFunctor.obj C ⟶ diagonalFunctor.obj (replacedBar C).right :=
  (baseDiagonalIso C).inv ≫ diagonalFunctor.map (baseUnit (barArrow C))
def projection (C : SimplicialCat.{u, u}) := diagonalFunctor.map (replacedBar C).hom

theorem projection_under_iso (C : SimplicialCat.{u, u}) :
    (wholeDiagonalIso C).inv ≫ diagonalFunctor.map (wholeProjection C) =
      barProjection C ≫ (baseDiagonalIso C).inv := by
  apply (cancel_mono (baseDiagonalIso C).hom).mp
  simp only [Category.assoc, wholeProjection_diagonal, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem original_projection_square (C : SimplicialCat.{u, u}) :
    totalComparison C ≫ projection C = barProjection C ≫ baseComparison C := by
  unfold totalComparison projection baseComparison
  have he := congrArg (fun t ↦ (wholeDiagonalIso C).inv ≫ t)
    (diagonal_unit_square (barArrow C))
  have ht := congrArg (fun t ↦ t ≫ diagonalFunctor.map (baseUnit (barArrow C)))
    (projection_under_iso C)
  calc
    _ = (wholeDiagonalIso C).inv ≫
        (diagonalFunctor.map (wholeProjection C) ≫ diagonalFunctor.map
          (baseUnit (barArrow C))) := by simpa only [Category.assoc] using he
    _ = _ := by simpa only [Category.assoc] using ht

theorem inverse_wholeMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    (wholeDiagonalIso C).inv ≫ diagonalFunctor.map (wholeRowsMap F) =
      barMap F ≫ (wholeDiagonalIso D).inv := by
  apply (cancel_mono (wholeDiagonalIso D).hom).mp
  simp only [Category.assoc, wholeMap_diagonal, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem inverse_baseMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    (baseDiagonalIso C).inv ≫ diagonalFunctor.map (baseRowsMap F) =
      diagonalNerveFunctor.map F ≫ (baseDiagonalIso D).inv := by
  apply (cancel_mono (baseDiagonalIso D).hom).mp
  simp only [Category.assoc, baseMap_diagonal, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem totalComparison_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    totalComparison C ≫ diagonalFunctor.map (replacedBarMap F).left =
      barMap F ≫ totalComparison D := by
  calc
    _ = (wholeDiagonalIso C).inv ≫
        (diagonalFunctor.map (totalUnit (barArrow C)) ≫
          diagonalFunctor.map (replacedBarMap F).left) := Category.assoc _ _ _
    _ = (wholeDiagonalIso C).inv ≫
        (diagonalFunctor.map (wholeRowsMap F) ≫
          diagonalFunctor.map (totalUnit (barArrow D))) := by
      simpa only [diagonalFunctor.map_comp] using congrArg
        (fun t ↦ (wholeDiagonalIso C).inv ≫ diagonalFunctor.map t)
        (totalUnit_natural (barArrowMap F))
    _ = ((wholeDiagonalIso C).inv ≫ diagonalFunctor.map (wholeRowsMap F)) ≫
        diagonalFunctor.map (totalUnit (barArrow D)) := (Category.assoc _ _ _).symm
    _ = (barMap F ≫ (wholeDiagonalIso D).inv) ≫
        diagonalFunctor.map (totalUnit (barArrow D)) := by rw [inverse_wholeMap]
    _ = _ := Category.assoc _ _ _

theorem baseComparison_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    baseComparison C ≫ diagonalFunctor.map (replacedBarMap F).right =
      diagonalNerveFunctor.map F ≫ baseComparison D := by
  calc
    _ = (baseDiagonalIso C).inv ≫
        (diagonalFunctor.map (baseUnit (barArrow C)) ≫
          diagonalFunctor.map (replacedBarMap F).right) := Category.assoc _ _ _
    _ = (baseDiagonalIso C).inv ≫
        (diagonalFunctor.map (baseRowsMap F) ≫
          diagonalFunctor.map (baseUnit (barArrow D))) := by
      simpa only [diagonalFunctor.map_comp] using congrArg
        (fun t ↦ (baseDiagonalIso C).inv ≫ diagonalFunctor.map t)
        (baseUnit_natural (barArrowMap F))
    _ = ((baseDiagonalIso C).inv ≫ diagonalFunctor.map (baseRowsMap F)) ≫
        diagonalFunctor.map (baseUnit (barArrow D)) := (Category.assoc _ _ _).symm
    _ = (diagonalNerveFunctor.map F ≫ (baseDiagonalIso D).inv) ≫
        diagonalFunctor.map (baseUnit (barArrow D)) := by rw [inverse_baseMap]
    _ = _ := Category.assoc _ _ _

end
end DaggerOriginalWholeBarRelativeReedy
