import OriginalWholeBarRelativeReedy
import OriginalSimplicialCategoryWholeBarFibreFunctor

/-! The full original Hom sum enters the relative Reedy fibre at the mapped original vertex. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite DaggerModels
open DaggerOriginalWholeBarRelativeReedy DaggerNativeReedyReplacementFibres
open DaggerNativeSSetFibrationSquareFibreWeak DaggerNativeBisimplicialDiagonal
open DaggerOriginalSimplicialCategoryBarFibre DaggerOriginalSimplicialCategoryBarFibreFunctor
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarFibrePullback
open DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
open DaggerOriginalSimplicialCategoryDiagonalNerve
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeBarReedyStrictFibre
noncomputable section

def point (C : SimplicialCat.{u, u}) (x : C.Obj) := sourceVertexMap C x ≫ baseComparison C

def fibre (C : SimplicialCat.{u, u}) (x : C.Obj) : SSet.{u} :=
  pullback (projection C) (point C x)

def strictComparison (C : SimplicialCat.{u, u}) (x : C.Obj) :
    originalHomSum C x ⟶ fibre C x :=
  pullback.lift (wholeBarHomInclusion C x ≫ totalComparison C)
    (SSet.stdSimplex.isTerminalObj₀.from (originalHomSum C x)) (by
      rw [Category.assoc, original_projection_square, ← Category.assoc,
        (wholeBarHomIsPullback C x).w, Category.assoc]
      rfl)

theorem strictComparison_fst (C : SimplicialCat.{u, u}) (x : C.Obj) :
    strictComparison C x ≫ pullback.fst (projection C) (point C x) =
      wholeBarHomInclusion C x ≫ totalComparison C := by
  simp only [strictComparison, pullback.lift_fst]

theorem strictComparison_snd (C : SimplicialCat.{u, u}) (x : C.Obj) :
    strictComparison C x ≫ pullback.snd (projection C) (point C x) =
      SSet.stdSimplex.isTerminalObj₀.from (originalHomSum C x) := by
  simp only [strictComparison, pullback.lift_snd]

theorem point_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    point C x ≫ diagonalFunctor.map (replacedBarMap F).right = point D (F.obj x) := by
  unfold point
  rw [Category.assoc, baseComparison_natural, ← Category.assoc, sourceVertexMap_natural]

def fibreMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    fibre C x ⟶ fibre D (F.obj x) :=
  DaggerNativeSSetFibrationSquareFibreWeak.fibreMap (projection C) (projection D)
    (diagonalFunctor.map (replacedBarMap F).left)
    (diagonalFunctor.map (replacedBarMap F).right)
    (diagonal_arrow_square (replacedBarMap F)) (point C x) (point D (F.obj x))
    (point_natural F x)

theorem strictComparison_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    strictComparison C x ≫ fibreMap F x =
      originalHomSumMap F x ≫ strictComparison D (F.obj x) := by
  apply pullback.hom_ext
  · simp only [fibreMap, Category.assoc,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst, strictComparison_fst]
    rw [← Category.assoc, strictComparison_fst, Category.assoc, totalComparison_natural]
    simp only [← Category.assoc]
    rw [← wholeBarHomInclusion_natural]
  · apply SSet.stdSimplex.isTerminalObj₀.hom_ext

end
end DaggerOriginalWholeBarReedyStrictFibre
