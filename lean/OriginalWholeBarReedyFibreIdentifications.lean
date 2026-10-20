import OriginalWholeBarBisimplicialPoint
import NativeRelativeReedyBisimplicialFibres

/-! BOTH diagonal pullbacks identify the exact original source point and strict comparison. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite DaggerModels
open DaggerOriginalWholeBarBisimplicialPoint DaggerOriginalWholeBarBisimplicial
open DaggerOriginalWholeBarRelativeReedy DaggerOriginalWholeBarReedyStrictFibre
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarFibrePullback
open DaggerNativeBisimplicialDiagonal DaggerNativeReedyRelativeReplacement
open DaggerNativeRelativeReedyBisimplicialFibres DaggerNativeSSetFibrationSquareFibreWeak
universe u
namespace DaggerOriginalWholeBarReedyFibreIdentifications
noncomputable section

def originalDiagonalIsPullback (C : SimplicialCat.{u, u}) (x : C.Obj) :
    IsPullback (wholeBarHomInclusion C x ≫ (wholeDiagonalIso C).inv)
      (SSet.stdSimplex.isTerminalObj₀.from (originalHomSum C x) ≫ diagonalPointIso.inv)
      (diagonalFunctor.map (wholeProjection C)) (diagonalFunctor.map (sourcePoint C x)) := by
  refine (wholeBarHomIsPullback C x).of_iso (Iso.refl _) (wholeDiagonalIso C).symm
    diagonalPointIso.symm (baseDiagonalIso C).symm ?_ ?_ ?_ ?_
  · simp
  · simp
  · exact (projection_under_iso C).symm
  · exact (sourcePoint_diagonal_inv C x).symm

def originalDiagonalFibreIso (C : SimplicialCat.{u, u}) (x : C.Obj) :
    originalHomSum C x ≅ pullback (diagonalFunctor.map (wholeProjection C))
      (diagonalFunctor.map (sourcePoint C x)) :=
  (originalDiagonalIsPullback C x).isoPullback

theorem originalDiagonalFibreIso_hom_fst (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (originalDiagonalFibreIso C x).hom ≫
      pullback.fst (diagonalFunctor.map (wholeProjection C))
        (diagonalFunctor.map (sourcePoint C x)) =
      wholeBarHomInclusion C x ≫ (wholeDiagonalIso C).inv :=
  (originalDiagonalIsPullback C x).isoPullback_hom_fst

def replacementDiagonalIsPullback (C : SimplicialCat.{u, u}) (x : C.Obj) :
    IsPullback
      (pullback.fst (projection C)
        (diagonalFunctor.map (sourcePoint C x ≫ baseUnit (barArrow C))))
      (pullback.snd (projection C)
        (diagonalFunctor.map (sourcePoint C x ≫ baseUnit (barArrow C))) ≫ diagonalPointIso.hom)
      (projection C) (point C x) := by
  have hb : diagonalFunctor.map (sourcePoint C x ≫ baseUnit (barArrow C)) =
      diagonalPointIso.hom ≫ point C x := by
    rw [← transported_point_diagonal C x, Iso.hom_inv_id_assoc]
  refine (IsPullback.of_hasPullback (projection C)
    (diagonalFunctor.map (sourcePoint C x ≫ baseUnit (barArrow C)))).of_iso
      (Iso.refl _) (Iso.refl _) diagonalPointIso (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simpa using hb

def replacementDiagonalFibreIso (C : SimplicialCat.{u, u}) (x : C.Obj) :
    pullback (projection C)
      (diagonalFunctor.map (sourcePoint C x ≫ baseUnit (barArrow C))) ≅ fibre C x :=
  (replacementDiagonalIsPullback C x).isoPullback

theorem replacementDiagonalFibreIso_hom_fst (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (replacementDiagonalFibreIso C x).hom ≫ pullback.fst (projection C) (point C x) =
      pullback.fst (projection C)
        (diagonalFunctor.map (sourcePoint C x ≫ baseUnit (barArrow C))) :=
  (replacementDiagonalIsPullback C x).isoPullback_hom_fst

theorem strictComparison_factor (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (originalDiagonalFibreIso C x).hom ≫
      imageComparison diagonalFunctor (barArrow C) (sourcePoint C x) ≫
        (replacementDiagonalFibreIso C x).hom = strictComparison C x := by
  have hi : imageComparison diagonalFunctor (barArrow C) (sourcePoint C x) ≫
      pullback.fst (projection C)
        (diagonalFunctor.map (sourcePoint C x ≫ baseUnit (barArrow C))) =
      pullback.fst (diagonalFunctor.map (wholeProjection C))
        (diagonalFunctor.map (sourcePoint C x)) ≫
          diagonalFunctor.map (totalUnit (barArrow C)) :=
    fibreMap_fst _ _ _ _ _ _ _ _
  apply pullback.hom_ext
  · simp only [Category.assoc, replacementDiagonalFibreIso_hom_fst, hi, strictComparison_fst]
    simpa only [Category.assoc, totalComparison] using congrArg
      (fun k ↦ k ≫ diagonalFunctor.map (totalUnit (barArrow C)))
      (originalDiagonalFibreIso_hom_fst C x)
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

end
end DaggerOriginalWholeBarReedyFibreIdentifications
