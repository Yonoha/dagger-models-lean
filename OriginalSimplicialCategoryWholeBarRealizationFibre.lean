import NativeRealizationMonomorphismPullbacks
import OriginalSimplicialCategoryWholeBarFibrePullback

/-!
# The actual strict fibre of the realized original whole bar

Realize the unchanged native whole-bar pullback over the unchanged original
source vertex. The original Hom coproduct is isomorphic to the actual TopCat
pullback, with its exact original inclusion and point map retained.
This is a strict fibre identification, not a homotopy-fibre or quasifibration theorem.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerNativeRealizationMonomorphismPullbacks
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFibre
open DaggerOriginalSimplicialCategoryBarPullback
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarFibrePullback
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarRealizationFibre
noncomputable section

/-- The actual original source vertex is a simplicial monomorphism. -/
theorem sourceVertexMap_mono (C : SimplicialCat.{u, u}) (x : C.Obj) :
    Mono (sourceVertexMap C x) := by
  rw [← sourceVertexIso_hom_ι C x]
  infer_instance

/-- The actual original whole-bar fibre square remains a pullback in TopCat. -/
theorem wholeBarHomRealizationIsPullback (C : SimplicialCat.{u, u}) (x : C.Obj) :
    IsPullback (SSet.toTop.map (wholeBarHomInclusion C x))
      (SSet.toTop.map (SSet.stdSimplex.isTerminalObj₀.from (originalHomSum C x)))
      (SSet.toTop.map (barProjection C)) (SSet.toTop.map (sourceVertexMap C x)) := by
  have := sourceVertexMap_mono C x
  exact realization_isPullback_of_mono (wholeBarHomIsPullback C x)

/-- The full realized original Hom coproduct is the native topological vertex pullback. -/
def wholeBarHomRealizationPullbackIso (C : SimplicialCat.{u, u}) (x : C.Obj) :
    SSet.toTop.obj (originalHomSum C x) ≅
      pullback (SSet.toTop.map (barProjection C)) (SSet.toTop.map (sourceVertexMap C x)) :=
  (wholeBarHomRealizationIsPullback C x).isoPullback

/-- The topological fibre isomorphism retains the exact realized original bar inclusion. -/
theorem wholeBarHomRealizationPullbackIso_hom_fst (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (wholeBarHomRealizationPullbackIso C x).hom ≫
      pullback.fst (SSet.toTop.map (barProjection C))
        (SSet.toTop.map (sourceVertexMap C x)) =
      SSet.toTop.map (wholeBarHomInclusion C x) :=
  (wholeBarHomRealizationIsPullback C x).isoPullback_hom_fst

/-- The topological fibre isomorphism retains the exact realized original point map. -/
theorem wholeBarHomRealizationPullbackIso_hom_snd (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (wholeBarHomRealizationPullbackIso C x).hom ≫
      pullback.snd (SSet.toTop.map (barProjection C))
        (SSet.toTop.map (sourceVertexMap C x)) =
      SSet.toTop.map (SSet.stdSimplex.isTerminalObj₀.from (originalHomSum C x)) :=
  (wholeBarHomRealizationIsPullback C x).isoPullback_hom_snd

end
end DaggerOriginalSimplicialCategoryWholeBarRealizationFibre
