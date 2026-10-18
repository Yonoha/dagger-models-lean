import OriginalSimplicialCategoryWholeBarFibreIso

/-!
# The actual native pullback of the original whole bar over the original vertex

Transport the native subcomplex-preimage pullback along the original Hom
coproduct-fibre isomorphism and the original source-point isomorphism.
The resulting four maps are the original Hom coproduct inclusion, its actual
standard-point map, the actual whole bar projection, and the original vertex.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFibre
open DaggerOriginalSimplicialCategoryBarPullback
open DaggerOriginalSimplicialCategoryWholeBarFibreDegree
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarFibrePullback
noncomputable section

/-- The whole strict fibre is the inverse image of the range of the actual original vertex. -/
theorem wholeBarFibre_eq_vertexPreimage (C : SimplicialCat.{u, u}) (x : C.Obj) :
    wholeBarFibre C x =
      (SSet.Subcomplex.range (sourceVertexMap C x)).preimage (barProjection C) :=
  congrArg (fun B ↦ B.preimage (barProjection C)) (sourceVertexSubcomplex_eq_range C x)

/-- The actual whole original Hom coproduct forms the native original vertex pullback. -/
theorem wholeBarHomIsPullback (C : SimplicialCat.{u, u}) (x : C.Obj) :
    IsPullback (wholeBarHomInclusion C x)
      (SSet.stdSimplex.isTerminalObj₀.from (originalHomSum C x))
      (barProjection C) (sourceVertexMap C x) := by
  have h := (sourceVertexSubcomplex C x).preimage_isPullback (barProjection C)
  refine h.of_iso (wholeBarHomFibreIso C x).symm (Iso.refl (bar C))
    (sourceVertexIso C x).symm (Iso.refl (diagonalNerveFunctor.obj C)) ?_ ?_ ?_ ?_
  · rw [← wholeBarHomFibreIso_hom_ι C x]
    simp [wholeBarFibre]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  · simp
  · rw [← sourceVertexIso_hom_ι C x]
    simp

end
end DaggerOriginalSimplicialCategoryWholeBarFibrePullback
