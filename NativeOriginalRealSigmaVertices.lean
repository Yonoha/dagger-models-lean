import ChallengeOriginalRealSigmaVertices

/-! The SAME original canonical vertices are retained by the four outer weak legs. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerChallengeOriginalRealSigmaVertices DaggerOriginalCotensorPrecompositionWeak
open DaggerNativeOriginalSigmaResolutionSpan DaggerOriginalSimplicialGroupoidCompletionUniversal
universe u
namespace DaggerNativeOriginalRealSigmaVertices
noncomputable section

/-- The original simplicial map sends every original identity edge to that same identity edge. -/
theorem map_sigma {X Y : SSet.{u}} (f : X ⟶ Y) (x : X.obj (op ⦋0⦌)) :
    f.app (op ⦋1⦌) (X.σ (0 : Fin 1) x) = Y.σ (0 : Fin 1) (f.app (op ⦋0⦌) x) :=
  congrFun (f.naturality (SimplexCategory.σ (0 : Fin 1)).op) x

theorem coherent_vertex (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x : C.Obj) :
    (coherentSigmaMap C hC).hom.app (op ⦋0⦌) (vertex C.toSimplicialCat x) =
      cotensorVertex C.toSimplicialCat x := by
  apply (NerveVertices.vertexEquiv
    (originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C.toSimplicialCat)).injective
  simpa only [vertex, cotensorVertex, Equiv.apply_symm_apply] using
    DaggerOriginalCoherentCotensorResolution.comparison_vertex C.toSimplicialCat
      (vertex C.toSimplicialCat x)

theorem ordinary_vertex (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x : C.Obj) :
    (ordinarySigmaMap C hC).hom.app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      cotensorVertex C.toSimplicialCat x := by
  apply (NerveVertices.vertexEquiv
    (originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C.toSimplicialCat)).injective
  simpa only [cotensorVertex, vertex, Equiv.apply_symm_apply] using
    DaggerNativeDegreeCotensorDiagonal.diagonalComparison_vertex C.toSimplicialCat
      (ComposableArrows.mk₀ x)

theorem real_ordinary_vertex (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x : C.Obj) :
    (DaggerNativeRealOrdinaryCotensorComparison.comparison C).hom.app (op ⦋0⦌)
        ((nerve (DaggerOriginalSimplicialDegreeCategory.degreeObjects
          C.toSimplicialCat (op ⦋0⦌))).σ (0 : Fin 1) (ComposableArrows.mk₀ x)) =
      (coherentNerve.obj (originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C.toSimplicialCat)).σ
        (0 : Fin 1) (cotensorVertex C.toSimplicialCat x) := by
  change ((DaggerNativeDegreeCotensorComparison.comparison C.toSimplicialCat).app
    (op ⦋0⦌)).app (op ⦋1⦌) _ = _
  refine Eq.trans (map_sigma
    ((DaggerNativeDegreeCotensorComparison.comparison C.toSimplicialCat).app (op ⦋0⦌))
    (ComposableArrows.mk₀ x)) ?_
  exact congrArg _ (ordinary_vertex C hC x)

theorem real_coherent_vertex (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x : C.Obj) :
    (DaggerNativeRealCoherentCotensorComparison.comparisonAction C).hom.app (op ⦋0⦌)
        ((coherentNerve.obj C.toSimplicialCat).σ (0 : Fin 1) (vertex C.toSimplicialCat x)) =
      (coherentNerve.obj (originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C.toSimplicialCat)).σ
        (0 : Fin 1) (cotensorVertex C.toSimplicialCat x) := by
  change (coherentNerve.map (DaggerNativeCoherentCotensorConstants.constantFunctor
    (SSet.stdSimplex.obj ⦋0⦌) C.toSimplicialCat)).app (op ⦋1⦌)
      ((coherentNerve.obj C.toSimplicialCat).σ (0 : Fin 1)
        (vertex C.toSimplicialCat x)) = _
  refine Eq.trans (map_sigma (coherentNerve.map
    (DaggerNativeCoherentCotensorConstants.constantFunctor
      (SSet.stdSimplex.obj ⦋0⦌) C.toSimplicialCat)) (vertex C.toSimplicialCat x)) ?_
  exact congrArg _ (coherent_vertex C hC x)

end
end DaggerNativeOriginalRealSigmaVertices
