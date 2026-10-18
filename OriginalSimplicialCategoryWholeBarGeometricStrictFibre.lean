import OriginalSimplicialCategoryWholeBarRealizationFibre

/-!
# The realized original Hom coproduct is the actual geometric strict fibre

The original realized source vertex is a point in the original realized
nerve. The full realized original Hom coproduct is homeomorphic to the exact
inverse image of that point under the actual realized whole-bar projection.
No replacement projection or homotopy-fibre assertion is used.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial DaggerModels Topology
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFibre
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarRealizationFibre
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarGeometricStrictFibre
noncomputable section

/-- The exact point obtained by realizing the original source vertex. -/
def realizedSourceVertex (C : SimplicialCat.{u, u}) (x : C.Obj) :
    SSet.toTop.obj (diagonalNerveFunctor.obj C) :=
  SSet.toTop.map (sourceVertexMap C x) (default : SSet.toTop.obj (Δ[0] : SSet.{u}))

/-- The realized original standard-point map has precisely the original vertex as its image. -/
theorem realizedSourceVertex_range (C : SimplicialCat.{u, u}) (x : C.Obj) :
    Set.range (SSet.toTop.map (sourceVertexMap C x)) = {realizedSourceVertex C x} := by
  ext a
  constructor
  · rintro ⟨t, rfl⟩
    change SSet.toTop.map (sourceVertexMap C x) t = realizedSourceVertex C x
    exact congrArg (SSet.toTop.map (sourceVertexMap C x)) (Subsingleton.elim t default)
  · intro h
    exact ⟨default, h.symm⟩

/-- The native subspace that is the actual strict fibre of the realized whole-bar projection. -/
abbrev geometricWholeBarFibre (C : SimplicialCat.{u, u}) (x : C.Obj) :=
  {a : SSet.toTop.obj (bar C) //
    SSet.toTop.map (barProjection C) a = realizedSourceVertex C x}

/-- The full realized original Hom coproduct is homeomorphic to the actual point fibre. -/
def wholeBarHomGeometricFibreHomeomorph (C : SimplicialCat.{u, u}) (x : C.Obj) :
    SSet.toTop.obj (originalHomSum C x) ≃ₜ geometricWholeBarFibre C x := by
  have := sourceVertexMap_mono C x
  let e := TopCat.homeoOfIso (wholeBarHomRealizationPullbackIso C x)
  let e' := TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype
    (SSet.toTop.map (barProjection C)) (SSet.toTop.map (sourceVertexMap C x)))
  let e'' := TopCat.pullbackHomeoPreimage (SSet.toTop.map (barProjection C))
    (SSet.toTop.map (barProjection C)).hom.continuous
    (SSet.toTop.map (sourceVertexMap C x))
    (SSet.closedEmbeddings_toObj_map_of_mono (sourceVertexMap C x)).isEmbedding
  exact (e.trans (e'.trans e'')).trans (Set.homeomorphOfEq (by
    ext a
    change SSet.toTop.map (barProjection C) a ∈
        Set.range (SSet.toTop.map (sourceVertexMap C x)) ↔
      SSet.toTop.map (barProjection C) a = realizedSourceVertex C x
    rw [realizedSourceVertex_range, Set.mem_singleton_iff]))

/-- The geometric homeomorphism's inclusion is exactly the realized original Hom inclusion. -/
theorem wholeBarHomGeometricFibreHomeomorph_val (C : SimplicialCat.{u, u}) (x : C.Obj)
    (a : SSet.toTop.obj (originalHomSum C x)) :
    (wholeBarHomGeometricFibreHomeomorph C x a).val =
      SSet.toTop.map (wholeBarHomInclusion C x) a := by
  change pullback.fst (SSet.toTop.map (barProjection C))
    (SSet.toTop.map (sourceVertexMap C x))
    ((wholeBarHomRealizationPullbackIso C x).hom a) = _
  exact ConcreteCategory.congr_hom (wholeBarHomRealizationPullbackIso_hom_fst C x) a

end
end DaggerOriginalSimplicialCategoryWholeBarGeometricStrictFibre
