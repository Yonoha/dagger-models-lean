import NativeSimplexIndexResolutionNaturality
import ChallengeActualWeightedConeComposite
import ActualQRealizationWeakEquivalences

/-! The unchanged Q-weighted resolution preserves actual weak maps. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerSSetGluing DaggerOriginalProductGadget
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementReindex
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualQWeightedResolutionNaturality
noncomputable section

abbrev weights := DaggerActualWeightedConeCompositeChallenge.diagram.{u}
abbrev toRealization := DaggerActualWeightedConeCompositeChallenge.toRealization.{u}

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-- Every exact original Q weight has the already proved weak terminal collapse. -/
theorem weights_point_GW (X : SSet.{u}) (P : DaggerActualWeightedConeCompositeChallenge.Index X) :
    GW (pointMap ((weights X).obj P)) := by
  let e := pointIsTerminal.{u}.uniqueUpToIso (isTerminalTensorUnit (C := SSet.{u}))
  have : WeakEquivalence (toUnit ((weights X).obj P)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerActualCounitRightConeQHomotopicalDiagram.object_toUnit_GW
        (ULiftHom.down.{0, u, u}.obj P).left)
  have he : toUnit ((weights X).obj P) ≫ e.inv = pointMap ((weights X).obj P) :=
    pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- Postcomposition preserves the whole Q weight and its original operators. -/
theorem weights_comp : DaggerNativeSimplexIndexResolutionNaturality.indexMap f ⋙ weights Y =
    weights X := rfl

/-- Map entire original index chains, keeping each entire Q parameter. -/
def map : DaggerBisimplicialDiagonal.diag (replacement (weights X)) ⟶
    DaggerBisimplicialDiagonal.diag (replacement (weights Y)) :=
  diagonalReindex (DaggerNativeSimplexIndexResolutionNaturality.indexMap f) (weights Y)

/-- Weak preservation follows from the proved standard-simplex comparison. -/
theorem map_GW (hf : GW f) : GW (map f) :=
  diagonalReindex_GW (DaggerNativeSimplexIndexResolutionNaturality.indexMap f) (weights Y)
    ((DaggerNativeSimplexIndexResolutionNaturality.nerveMap_GW_iff f).mpr hf)
    (weights_point_GW Y)

/-- The square uses the fixed original augmentation and the original realized map. -/
theorem augmentation_square : map f ≫ toRealization Y =
    toRealization X ≫ realization.map f := by
  apply NatTrans.ext
  funext q x
  rcases x with ⟨c, t⟩
  let σ := ULiftHom.down.{0, u, u}.obj (c.obj 0)
  change (realizationUnit.app σ.left ≫ realization.map (σ.hom ≫ f)).app q t =
    ((realizationUnit.app σ.left ≫ realization.map σ.hom) ≫ realization.map f).app q t
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Weak contractibility of X transfers to the nerve of the entire lifted simplex index. -/
theorem index_toUnit_GW (X : SSet.{u}) (hX : GW (toUnit X)) :
    GW (toUnit (nerve (DaggerNativeSimplexIndexResolution.LiftedIndex X))) := by
  have : WeakEquivalence (DaggerNativeSimplexIndexResolution.toOriginal X) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerNativeSimplexIndexNerveWeakContractibility.toOriginal_GW X)
  have : WeakEquivalence (toUnit X) := (weakEquivalence_iff_GW _).mpr hX
  have : WeakEquivalence (DaggerNativeSimplexIndexResolution.toLiftedNerve X) :=
    (weakEquivalence_iff_GW _).mpr (DaggerNativeSimplexIndexResolution.toLiftedNerve_GW X)
  have he : DaggerNativeSimplexIndexResolution.toLiftedNerve X ≫
      toUnit (nerve (DaggerNativeSimplexIndexResolution.LiftedIndex X)) =
    DaggerNativeSimplexIndexResolution.toOriginal X ≫ toUnit X :=
    isTerminalTensorUnit.hom_ext _ _
  exact (weakEquivalence_iff_GW _).mp (weakEquivalence_of_precomp_of_fac he)

/-- The full Q-weighted resolution of a weakly contractible X is weakly contractible. -/
theorem resolution_toUnit_GW (X : SSet.{u}) (hX : GW (toUnit X)) :
    GW (toUnit (DaggerBisimplicialDiagonal.diag (replacement (weights X)))) := by
  have : WeakEquivalence (diagonalProjection (weights X)) :=
    (weakEquivalence_iff_GW _).mpr (diagonalProjection_GW (weights X) (weights_point_GW X))
  have : WeakEquivalence (toUnit (nerve (DaggerActualWeightedConeCompositeChallenge.Index X))) :=
    (weakEquivalence_iff_GW _).mpr (index_toUnit_GW X hX)
  have he : diagonalProjection (weights X) ≫
      toUnit (nerve (DaggerActualWeightedConeCompositeChallenge.Index X)) =
    toUnit (DaggerBisimplicialDiagonal.diag (replacement (weights X))) :=
    isTerminalTensorUnit.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- On every standard simplex the unchanged realization augmentation is weak. -/
theorem representable_augmentation_GW (n : SimplexCategory) :
    GW (toRealization (uliftYoneda.{u}.obj n)) := by
  have : WeakEquivalence (toUnit (DaggerBisimplicialDiagonal.diag
      (replacement (weights (uliftYoneda.{u}.obj n))))) :=
    (weakEquivalence_iff_GW _).mpr (resolution_toUnit_GW (uliftYoneda.{u}.obj n)
      (DaggerActualKanSimplexCotensorComparison.simplex_toUnit_GW n.len))
  have : WeakEquivalence (toUnit (realization.obj (uliftYoneda.{u}.obj n))) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerActualQRealizationRepresentableWeakness.representable_toUnit_GW n)
  have he : toRealization (uliftYoneda.{u}.obj n) ≫
      toUnit (realization.obj (uliftYoneda.{u}.obj n)) =
    toUnit (DaggerBisimplicialDiagonal.diag
      (replacement (weights (uliftYoneda.{u}.obj n)))) := isTerminalTensorUnit.hom_ext _ _
  have : WeakEquivalence (toRealization (uliftYoneda.{u}.obj n) ≫
      toUnit (realization.obj (uliftYoneda.{u}.obj n))) := by rw [he]; infer_instance
  exact (weakEquivalence_iff_GW _).mp (weakEquivalence_of_postcomp (toRealization (uliftYoneda.{u}.obj n))
    (toUnit (realization.obj (uliftYoneda.{u}.obj n))))

end
end DaggerActualQWeightedResolutionNaturality
