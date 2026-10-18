import NativeSimplicialReplacement

/-! A literal standard-simplex resolution of the original simplex-index nerve. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerSSetGluing DaggerOriginalProductGadget
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerNativeSimplicialReplacementCells DaggerNativeSimplicialReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSimplexIndexResolution
noncomputable section

abbrev Index (X : SSet.{u}) := SimplexIndex X
abbrev LiftedIndex (X : SSet.{u}) := ULiftHom.{u} (Index X)

def diagram (X : SSet.{u}) : LiftedIndex X ⥤ SSet.{u} where
  obj P := uliftYoneda.obj (ULiftHom.down.{0, u, u}.obj P).left
  map f := uliftYoneda.map f.down.left
  map_id _ := uliftYoneda.map_id _
  map_comp f g := uliftYoneda.map_comp f.down.left g.down.left

/-- Every original simplex supplies its whole original map to X. -/
def diagramAugmentation (X : SSet.{u}) : diagram X ⟶ (Functor.const (LiftedIndex X)).obj X where
  app P := (ULiftHom.down.{0, u, u}.obj P).hom
  naturality {_P _Q} f := (CostructuredArrow.w f.down).trans (Category.comp_id _).symm

/-- Only standard simplices are collapsed in the chain projection. -/
theorem diagram_point_GW (X : SSet.{u}) (P : LiftedIndex X) :
    GW (pointMap ((diagram X).obj P)) := by
  let Y := (diagram X).obj P
  let e := pointIsTerminal.{u}.uniqueUpToIso (isTerminalTensorUnit (C := SSet.{u}))
  have : IsIso e.inv := e.isIso_inv
  have : WeakEquivalence (toUnit Y) := (weakEquivalence_iff_GW _).mpr
    (DaggerActualKanSimplexCotensorComparison.simplex_toUnit_GW
      (ULiftHom.down.{0, u, u}.obj P).left.len)
  have he : toUnit Y ≫ e.inv = pointMap Y := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

def resolution (X : SSet.{u}) : SimplicialObject SSet.{u} := replacement (diagram X)

def toLiftedNerve (X : SSet.{u}) : DaggerBisimplicialDiagonal.diag (resolution X) ⟶
    nerve (LiftedIndex X) := diagonalProjection (diagram X)

/-- The projection maps weakly to the full nerve of the original simplex index. -/
def toNerve (X : SSet.{u}) : DaggerBisimplicialDiagonal.diag (resolution X) ⟶
    nerve (Index X) := toLiftedNerve X ≫ DaggerNativeSmallHomNerveLift.downMap (Index X)

/-- Its other comparison applies the whole original simplex map to the whole parameter. -/
def toOriginal (X : SSet.{u}) : DaggerBisimplicialDiagonal.diag (resolution X) ⟶ X :=
  diagonalAugmentation (diagram X) (diagramAugmentation X)

theorem toLiftedNerve_GW (X : SSet.{u}) : GW (toLiftedNerve X) :=
  diagonalProjection_GW (diagram X) (diagram_point_GW X)

theorem toNerve_GW (X : SSet.{u}) : GW (toNerve X) := by
  have : WeakEquivalence (toLiftedNerve X) := (weakEquivalence_iff_GW _).mpr
    (toLiftedNerve_GW X)
  have : IsIso (DaggerNativeSmallHomNerveLift.downMap (Index X)) :=
    (DaggerNativeSmallHomNerveLift.iso (Index X)).isIso_inv
  apply (weakEquivalence_iff_GW _).mp
  dsimp only [toNerve]
  infer_instance

/-- No simplex is replaced by its vertices or by its endpoint values. -/
theorem toOriginal_cell (X : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (c : (nerve (LiftedIndex X)).obj q)
    (t : ((diagram X).obj (first c)).obj q) :
    (toOriginal X).app q ⟨c, t⟩ =
      (ULiftHom.down.{0, u, u}.obj (first c)).hom.app q t := rfl

end
end DaggerNativeSimplexIndexResolution
