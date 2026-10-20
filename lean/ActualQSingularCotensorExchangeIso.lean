import ActualSSetCotensorExchange
import ActualQSingularSimplexCotensorDiagonal

/-! The two actual mixed bisimplicial objects are isomorphic in all degrees and operators. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalCounitRightConeQFunctor DaggerSSetGluing
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualSSetCotensorExchange
open DaggerActualQSingularSimplexCotensorDiagonal
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQSingularCotensorExchangeIso
noncomputable section

/-- The native adjunction exchange and native Yoneda equivalence identify each full degree. -/
def degreeEquiv (X : SSet.{u}) (q m : SimplexCategoryᵒᵖ) :
    (((singularMixed X).flip.obj q).obj m) ≃
      ((DaggerActualQKanCotensorComparison.mixed X).obj q).obj m :=
  Equiv.ulift.trans
    ((exchangeHomEquiv (QFunctor.obj q.unop) (SSet.stdSimplex.obj m.unop) X).trans
      SSet.yonedaEquiv)

/-- The identification retains every operator in the standard-simplex direction. -/
theorem degreeEquiv_operator (X : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    {m r : SimplexCategoryᵒᵖ} (i : m ⟶ r) (f : ((singularMixed X).flip.obj q).obj m) :
    degreeEquiv X q r (((singularMixed X).flip.obj q).map i f) =
      ((DaggerActualQKanCotensorComparison.mixed X).obj q).map i (degreeEquiv X q m f) := by
  change SSet.yonedaEquiv (exchangeHomEquiv (QFunctor.obj q.unop)
      (SSet.stdSimplex.obj r.unop) X
      (f.down ≫ (MonoidalClosed.pre (SSet.stdSimplex.map i.unop)).app X)) = _
  rw [exchangeHomEquiv_parameter]
  exact SSet.yonedaEquiv_map_comp i.unop _

/-- Each whole column is an actual simplicial-set isomorphism, without a Kan premise. -/
def columnIso (X : SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    (singularMixed X).flip.obj q ≅ (DaggerActualQKanCotensorComparison.mixed X).obj q :=
  NatIso.ofComponents (fun m ↦ (degreeEquiv X q m).toIso) (by
    intro m r i
    funext f
    exact degreeEquiv_operator X q i f)

/-- The same identifications retain all original Q operators as well. -/
def exchangeIso (X : SSet.{u}) :
    (singularMixed X).flip ≅ DaggerActualQKanCotensorComparison.mixed X :=
  NatIso.ofComponents (columnIso X) (by
    intro q r i
    apply NatTrans.ext
    funext m f
    change SSet.yonedaEquiv (exchangeHomEquiv (QFunctor.obj r.unop)
        (SSet.stdSimplex.obj m.unop) X (QFunctor.map i.unop ≫ f.down)) = _
    rw [exchangeHomEquiv_source, SSet.yonedaEquiv_comp]
    rfl)

/-- The existing flip isomorphism and existing diagonal functor identify the two diagonals. -/
def diagonalExchangeIso (X : SSet.{u}) :
    DaggerBisimplicialDiagonal.diag (singularMixed X) ≅
      DaggerBisimplicialDiagonal.diag (DaggerActualQKanCotensorComparison.mixed X) :=
  (DaggerBisimplicialDiagonal.diagFlipIso (singularMixed X)).symm ≪≫
    DaggerBisimplicialDiagonal.diagonalFunctor.mapIso (exchangeIso X)

/-- The unchanged original singular complex now maps to the same actual Q-cotensor diagonal. -/
def singularComparison (X : SSet.{u}) :
    singular.obj X ⟶
      DaggerBisimplicialDiagonal.diag (DaggerActualQKanCotensorComparison.mixed X) :=
  diagonalComparison X ≫ (diagonalExchangeIso X).hom

/-- Both legs are proved weak; no singular-to-diagonal weakness is supplied as a premise. -/
theorem singularComparison_GW (X : SSet.{u}) [X.KanComplex] : GW (singularComparison X) := by
  have : WeakEquivalence (diagonalComparison X) :=
    (weakEquivalence_iff_GW _).2 (diagonalComparison_GW X)
  apply (weakEquivalence_iff_GW _).1
  dsimp only [singularComparison]
  infer_instance

end
end DaggerActualQSingularCotensorExchangeIso
