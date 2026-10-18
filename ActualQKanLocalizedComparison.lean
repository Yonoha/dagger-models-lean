import ActualQKanNaturalComparisons
import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant

/-! The proved original-Q weak span becomes a natural isomorphism after localization. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra MonoidalClosed
open DaggerOriginalCounitRightConeQRealizationAdjunction DaggerSSetGluing
open DaggerActualQKanNaturalComparisons DaggerActualQSingularCotensorExchangeIso
open scoped SSet.modelCategoryQuillen
universe u v w

namespace DaggerActualQKanLocalizedComparison
noncomputable section

/-- The actual Q-cotensor diagonal, retaining its native action on all target maps. -/
def diagonalCotensors : SSet.{u} ⥤ SSet.{u} where
  obj X := DaggerBisimplicialDiagonal.diag (DaggerActualQKanCotensorComparison.mixed X)
  map f := DaggerBisimplicialDiagonal.diagMap (mixedMap f)
  map_id X := by
    apply NatTrans.ext
    funext q x
    change ((ihom (DaggerOriginalCounitRightConeQFunctor.QFunctor.obj q.unop)).map
      (𝟙 X)).app q x = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext q x
    change ((ihom (DaggerOriginalCounitRightConeQFunctor.QFunctor.obj q.unop)).map
      (f ≫ g)).app q x = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- The first leg of the literal original-Q span as a natural transformation. -/
def constants : 𝟭 SSet.{u} ⟶ diagonalCotensors where
  app X := DaggerBisimplicialDiagonal.diagMap (DaggerActualQKanCotensorComparison.constants X)
  naturality _ _ f := constants_naturality f

/-- The second leg uses the original singular functor and the proved exchange isomorphism. -/
def singularComparisonNatTrans : singular.{u} ⟶ diagonalCotensors where
  app X := singularComparison X
  naturality _ _ f := singularComparison_naturality f

variable {H : Type w} [Category.{v} H] (L : SSet.{u} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{u})]

/-- Localization inverts the first leg on every actual native fibrant object. -/
theorem localized_constants_isIso (X : FibrantObject SSet.{u}) :
    IsIso (L.map (constants.app X.obj)) := by
  apply Localization.inverts L (weakEquivalences SSet.{u})
  rw [← weakEquivalence_iff, weakEquivalence_iff_GW]
  exact DaggerActualQKanCotensorComparison.diagonal_constants_GW X.obj

/-- Localization also inverts the literal singular comparison on the same object. -/
theorem localized_singularComparison_isIso (X : FibrantObject SSet.{u}) :
    IsIso (L.map (singularComparisonNatTrans.app X.obj)) := by
  apply Localization.inverts L (weakEquivalences SSet.{u})
  rw [← weakEquivalence_iff, weakEquivalence_iff_GW]
  exact singularComparison_GW X.obj

/-- Both legs are natural isomorphisms on the full native subcategory of Kan complexes. -/
def localizedConstantsIso :
    FibrantObject.ι ⋙ L ≅ FibrantObject.ι ⋙ diagonalCotensors ⋙ L := by
  let α := Functor.whiskerLeft FibrantObject.ι (Functor.whiskerRight constants L)
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact localized_constants_isIso L
  exact asIso α

/-- The original singular comparison gives the other natural isomorphism to the same target. -/
def localizedSingularComparisonIso :
    FibrantObject.ι ⋙ singular.{u} ⋙ L ≅ FibrantObject.ι ⋙ diagonalCotensors ⋙ L := by
  let α := Functor.whiskerLeft FibrantObject.ι
    (Functor.whiskerRight singularComparisonNatTrans L)
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact localized_singularComparison_isIso L
  exact asIso α

/-- The actual singular functor and the identity agree naturally after localization on Kan objects. -/
def localizedSingularIso : FibrantObject.ι ⋙ singular.{u} ⋙ L ≅ FibrantObject.ι ⋙ L :=
  localizedSingularComparisonIso L ≪≫ (localizedConstantsIso L).symm

end
end DaggerActualQKanLocalizedComparison
