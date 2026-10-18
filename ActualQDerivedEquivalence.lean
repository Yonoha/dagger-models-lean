import ActualQDualFibrantDerived

/-! The original-Q right derived functor is an equivalence by the proved native weak span. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
open DaggerNativeFibrantOppositeDerivability DaggerActualQDualFibrantDerived
open scoped SSet.modelCategoryQuillen
universe u v w

namespace DaggerActualQDerivedEquivalence
noncomputable section

variable {H : Type w} [Category.{v} H] (L : SSet.{u} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{u})]

/-- Transport the original localization through the native double-op equivalence. -/
def doubleLocalization : SSet.{u}ᵒᵖᵒᵖ ⥤ H := (opOpEquivalence SSet.{u}).functor ⋙ L

/-- The transported functor localizes precisely the native twice-opposite weak class. -/
theorem doubleLocalization_isLocalization :
    (doubleLocalization L).IsLocalization doubleWeak.{u} := by
  refine Functor.IsLocalization.of_equivalence_source L (weakEquivalences SSet.{u})
    (doubleLocalization L) doubleWeak.{u} (opOpEquivalence SSet.{u}).symm ?_ ?_ (Iso.refl L)
  · intro X Y f hf
    exact MorphismProperty.le_isoClosure doubleWeak _ hf
  · intro X Y f hf
    exact Localization.inverts L (weakEquivalences SSet.{u}) f.unop.unop hf

/-- Recover the same native fibrant subcategory from the opposite cofibrant objects. -/
def dualFibrantToNative : (CofibrantObject SSet.{u}ᵒᵖ)ᵒᵖ ⥤ FibrantObject SSet.{u} where
  obj X := ⟨X.unop.obj.unop, isFibrant_unop X.unop.obj⟩
  map f := { hom := f.unop.hom.unop }

/-- The previously proved singular-to-identity natural isomorphism in the native dual domain. -/
def dualSingularIso :
    (dualFibrantInclusion SSet.{u}).functor ⋙ localizedSingular L ≅
      (dualFibrantInclusion SSet.{u}).functor ⋙ doubleLocalization L :=
  Functor.isoWhiskerLeft dualFibrantToNative
    (DaggerActualQKanLocalizedComparison.localizedSingularIso L)

/-- Native fibrant evaluation and the weak span compare the right derived functor to localization. -/
def rightDerivedComparisonIso :
    ((dualFibrantInclusion SSet.{u}).functor ⋙ doubleWeak.Q) ⋙ rightDerived L ≅
      (dualFibrantInclusion SSet.{u}).functor ⋙ doubleLocalization L := by
  let β := Functor.whiskerLeft (dualFibrantInclusion SSet.{u}).functor (rightDerivedUnit L)
  have : IsIso β := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact rightDerivedUnit_isIso L
  exact Functor.associator _ _ _ ≪≫ (asIso β).symm ≪≫ dualSingularIso L

/-- No equivalence assumption is supplied: both restrictions are actual native localizations. -/
theorem rightDerived_isEquivalence : (rightDerived L).IsEquivalence := by
  have := dualFibrantInclusion_isLocalizedEquivalence SSet.{u}
  have := doubleLocalization_isLocalization L
  have := LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (dualFibrantInclusion SSet.{u}) doubleWeak.Q
  have := LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (dualFibrantInclusion SSet.{u}) (doubleLocalization L)
  have : CatCommSq
      (LocalizerMorphism.id ((weakEquivalences (CofibrantObject SSet.{u}ᵒᵖ)).op)).functor
      ((dualFibrantInclusion SSet.{u}).functor ⋙ doubleWeak.Q)
      ((dualFibrantInclusion SSet.{u}).functor ⋙ doubleLocalization L)
      (rightDerived L) := ⟨(rightDerivedComparisonIso L).symm⟩
  have : ((LocalizerMorphism.id ((weakEquivalences (CofibrantObject SSet.{u}ᵒᵖ)).op)).functor ⋙
      (dualFibrantInclusion SSet.{u}).functor ⋙ doubleLocalization L).IsLocalization
      (weakEquivalences (CofibrantObject SSet.{u}ᵒᵖ)).op :=
    Functor.IsLocalization.of_iso _ (Functor.leftUnitor _).symm
  have : (LocalizerMorphism.id
      ((weakEquivalences (CofibrantObject SSet.{u}ᵒᵖ)).op)).IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization _
      ((dualFibrantInclusion SSet.{u}).functor ⋙ doubleLocalization L)
  exact (LocalizerMorphism.id ((weakEquivalences (CofibrantObject SSet.{u}ᵒᵖ)).op)).isEquivalence
    ((dualFibrantInclusion SSet.{u}).functor ⋙ doubleWeak.Q)
    ((dualFibrantInclusion SSet.{u}).functor ⋙ doubleLocalization L) (rightDerived L)

end
end DaggerActualQDerivedEquivalence
