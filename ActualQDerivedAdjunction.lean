import ActualQDerivedEquivalence
import ActualQRealizationWeakEquivalences
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! Derive the literal original-Q adjunction using the proved native model-category data. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerNativeFibrantOppositeDerivability DaggerActualQDualFibrantDerived
open DaggerActualQDerivedEquivalence
open scoped SSet.modelCategoryQuillen
universe u v w

namespace DaggerActualQDerivedAdjunction
noncomputable section

/-- Conjugate the unchanged original realization by the native double-op equivalence. -/
def doubleRealization : SSet.{u}ᵒᵖᵒᵖ ⥤ SSet.{u}ᵒᵖᵒᵖ :=
  (opOpEquivalence SSet.{u}).functor ⋙ realization.{u} ⋙ (opOpEquivalence SSet.{u}).inverse

/-- Conjugate precisely the original singular functor by the same equivalence. -/
def doubleSingular : SSet.{u}ᵒᵖᵒᵖ ⥤ SSet.{u}ᵒᵖᵒᵖ :=
  (opOpEquivalence SSet.{u}).functor ⋙ singular.{u} ⋙ (opOpEquivalence SSet.{u}).inverse

/-- The actual adjunction is transported by composition of native adjunctions. -/
def doubleAdjunction : doubleRealization.{u} ⊣ doubleSingular.{u} :=
  ((opOpEquivalence SSet.{u}).toAdjunction.comp realizationSingularAdjunction.{u}).comp
    (opOpEquivalence SSet.{u}).symm.toAdjunction

/-- The proved preservation of all geometric weak equivalences inverts the full native class. -/
theorem realization_inverts : doubleWeak.{u}.IsInvertedBy (doubleRealization ⋙ doubleWeak.Q) := by
  intro X Y f hf
  have : WeakEquivalence f.unop.unop := ⟨hf⟩
  have := DaggerActualQRealizationWeakEquivalences.realization_weakEquivalence f.unop.unop
  apply Localization.inverts doubleWeak.Q doubleWeak
  change weakEquivalences SSet.{u} (realization.map f.unop.unop)
  exact mem_weakEquivalences _

variable {H : Type w} [Category.{v} H] (L : SSet.{u} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{u})]

local instance : (doubleLocalization L).IsLocalization doubleWeak.{u} :=
  doubleLocalization_isLocalization L

/-- The left derived functor is the native localization lift of the actual realization. -/
def leftDerived : H ⥤ doubleWeak.{u}.Localization :=
  have := doubleLocalization_isLocalization L
  Localization.lift (doubleRealization ⋙ doubleWeak.Q) realization_inverts (doubleLocalization L)

/-- Its comparison is the native localization-factorization isomorphism. -/
def leftDerivedComparisonIso :
    doubleLocalization L ⋙ leftDerived L ≅ doubleRealization ⋙ doubleWeak.{u}.Q :=
  have := doubleLocalization_isLocalization L
  Localization.fac (doubleRealization ⋙ doubleWeak.Q) realization_inverts (doubleLocalization L)

/-- The left comparison retains the literal native factorization map. -/
def α : doubleLocalization L ⋙ leftDerived L ⟶ doubleRealization ⋙ doubleWeak.{u}.Q :=
  (leftDerivedComparisonIso L).hom

/-- The right comparison retains the literal native total-derived unit. -/
def β : doubleSingular ⋙ doubleLocalization L ⟶ doubleWeak.{u}.Q ⋙ rightDerived L :=
  rightDerivedUnit L

/-- Localization's universal property proves the left derived property. -/
theorem leftDerived_isLeftDerivedFunctor :
    (leftDerived L).IsLeftDerivedFunctor (α L) doubleWeak.{u} := by
  have := doubleLocalization_isLocalization L
  exact Functor.isLeftDerivedFunctor_of_inverts doubleWeak _ (leftDerivedComparisonIso L)

/-- The constructed actual right derived functor has the corresponding universal property. -/
theorem rightDerived_isRightDerivedFunctor :
    (rightDerived L).IsRightDerivedFunctor (β L) doubleWeak.{u} :=
  DaggerActualQDualFibrantDerived.rightDerived_isRightDerivedFunctor L

/-- Postcomposition of the invertible left comparison still gives a left derived functor. -/
theorem leftRight_isLeftDerivedFunctor :
    (leftDerived L ⋙ rightDerived L).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight (α L) (rightDerived L))
      doubleWeak.{u} := by
  have := doubleLocalization_isLocalization L
  exact Functor.isLeftDerivedFunctor_of_inverts doubleWeak _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (leftDerivedComparisonIso L) (rightDerived L))

/-- The right-derived comparison is invertible on every native fibrant resolution. -/
theorem rightLeft_isRightDerivedFunctor :
    (rightDerived L ⋙ leftDerived L).IsRightDerivedFunctor
      (Functor.whiskerRight (β L) (leftDerived L) ≫ (Functor.associator _ _ _).hom)
      doubleWeak.{u} := by
  have := dualFibrantInclusion_isRightDerivabilityStructure SSet.{u}
  have h : (dualFibrantInclusion SSet.{u}).Derives
      ((doubleSingular ⋙ doubleLocalization L) ⋙ leftDerived L) := by
    intro X Y f hf
    have := dualFibrantInclusion_derives L f hf
    change IsIso ((leftDerived L).map
      (((dualFibrantInclusion SSet.{u}).functor ⋙ localizedSingular L).map f))
    infer_instance
  apply h.isRightDerivedFunctor_of_isIso
  intro X
  have := rightDerivedUnit_isIso L X
  change IsIso ((leftDerived L).map ((rightDerivedUnit L).app _) ≫ 𝟙 _)
  infer_instance

/-- Mathlib's derived-adjunction theorem applies with all composition hypotheses proved. -/
def derivedAdjunction : leftDerived L ⊣ rightDerived L :=
  have := doubleLocalization_isLocalization L
  have := leftDerived_isLeftDerivedFunctor L
  have := rightDerived_isRightDerivedFunctor L
  have := leftRight_isLeftDerivedFunctor L
  have := rightLeft_isRightDerivedFunctor L
  doubleAdjunction.derived doubleWeak doubleWeak (α L) (β L)

/-- The actual derived counit is an isomorphism because the proved right derived functor is an equivalence. -/
theorem derivedCounit_isIso : IsIso (derivedAdjunction L).counit := by
  have := rightDerived_isEquivalence L
  infer_instance

end
end DaggerActualQDerivedAdjunction
