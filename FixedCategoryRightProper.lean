import FixedCategoryHomLimits
import SSetRightProper

/-! Pullback closure for the unchanged all-Hom weak equivalences on the original fixed-O
category. The same original square is evaluated at every ordered pair, retaining both
endpoint transports. Only local SSet fibration/weak-equivalence instances are used. -/

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerFixedCategoryRightProper

/-- The original local weak equivalences are stable under pullback along local fibrations. -/
theorem W_of_isPullback {O : Type u} {E' E B' B : FixedDaggerSimplicialCat O}
    {t : E' ⟶ E} {l : E' ⟶ B'} {r : E ⟶ B} {b : B' ⟶ B}
    (sq : IsPullback t l r b) (hr : DaggerFixedCategoryGenerators.F O r)
    (hb : DaggerFixedCategoryGenerators.W O b) : DaggerFixedCategoryGenerators.W O t := by
  apply (DaggerFixedCategoryGenerators.W_iff_homwise t).2
  intro x y
  let H := DaggerFixedCategoryHomLimits.homEval O x y
  have hr' := (DaggerFixedCategoryGenerators.F_iff_homwise r).1 hr x y
  have hb' := (DaggerFixedCategoryGenerators.W_iff_homwise b).1 hb x y
  have : Fibration (H.map r) := (HomotopicalAlgebra.fibration_iff _).2
    ((DaggerFixedCategoryHomLimits.original_hom_property_iff (fibrations SSet.{u}) r x y).2
      ((HomotopicalAlgebra.fibration_iff _).1 hr'))
  have : WeakEquivalence (H.map b) := (HomotopicalAlgebra.weakEquivalence_iff _).2
    ((DaggerFixedCategoryHomLimits.original_hom_property_iff (weakEquivalences SSet.{u}) b x y).2
      ((HomotopicalAlgebra.weakEquivalence_iff _).1 hb'))
  have ht : WeakEquivalence (H.map t) :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback
      (DaggerFixedCategoryHomLimits.map_isPullback O x y sq)
  exact (HomotopicalAlgebra.weakEquivalence_iff _).2
    ((DaggerFixedCategoryHomLimits.original_hom_property_iff (weakEquivalences SSet.{u}) t x y).1
      ((HomotopicalAlgebra.weakEquivalence_iff _).1 ht))

end DaggerFixedCategoryRightProper
