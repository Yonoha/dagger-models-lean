import ActualCounitRightConeHomContractibility
import OriginalCounitRightConeQFunctorReconciled

/-! The actual original Q diagram has weak augmentation and weak transition maps. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeQFunctor
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualCounitRightConeQHomotopicalDiagram

noncomputable section

/-- Every object of the literal cosimplicial Q is weakly contractible. -/
theorem object_toUnit_GW (m : SimplexCategory) : GW (toUnit (QFunctor.{u}.obj m)) :=
  DaggerActualCounitRightConeHomContractibility.Q_toUnit_GW m.len

/-- The canonical original point augmentation is weak in every degree. -/
theorem augmentation_GW (m : SimplexCategory) : GW (augmentation.{u}.app m) := by
  let e := (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u})).uniqueUpToIso
    SSet.stdSimplex.isTerminalObj₀
  have : WeakEquivalence (toUnit (QFunctor.{u}.obj m)) :=
    (weakEquivalence_iff_GW _).2 (object_toUnit_GW m)
  have h : toUnit (QFunctor.{u}.obj m) ≫ e.hom = augmentation.app m :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  apply (weakEquivalence_iff_GW _).1
  rw [← h]
  infer_instance

/-- Every actual original transition map is geometrically weak. -/
theorem transition_GW {m n : SimplexCategory} (f : m ⟶ n) : GW (QFunctor.{u}.map f) := by
  have : WeakEquivalence (augmentation.{u}.app m) :=
    (weakEquivalence_iff_GW _).2 (augmentation_GW m)
  have : WeakEquivalence (augmentation.{u}.app n) :=
    (weakEquivalence_iff_GW _).2 (augmentation_GW n)
  have h : QFunctor.{u}.map f ≫ augmentation.app n = augmentation.app m :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have : WeakEquivalence (QFunctor.{u}.map f ≫ augmentation.app n) := by
    rw [h]
    infer_instance
  exact (weakEquivalence_iff_GW _).1
    (weakEquivalence_of_postcomp (QFunctor.{u}.map f) (augmentation.app n))

end
end DaggerActualCounitRightConeQHomotopicalDiagram
