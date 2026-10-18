import NativeInternalHomOppositeTargetComparison
import NativeHoEquivalenceIsoSquare
import NativeQuasicategoryOpposite
import NativeJoyalMappingTest

/-!
# Opposite invariance of the original Joyal mapping weak class

Use the original internal-Hom precomposition maps and the fixed mapping-category
definition. The target comparison, native ho opposite comparison, and native
quasicategory horn reversal supply both directions without a model-structure assumption.
-/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeInternalHomOppositeTargetComparison
open DaggerNativeHoEquivalenceIsoSquare
open DaggerNativeHoOppositeEquivalence
open DaggerNativeQuasicategoryOpposite
open DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeJoyalMappingOpposite

/-- Transport the original precomposition test along an isomorphism of targets. -/
theorem ho_pre_iff_of_target_iso {A B Z Z' : SSet.{u}} (f : A ⟶ B) (e : Z ≅ Z') :
    (SSet.hoFunctor.map ((MonoidalClosed.pre f).app Z)).toFunctor.IsEquivalence ↔
      (SSet.hoFunctor.map ((MonoidalClosed.pre f).app Z')).toFunctor.IsEquivalence := by
  exact ho_equivalence_iff_of_iso_square
    ((MonoidalClosed.pre f).app Z) ((MonoidalClosed.pre f).app Z')
    ((ihom B).mapIso e) ((ihom A).mapIso e)
    ((MonoidalClosed.pre f).naturality e.hom).symm

/-- Compare the exact mapping test on the opposite map with the opposite target. -/
theorem targetTest_opposite_iff {A B : SSet.{u}} (f : A ⟶ B) (Z : SSet.{u}) :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre (SSet.opFunctor.map f)).app Z)).toFunctor.IsEquivalence ↔
      (SSet.hoFunctor.map ((MonoidalClosed.pre f).app Z.op)).toFunctor.IsEquivalence := by
  exact (ho_equivalence_iff_of_iso_square
    (SSet.opFunctor.map ((MonoidalClosed.pre f).app Z.op))
    ((MonoidalClosed.pre (SSet.opFunctor.map f)).app Z)
    (targetComparisonIso B Z) (targetComparisonIso A Z)
    (target_pre_naturality f Z)).symm.trans
      (ho_op_isEquivalence_iff ((MonoidalClosed.pre f).app Z.op))

/-- Actual simplicial opposite preserves the fixed ordinary Joyal mapping weak class. -/
theorem weak_op_of_weak {A B : SSet.{u}} (f : A ⟶ B)
    (hf : weakCategoricalEquivalences f) :
    weakCategoricalEquivalences (SSet.opFunctor.map f) := by
  intro Z hZ
  letI : SSet.Quasicategory Z.op := quasicategory_op Z
  exact (targetTest_opposite_iff f Z).2 (hf Z.op)

/-- The original Joyal mapping weak predicate is equivalent on a map and its opposite. -/
theorem weak_op_iff {A B : SSet.{u}} (f : A ⟶ B) :
    weakCategoricalEquivalences (SSet.opFunctor.map f) ↔ weakCategoricalEquivalences f := by
  constructor
  · intro h Z hZ
    letI : SSet.Quasicategory Z.op := quasicategory_op Z
    have ht :
        (SSet.hoFunctor.map ((MonoidalClosed.pre f).app Z.op.op)).toFunctor.IsEquivalence :=
      (targetTest_opposite_iff f Z.op).1 (h Z.op)
    exact (ho_pre_iff_of_target_iso f (SSet.opFunctorCompOpFunctorIso.app Z)).1 ht
  · exact weak_op_of_weak f

end DaggerNativeJoyalMappingOpposite
