import ActualQuasicategoryMappingFibres
import OriginalUnitaryCoreConstruction
import ActualDaggerRigidificationQuillen

/-! Frozen FULL manuscript Theorem C: the ORIGINAL standard weak class and SAME unitary core. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalUnitaryCoreConstruction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerChallengeOriginalMainTheoremC

/-- Full faithfulness uses all original ordered pairs of vertices, including equal ones. -/
def FullyFaithful {X Y : DaggerSSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x y : X.toSSet.obj (op ⦋0⦌),
    WeakEquivalence (DaggerActualQuasicategoryMappingFibres.map f.hom ⦋0⦌ x y)

/-- The manuscript's exact condition(2), with the SAME original unitary-core functor. -/
def ConditionTwo {X Y : DaggerSSet.{u}} (f : X ⟶ Y) : Prop :=
  FullyFaithful f ∧ Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f))

/-- The manuscript's exact condition(3), in the original Kan-Quillen weak class. -/
def ConditionThree {X Y : DaggerSSet.{u}} (f : X ⟶ Y) : Prop :=
  FullyFaithful f ∧ WeakEquivalence (unitaryCoreFunctor.map f)

/-- All three conditions for EVERY original dagger quasi-category map; no extra hypotheses. -/
def Statement : Prop :=
  ∀ {X Y : DaggerSSet.{u}} [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory] (f : X ⟶ Y),
    (DaggerJoyalWeakProperties.standardJoyalWeakEquivalences f ↔ ConditionTwo f) ∧
    (DaggerJoyalWeakProperties.standardJoyalWeakEquivalences f ↔ ConditionThree f)

end DaggerChallengeOriginalMainTheoremC
