import OriginalFixedObjectStrictDaggerSmallness
import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Actual small object factorizations for the original strict dagger groupoids

Finite presentability of every actual generator domain supplies the required smallness.
Use native small object argument at aleph0 on the exact original category and classes.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectGroupoidClasses
open DaggerOriginalFixedObjectCofibrations DaggerOriginalFixedObjectStrictDaggerSmallness
universe u
namespace DaggerOriginalFixedObjectStrictDaggerSmallObject
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderbot_aleph0_ord_to_type

/-- The proved original colimits supply all colimits required for transfinite iteration. -/
instance strictHasIteration (O J : Type u) [LinearOrder J] :
    HasIterationOfShape J (FixedStrictDaggerGroupoids O) where

/-- An actual finitely presentable original domain preserves all filtered colimits in Hom. -/
instance domainPreservesFiltered (O J : Type u) [SmallCategory J] [IsFiltered J]
    (A : FixedStrictDaggerGroupoids O) [IsFinitelyPresentable.{u} A] :
    PreservesColimitsOfShape J (coyoneda.obj (Opposite.op A)) := by
  letI : IsCardinalFiltered J Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff J).mpr inferInstance
  exact preservesColimitsOfShape_of_isCardinalPresentable A Cardinal.aleph0.{u} J

/-- Actual boundary domain smallness verifies every native small object argument condition. -/
instance boundaryCardinal (O : Type u) :
    (boundaryGenerators O).IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  preservesColimit i hi _f _hf := by
    haveI := boundary_domain_isFinitelyPresentable O i hi
    infer_instance

/-- Actual horn domain smallness verifies every native small object argument condition. -/
instance hornCardinal (O : Type u) :
    (hornGenerators O).IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  preservesColimit i hi _f _hf := by
    haveI := horn_domain_isFinitelyPresentable O i hi
    infer_instance

/-- The actual functorial first model factorization, for the intended original classes. -/
def boundaryFactorizationData (O : Type u) :
    (strictDaggerCofibrations O).FunctorialFactorizationData
      (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O) := by
  change MorphismProperty.FunctorialFactorizationData
    (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O).llp
    (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O)
  rw [← boundaryGenerators_rlp_eq]
  exact SmallObject.functorialFactorizationData (boundaryGenerators O) Cardinal.aleph0.{u}

/-- The original canonical cofibration and original trivial fibration really factor every arrow. -/
instance strictDaggerCofTrivialFibFactorization (O : Type u) :
    (strictDaggerCofibrations O).HasFactorization
      (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O) := by
  letI : (strictDaggerCofibrations O).HasFunctorialFactorization
      (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O) := ⟨⟨boundaryFactorizationData O⟩⟩
  infer_instance

end
end DaggerOriginalFixedObjectStrictDaggerSmallObject
