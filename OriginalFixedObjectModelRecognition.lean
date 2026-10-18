import OriginalFixedObjectCofibrations

/-!
# Exact remaining model-recognition obligations on the original strict groupoids

Finite limits, original Homwise model-class closure and weak/fibration
factorization are already proved. Finite colimits and the canonical
cofibration/trivial-fibration factorization remain explicit hypotheses here.
These conditional definitions do not establish those two missing hypotheses
and do not install an unconditional ModelCategory instance.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
universe u
namespace DaggerOriginalFixedObjectModelRecognition
noncomputable section

/-- Conditional actual ordinary model, requiring precisely the two still missing constructions. -/
def strictModelRecognition (O : Type u) [HasFiniteColimits (FixedStrictGroupoids O)]
    [(strictCofibrations O).HasFactorization (strictFibrations O ⊓ strictWeakEquivalences O)] :
    ModelCategory (FixedStrictGroupoids O) := by
  letI : (cofibrations (FixedStrictGroupoids O)).HasFactorization
      (trivialFibrations (FixedStrictGroupoids O)) := by
    change (strictCofibrations O).HasFactorization
      (strictFibrations O ⊓ strictWeakEquivalences O)
    infer_instance
  letI : (weakEquivalences (FixedStrictGroupoids O)).HasFactorization
      (fibrations (FixedStrictGroupoids O)) := by
    change (strictWeakEquivalences O).HasFactorization (strictFibrations O)
    infer_instance
  exact DaggerOriginalJoyalModelRecognition.modelRecognition
    (by rw [strictCof_eq_llp])

/-- Conditional actual dagger model with the same exact two unproved constructions explicit. -/
def strictDaggerModelRecognition (O : Type u)
    [HasFiniteColimits (FixedStrictDaggerGroupoids O)]
    [(strictDaggerCofibrations O).HasFactorization
      (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O)] :
    ModelCategory (FixedStrictDaggerGroupoids O) := by
  letI : (cofibrations (FixedStrictDaggerGroupoids O)).HasFactorization
      (trivialFibrations (FixedStrictDaggerGroupoids O)) := by
    change (strictDaggerCofibrations O).HasFactorization
      (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O)
    infer_instance
  letI : (weakEquivalences (FixedStrictDaggerGroupoids O)).HasFactorization
      (fibrations (FixedStrictDaggerGroupoids O)) := by
    change (strictDaggerWeakEquivalences O).HasFactorization (strictDaggerFibrations O)
    infer_instance
  exact DaggerOriginalJoyalModelRecognition.modelRecognition
    (by rw [strictDaggerCof_eq_llp])

end
end DaggerOriginalFixedObjectModelRecognition
