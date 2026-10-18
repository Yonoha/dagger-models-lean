import OriginalFixedObjectGroupoidColimits
import OriginalFixedObjectModelRecognition

/-!
# Model recognition after proving the original finite colimits

Both original categories now have finite limits and finite colimits without assumptions.
Only the canonical cofibration/trivial-fibration factorization remains an explicit input.
These conditional constructors do not assert that the remaining factorization exists.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
universe u
namespace DaggerOriginalFixedObjectColimitModelRecognition
noncomputable section

/-- Finite colimits are now proved; only the first actual model factorization is required. -/
def strictModelFromFactorization (O : Type u)
    [(strictCofibrations O).HasFactorization (strictFibrations O ⊓ strictWeakEquivalences O)] :
    ModelCategory (FixedStrictGroupoids O) :=
  DaggerOriginalFixedObjectModelRecognition.strictModelRecognition O

/-- The same single remaining factorization suffices for the original dagger model. -/
def strictDaggerModelFromFactorization (O : Type u)
    [(strictDaggerCofibrations O).HasFactorization
      (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O)] :
    ModelCategory (FixedStrictDaggerGroupoids O) :=
  DaggerOriginalFixedObjectModelRecognition.strictDaggerModelRecognition O

end
end DaggerOriginalFixedObjectColimitModelRecognition
