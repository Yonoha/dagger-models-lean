import OriginalJoyalModelRecognition

/-!
# Exact canonical cofibrations of the original fixed-object strict groupoids

The cofibration class is precisely left lifting against the unchanged Homwise
trivial fibrations. Expose that exact native class and its retract stability.
No cofibration/trivial-fibration factorization or model existence is assumed.
-/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidClasses
open scoped DaggerOriginalFixedObjectGroupoidClasses
universe u
namespace DaggerOriginalFixedObjectCofibrations
noncomputable section

/-- The full ordinary canonical cofibration class, with the exact original Homwise targets. -/
def strictCofibrations (O : Type u) : MorphismProperty (FixedStrictGroupoids O) :=
  (strictFibrations O ⊓ strictWeakEquivalences O).llp

/-- Native ordinary cofibrations are the exact canonical lifting class. -/
scoped instance strictCofStructure (O : Type u) :
    CategoryWithCofibrations (FixedStrictGroupoids O) := ⟨strictCofibrations O⟩

/-- The full dagger canonical cofibration class uses the unchanged original dagger maps. -/
def strictDaggerCofibrations (O : Type u) : MorphismProperty (FixedStrictDaggerGroupoids O) :=
  (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O).llp

/-- Native dagger cofibrations are that exact original lifting class. -/
scoped instance strictDaggerCofStructure (O : Type u) :
    CategoryWithCofibrations (FixedStrictDaggerGroupoids O) := ⟨strictDaggerCofibrations O⟩

open scoped DaggerOriginalFixedObjectCofibrations

/-- The original ordinary cofibration class is literally the native trivial-fibration LLP. -/
theorem strictCof_eq_llp (O : Type u) :
    cofibrations (FixedStrictGroupoids O) = (trivialFibrations (FixedStrictGroupoids O)).llp :=
  rfl

/-- The original ordinary cofibrations are stable under native arrow retracts. -/
instance strictCofRetracts (O : Type u) :
    (cofibrations (FixedStrictGroupoids O)).IsStableUnderRetracts := by
  rw [strictCof_eq_llp]
  infer_instance

/-- The original dagger cofibrations are literally the same specified native lifting class. -/
theorem strictDaggerCof_eq_llp (O : Type u) :
    cofibrations (FixedStrictDaggerGroupoids O) =
      (trivialFibrations (FixedStrictDaggerGroupoids O)).llp := rfl

/-- The original dagger cofibrations are stable under native arrow retracts. -/
instance strictDaggerCofRetracts (O : Type u) :
    (cofibrations (FixedStrictDaggerGroupoids O)).IsStableUnderRetracts := by
  rw [strictDaggerCof_eq_llp]
  infer_instance

end
end DaggerOriginalFixedObjectCofibrations
