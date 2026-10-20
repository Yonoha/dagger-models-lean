import OriginalFixedObjectModelProperties
import Mathlib.AlgebraicTopology.ModelCategory.JoyalTrick

/-!
# Model recognition from a weak/fibration factorization and the other model factorization

Reuse Mathlib's Joyal trick dual. The missing cofibration/trivial-fibration
factorization is an explicit assumption; it is not manufactured from a weak
factorization or from model existence. All original exact classes stay fixed.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
universe u v
namespace DaggerOriginalJoyalModelRecognition
noncomputable section

variable {C : Type u} [Category.{v} C]
  [CategoryWithCofibrations C] [CategoryWithFibrations C] [CategoryWithWeakEquivalences C]
  [(weakEquivalences C).HasTwoOutOfThreeProperty]
  [(fibrations C).IsStableUnderComposition]
  [(weakEquivalences C).HasFactorization (fibrations C)]
  [(cofibrations C).HasFactorization (trivialFibrations C)]

/-- Factor the actual weak left leg again; its new left factor is a trivial cofibration. -/
def upgradedFactorization {X Y : C} (f : X ⟶ Y) :
    (trivialCofibrations C).MapFactorizationData (fibrations C) f := by
  let w := MorphismProperty.factorizationData (weakEquivalences C) (fibrations C) f
  let c := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) w.i
  refine
    { Z := c.Z
      i := c.i
      p := c.p ≫ w.p
      fac := by rw [← Category.assoc, c.fac, w.fac]
      hi := ⟨c.hi, ?_⟩
      hp := (fibrations C).comp_mem _ _ c.hp.1 w.hp }
  exact (weakEquivalences C).of_postcomp c.i c.p c.hp.2 (by rw [c.fac]; exact w.hi)

/-- The complete second model factorization follows from the two specified actual inputs. -/
def upgradedHasFactorization :
    (trivialCofibrations C).HasFactorization (fibrations C) :=
  ⟨fun f ↦ ⟨upgradedFactorization f⟩⟩

/-- Exact conditional recognition, retaining finite colimits and the first model factorization
as explicit inputs. -/
def modelRecognition [HasFiniteLimits C] [HasFiniteColimits C]
    [(weakEquivalences C).IsStableUnderRetracts]
    [(fibrations C).IsStableUnderRetracts] [(cofibrations C).IsStableUnderRetracts]
    [(fibrations C).IsStableUnderBaseChange]
    (hcof : cofibrations C ≤ (trivialFibrations C).llp) : ModelCategory C := by
  letI : (trivialCofibrations C).HasFactorization (fibrations C) := upgradedHasFactorization
  have hlift : ∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
      [Cofibration i] [WeakEquivalence p] [Fibration p], HasLiftingProperty i p := by
    intro A B X Y i p hi hp hf
    exact hcof i ((cofibration_iff i).1 hi) p
      ((mem_trivialFibrations_iff p).2 ⟨hf, hp⟩)
  exact
    { cm4b := fun i p hi hf hw ↦ hlift i p
      cm4a := fun i p hi hw hf ↦ ModelCategory.hasLiftingProperty_of_joyalTrickDual hlift i p }

end
end DaggerOriginalJoyalModelRecognition
