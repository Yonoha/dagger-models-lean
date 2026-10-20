import NativeInnerJoyalMappingWeak
import NativeJoyalMappingWeakProperties
import NativeJoyalFirstFactorization

/-!
# The full inner replacement preserves and detects the original Joyal weak predicate

Every unit is now proved weak for all quasi-category targets. The exact naturality square
and two-out-of-three therefore show preservation and reflection for arbitrary original maps.
The ordinary fibration candidate is proved inner-right; its terminal-source objects are
actual native quasi-categories. A weak-inner factorization is not relabelled as a full
second Joyal factorization, since inner-right and the candidate remain different classes.
-/
set_option autoImplicit false
open CategoryTheory Limits MorphismProperty
open DaggerNativeJoyalMappingTest DaggerNativeInnerHornFactorization
open DaggerNativeInnerJoyalMappingWeak
universe u
namespace DaggerNativeInnerQuasicategoryWeakReplacement
noncomputable section

/-- The actual full replacement functor preserves and detects exactly the fixed weak class. -/
theorem replacement_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    weakCategoricalEquivalences (replacement.map f) ↔ weakCategoricalEquivalences f := by
  have hnat : f ≫ unit.app Y = unit.app X ≫ replacement.map f := unit.naturality f
  constructor
  · intro hf
    have h := weakCategoricalEquivalences.comp_mem (unit.app X) (replacement.map f)
      (unit_weak X) hf
    rw [← hnat] at h
    exact weakCategoricalEquivalences.of_postcomp f (unit.app Y) (unit_weak Y) h
  · intro hf
    have h := weakCategoricalEquivalences.comp_mem f (unit.app Y) hf (unit_weak Y)
    rw [hnat] at h
    exact weakCategoricalEquivalences.of_precomp (unit.app X) (replacement.map f)
      (unit_weak X) h

/-- The literal ordinary fibration candidate lifts against every original inner horn. -/
theorem candidate_inner {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : DaggerNativeJoyalFirstFactorization.candidateFibrations p) : innerFibrations p := by
  intro A B i hi
  have hl := le_llp_rlp generators i hi
  exact hp i ⟨innerAnodyne_mono i hl, innerAnodyne_weak i hl⟩

/-- A terminal-source object for the literal candidate is an actual native quasi-category. -/
theorem candidate_terminal_quasicategory {X T : SSet.{u}} (p : X ⟶ T) (hT : IsTerminal T)
    (hp : DaggerNativeJoyalFirstFactorization.candidateFibrations p) : X.Quasicategory :=
  (quasicategory_iff_inner_terminal p hT).2 (candidate_inner p hp)

/-- The same full factorization now has genuinely mono-and-mapping-weak left factors. -/
def weakInnerFactorization :
    (monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences.{u}).FunctorialFactorizationData
      innerFibrations.{u} :=
  factorization.ofLE (fun _ _ i hi ↦ ⟨innerAnodyne_mono i hi, innerAnodyne_weak i hi⟩) le_rfl

end
end DaggerNativeInnerQuasicategoryWeakReplacement
