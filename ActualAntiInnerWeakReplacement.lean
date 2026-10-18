import ActualAntiInnerJoyalMappingWeak
import NativeInnerQuasicategoryWeakReplacement

/-!
# The full actual anti-involutive replacement preserves and reflects the fixed weak class

Use the actual normal and mapping-weak units, their complete naturality square, and
existing two-out-of-three. Fibration candidates have underlying quasi-categorical
terminal-source objects, without assuming the unproved full DCH model existence.
-/
set_option autoImplicit false
open CategoryTheory Limits DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerActualAntiJoyalMappingWeakProperties
open DaggerActualAntiInnerHornFactorization
universe u
namespace DaggerActualAntiInnerWeakReplacement
noncomputable section

/-- The entire actual replacement functor preserves and reflects the unchanged weak class. -/
theorem replacement_map_weak_iff {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) :
    weakEquivalences (replacement.map f) ↔ weakEquivalences f := by
  have hX : weakEquivalences (unit.app X) :=
    DaggerActualAntiInnerJoyalMappingWeak.unit_weak X
  have hY : weakEquivalences (unit.app Y) :=
    DaggerActualAntiInnerJoyalMappingWeak.unit_weak Y
  have hnat : f ≫ unit.app Y = unit.app X ≫ replacement.map f := unit.naturality f
  constructor
  · intro hf
    have h := weakEquivalences.comp_mem (unit.app X) (replacement.map f) hX hf
    rw [← hnat] at h
    exact weakEquivalences.of_postcomp f (unit.app Y) hY h
  · intro hf
    have h := weakEquivalences.comp_mem f (unit.app Y) hf hY
    rw [hnat] at h
    exact weakEquivalences.of_precomp (unit.app X) (replacement.map f) hX h

/-- Every actual fixed Joyal candidate belongs to the complete actual inner-right class. -/
theorem candidate_inner {X Y : AntiInvolutiveSSet.{u}} (p : X ⟶ Y)
    (hp : DaggerActualAntiJoyalFirstFactorization.candidateFibrations p) : innerFibrations p :=
  (innerFibrations_iff_underlying p).2
    (DaggerNativeInnerQuasicategoryWeakReplacement.candidate_inner p.hom
      (DaggerActualAntiJoyalAdjointLifting.candidate_forget p hp))

/-- The underlying object of a terminal-source candidate is an actual native quasi-category. -/
theorem candidate_terminal_quasicategory {X T : AntiInvolutiveSSet.{u}} (p : X ⟶ T)
    (hT : IsTerminal T) (hp : DaggerActualAntiJoyalFirstFactorization.candidateFibrations p) :
    X.toSSet.Quasicategory :=
  DaggerNativeInnerQuasicategoryWeakReplacement.candidate_terminal_quasicategory p.hom
    (IsTerminal.isTerminalObj antiForget _ hT)
    (DaggerActualAntiJoyalAdjointLifting.candidate_forget p hp)

/-- The same complete actual factorization has genuinely normal-and-weak left factors. -/
def weakInnerFactorization :
    (DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation.normalMonos.{u} ⊓
      weakEquivalences.{u}).FunctorialFactorizationData innerFibrations.{u} :=
  factorization.ofLE (fun _ _ i hi ↦
    ⟨DaggerActualAntiInnerHornFactorization.innerAnodyne_le_normal i hi,
      DaggerActualAntiInnerJoyalMappingWeak.anti_inner_weak i hi⟩) le_rfl

end
end DaggerActualAntiInnerWeakReplacement
