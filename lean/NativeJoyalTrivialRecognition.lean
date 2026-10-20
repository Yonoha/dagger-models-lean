import NativeWeakRightRecognition
import NativeJoyalMappingWeakProperties

/-!
# The exact ordinary Joyal trivial-candidate recognition gate

Reuse the original native Kan mono / mono-right factorization and the proved
mapping weakness of every mono-right map. The complete original candidate-and-weak
class equals the complete mono-right class, without assuming a Joyal model.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeJoyalMappingTest DaggerNativeJoyalFirstFactorization
open DaggerNativeBoundaryJoyalMappingWeak DaggerNativeWeakRightRecognition
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeJoyalTrivialRecognition
noncomputable section

def monoFactorization :
    (MorphismProperty.monomorphisms SSet.{u}).FunctorialFactorizationData
      (MorphismProperty.monomorphisms SSet.{u}).rlp :=
  (MorphismProperty.functorialFactorizationData (cofibrations SSet.{u})
    (trivialFibrations SSet.{u})).ofLE
      (fun _ _ i hi ↦ (SSet.modelCategoryQuillen.cofibration_iff i).1
        ((cofibration_iff i).2 hi))
      (fun _ _ p hp ↦ boundary_rlp_monomorphisms p
        ((boundary_rlp_iff_trivialFibration p).2 hp))

theorem mono_rlp_weak :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ≤ weakCategoricalEquivalences.{u} := by
  intro A B p hp
  exact boundary_rlp_weak p (fun n ↦
    hp (SSet.boundary n).ι (show Mono (SSet.boundary n).ι from inferInstance))

theorem candidate_trivial_le_mono_rlp :
    candidateFibrations.{u} ⊓ weakCategoricalEquivalences.{u} ≤
      (MorphismProperty.monomorphisms SSet.{u}).rlp :=
  candidate_weak_le_rlp _ _ monoFactorization.factorizationData mono_rlp_weak

theorem candidate_trivial_eq_mono_rlp :
    candidateFibrations.{u} ⊓ weakCategoricalEquivalences.{u} =
      (MorphismProperty.monomorphisms SSet.{u}).rlp :=
  candidate_weak_eq_rlp _ _ monoFactorization.factorizationData mono_rlp_weak

end
end DaggerNativeJoyalTrivialRecognition
