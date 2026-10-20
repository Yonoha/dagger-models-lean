import NativeBoundaryJoyalMappingWeak
import ActualAntiNormalFactorization
import ActualAntiJoyalMappingWeakProperties

/-!
# The first exact Joyal factorization for the original anti-involutive category

The fixed normal class and fixed underlying mapping weak class are retained.
The fibration candidate is their right lifting class; its full model axioms
and agreement with an underlying ordinary fibration class remain separate goals.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerActualAntiNormalBoundaryLifting DaggerActualAntiNormalFactorization
open DaggerActualAntiJoyalMappingWeakProperties
universe u
namespace DaggerActualAntiJoyalFirstFactorization
noncomputable section

/-- The exact class that the required model structure must realize as fibrations. -/
def candidateFibrations : MorphismProperty AntiInvolutiveSSet.{u} :=
  (normalMonos ⊓ weakEquivalences).rlp

/-- Every original normal-right map satisfies the fixed underlying Joyal mapping test. -/
theorem normal_rlp_le_weak : normalMonos.{u}.rlp ≤ weakEquivalences.{u} := by
  intro X Y p hp
  exact DaggerNativeBoundaryJoyalMappingWeak.boundary_rlp_weak p.hom
    ((normal_rlp_iff_underlying_boundary p).1 hp)

/-- Normal-right maps belong to both required classes for the first model factorization. -/
theorem normal_rlp_le_candidate_trivial :
    normalMonos.{u}.rlp ≤ candidateFibrations.{u} ⊓ weakEquivalences.{u} := by
  intro X Y p hp
  exact ⟨MorphismProperty.antitone_rlp inf_le_left p hp, normal_rlp_le_weak p hp⟩

/-- The same original functorial normal decomposition, with its right class strengthened. -/
def firstFactorization :
    normalMonos.{u}.FunctorialFactorizationData
      (candidateFibrations.{u} ⊓ weakEquivalences.{u}) :=
  normalFactorization.ofLE le_rfl normal_rlp_le_candidate_trivial

instance firstHasFunctorialFactorization :
    normalMonos.{u}.HasFunctorialFactorization
      (candidateFibrations.{u} ⊓ weakEquivalences.{u}) :=
  ⟨⟨firstFactorization⟩⟩

/-- Lifting against the complete normal class is the exact all-boundary criterion. -/
theorem normal_rlp_weak_iff_boundary {X Y : AntiInvolutiveSSet.{u}} (p : X ⟶ Y) :
    normalMonos.rlp p ∧ weakEquivalences p ↔
      ∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι p.hom := by
  constructor
  · intro h
    exact (normal_rlp_iff_underlying_boundary p).1 h.1
  · intro h
    have hp := (normal_rlp_iff_underlying_boundary p).2 h
    exact ⟨hp, normal_rlp_le_weak p hp⟩

end
end DaggerActualAntiJoyalFirstFactorization
