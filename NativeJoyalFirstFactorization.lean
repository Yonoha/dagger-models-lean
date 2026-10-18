import NativeBoundaryJoyalMappingWeak

/-!
# The first factorization for the fixed ordinary Joyal mapping classes

Reuse the established native Kan functorial factorization on ordinary SSet.
Its right factor is mapping-weak and lifts against all monomorphisms, hence
against monomorphisms that satisfy the fixed Joyal weak predicate.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeJoyalMappingTest DaggerNativeBoundaryJoyalMappingWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeJoyalFirstFactorization
noncomputable section

/-- The exact ordinary Joyal fibration candidate, before proving its full model axioms. -/
def candidateFibrations : MorphismProperty SSet.{u} :=
  (MorphismProperty.monomorphisms SSet ⊓ weakCategoricalEquivalences).rlp

/-- Native Kan trivial fibrations lie in the exact first Joyal right-factor classes. -/
theorem kan_trivial_le_candidate_trivial :
    trivialFibrations SSet.{u} ≤ candidateFibrations.{u} ⊓ weakCategoricalEquivalences.{u} := by
  intro X Y p hp
  have hb := (boundary_rlp_iff_trivialFibration p).2 hp
  have hm := boundary_rlp_monomorphisms p hb
  exact ⟨MorphismProperty.antitone_rlp inf_le_left p hm, boundary_rlp_weak p hb⟩

/-- Every original ordinary map has a functorial mono/(fibration-candidate and weak) factorization. -/
def firstFactorization :
    (MorphismProperty.monomorphisms SSet.{u}).FunctorialFactorizationData
      (candidateFibrations.{u} ⊓ weakCategoricalEquivalences.{u}) :=
  (MorphismProperty.functorialFactorizationData (cofibrations SSet.{u})
    (trivialFibrations SSet.{u})).ofLE
      (fun _ _ i hi ↦ (SSet.modelCategoryQuillen.cofibration_iff i).1
        ((cofibration_iff i).2 hi))
      kan_trivial_le_candidate_trivial

instance firstHasFunctorialFactorization :
    (MorphismProperty.monomorphisms SSet.{u}).HasFunctorialFactorization
      (candidateFibrations.{u} ⊓ weakCategoricalEquivalences.{u}) :=
  ⟨⟨firstFactorization⟩⟩

end
end DaggerNativeJoyalFirstFactorization
