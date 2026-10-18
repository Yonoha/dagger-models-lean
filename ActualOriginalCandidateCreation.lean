import ActualFreeNativeSmithGenerators

/-! Exact full fibration creation by the original antiForget functor. -/
set_option autoImplicit false
open CategoryTheory DaggerModels MorphismProperty
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerActualAntiJoyalMappingWeakProperties DaggerActualAntiNormalFactorization
open DaggerActualFreeNativeSmithGenerators
universe u
namespace DaggerActualOriginalCandidateCreation
noncomputable section

instance normalStableRetracts : normalMonos.{u}.IsStableUnderRetracts := by
  rw [normalMonos_eq_generators_rlp_llp]
  infer_instance

theorem generated_left_le : generators.{u}.rlp.llp ≤ normalMonos.{u} ⊓ weakEquivalences := by
  intro A B f hf
  let q := DaggerActualOriginalAntiJoyalSmithModelData.secondFactorization.factorizationData f
  have hp : generators.rlp q.p :=
    MorphismProperty.antitone_rlp generators_le q.p q.hp
  have : HasLiftingProperty f q.p := hf q.p hp
  exact (normalMonos ⊓ weakEquivalences).of_retract
    (RetractArrow.ofLeftLiftingProperty q.fac) q.hi

theorem full_normal_weak_le_generated :
    normalMonos.{u} ⊓ weakEquivalences ≤ generators.{u}.rlp.llp := by
  intro A B f hf
  let q := factorization.factorizationData f
  have hi := generated_left_le q.i q.hi
  have hpW : weakEquivalences q.p := weakEquivalences.of_precomp q.i q.p hi.2
    (by rw [q.fac]; exact hf.2)
  have hpU := (right_iff_underlying q.p).mp q.hp
  have hpR : normalMonos.rlp q.p := by
    apply (DaggerActualAntiNormalBoundaryLifting.normal_rlp_iff_underlying_boundary q.p).mpr
    have hmono := DaggerNativeJoyalTrivialRecognition.candidate_trivial_le_mono_rlp
      q.p.hom ⟨hpU, hpW⟩
    intro n
    exact hmono (SSet.boundary n).ι (show Mono (SSet.boundary n).ι from inferInstance)
  have : HasLiftingProperty f q.p := hpR f hf.1
  exact generators.rlp.llp.of_retract (RetractArrow.ofLeftLiftingProperty q.fac) q.hi

theorem generated_left_eq : generators.{u}.rlp.llp = normalMonos.{u} ⊓ weakEquivalences :=
  le_antisymm generated_left_le full_normal_weak_le_generated

theorem full_candidate_eq_generated :
    DaggerActualAntiJoyalFirstFactorization.candidateFibrations.{u} = generators.{u}.rlp := by
  rw [DaggerActualAntiJoyalFirstFactorization.candidateFibrations, ← generated_left_eq,
    MorphismProperty.rlp_llp_rlp]

theorem candidate_iff_underlying {X Y : AntiInvolutiveSSet.{u}} (p : X ⟶ Y) :
    DaggerActualAntiJoyalFirstFactorization.candidateFibrations p ↔
      DaggerNativeJoyalFirstFactorization.candidateFibrations p.hom := by
  rw [full_candidate_eq_generated]
  exact right_iff_underlying p

end
end DaggerActualOriginalCandidateCreation
