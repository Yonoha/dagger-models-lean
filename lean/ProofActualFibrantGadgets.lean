import ChallengeActualFibrantGadgets
import ActualFibrantGadgetOver
import ActualFibrantGadgetVertices
import ActualNerveTrivialFibrationRigidification

/-! Verify the exact gadget statement in the existing full dagger-model/Q context. -/
set_option autoImplicit false
open CategoryTheory DaggerModels OrdinaryRigidification OriginalOrdinaryLocalKanReplacement
open DaggerActualFibrantGadgetData DaggerActualFibrantGadgetExtensions
open DaggerActualFibrantGadgetVertices DaggerActualFibrantGadgetOver
open DaggerActualNerveTrivialFibrationRigidification
universe u
namespace DaggerActualFibrantGadgetsProof

theorem verified : DaggerActualFibrantGadgetsChallenge.statement.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact ⟨gadget_quasicategory X, unit_vertex_bijective X,
      OriginalOrdinaryLocalKanReplacementHom.unit_hom_anodyne (rigidification.obj X)⟩
  · intro D hD
    obtain ⟨r, hr⟩ := exists_retraction D hD
    refine ⟨r, hr, fun X σ ↦ unit_extension D r hr σ,
      fun X Y f σ ↦ extension_naturality D r f σ,
      over D r, overUnit D r hr, ?_, ?_, ?_⟩
    · intro X; rfl
    · intro X Y f; rfl
    · intro X; rfl
  · intro A B p ho hh
    exact ⟨nerve_trivialFibration p ho hh,
      rigidification_nerve_local_and_surjective p ho hh⟩

end DaggerActualFibrantGadgetsProof
