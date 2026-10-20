import OriginalTaggedNormalModelInputs
import OriginalTaggedFreeZeroNativeWitness
import OriginalTaggedReverseAdjunctions
import TopCatModelCategory.QuillenAdjunction

/-!
# The actual tagged right adjunction fails the original cofibration comparison

The witness is literally the manuscript's initial map to freeDagger of the
standard point. The tagged restriction and the right Kan adjunction are the
existing actual ones. For any two supplied model structures whose cofibrations
are the original free/normal classes, the actual right adjunction is not Quillen.
No DCH model construction is assumed to have been completed here.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra DaggerModels
open OriginalTaggedReversePresheafInclusion OriginalTaggedNormalModelInputs
open OriginalTaggedReverseAdjunctions DaggerOriginalTaggedFreeZeroNativeWitness
universe u
namespace DaggerOriginalTaggedRightAdjunctionQuillenObstruction
noncomputable section

/-- Every original nonempty dagger object gives a fixed new vertex in its tagged initial map. -/
theorem restricted_initial_not_normalMono (X : DaggerSSet.{u})
    (x : X.toSSet.obj (op ⦋0⦌)) :
    ¬ AntiInvolutiveSSet.NormalMono
      (presheafRoute.map (DaggerSSet.emptyIsInitial.to X)) := by
  intro h
  have hs := (restricted_normalMono_iff_freeCofibration_and_vertex_surjective
    (DaggerSSet.emptyIsInitial.to X)).1 h |>.2
  obtain ⟨a, _⟩ := hs x
  exact PEmpty.elim a

variable [ModelCategory DaggerSSet.{u}] [ModelCategory AntiInvolutiveSSet.{u}]

/-- The literal original free-zero arrow is a model cofibration whose actual image is not. -/
theorem literal_freeZero_model_cofibration_mismatch
    (hdagger : ∀ {X Y : DaggerSSet.{u}} (f : X ⟶ Y),
      Cofibration f ↔ DaggerSSet.FreeCofibration f)
    (hanti : ∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
      Cofibration f ↔ AntiInvolutiveSSet.NormalMono f) :
    Cofibration freeZeroArrow.{u} ∧ ¬ Cofibration (presheafRoute.map freeZeroArrow.{u}) := by
  refine ⟨(hdagger _).2 freeZeroArrow_freeCofibration, ?_⟩
  intro h
  exact restricted_freeZeroArrow_not_normalMono ((hanti _).1 h)

/-- The actual original tagged restriction cannot preserve the prescribed cofibrations. -/
theorem restriction_not_preservesCofibrations
    (hdagger : ∀ {X Y : DaggerSSet.{u}} (f : X ⟶ Y),
      Cofibration f ↔ DaggerSSet.FreeCofibration f)
    (hanti : ∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
      Cofibration f ↔ AntiInvolutiveSSet.NormalMono f) :
    ¬ presheafRoute.{u}.PreservesCofibrations := by
  intro h
  have := h
  obtain ⟨hs, ht⟩ := literal_freeZero_model_cofibration_mismatch hdagger hanti
  have := hs
  exact ht (inferInstanceAs (Cofibration (presheafRoute.map freeZeroArrow.{u})))

/-- The actual tagged restriction/right-Kan adjunction is not Quillen for these exact classes. -/
theorem rightAdjunction_not_isQuillenAdjunction
    (hdagger : ∀ {X Y : DaggerSSet.{u}} (f : X ⟶ Y),
      Cofibration f ↔ DaggerSSet.FreeCofibration f)
    (hanti : ∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
      Cofibration f ↔ AntiInvolutiveSSet.NormalMono f) :
    ¬ rightAdjunction.{u}.IsQuillenAdjunction := by
  intro h
  have := h
  exact restriction_not_preservesCofibrations hdagger hanti
    (Adjunction.IsQuillenAdjunction.preservesCofibrations rightAdjunction)

end
end DaggerOriginalTaggedRightAdjunctionQuillenObstruction
