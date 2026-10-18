import OriginalRealizedRelativeFunctionTrivialFibrations
import OriginalBorelModelConsequences

/-!
# Original realized parameter products preserve Borel cofibrant actions

For each original realized subcomplex inclusion with locally compact source
and target, the relative function map of a Borel trivial fibration is again
trivial. Lifting from the native initial arrow of a cofibrant action proves
the original tensor inclusion is a Borel cofibration. The initial pushout
and its arrow are identified explicitly; no underlying-to-Borel implication
is used.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory DaggerOriginalBorelModelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalLocallyCompactTensorAdjunction
open DaggerOriginalLocallyCompactActionTensorAdjunction
open DaggerOriginalRealizedRelativeFunctionTrivialFibrations DaggerOriginalBorelModelCategory
open DaggerOriginalEC2BorelModelCompatibility

universe u

namespace DaggerOriginalRealizedParameterActionCofibrations

noncomputable section

instance actionTensor_isLeftAdjoint (K : LocallyCompactTopCat.{u}) :
    (locallyCompactActionTensor.obj K).IsLeftAdjoint :=
  (locallyCompactActionAdjunction.adj K).isLeftAdjoint

/-- Both sides of this original parameter map are preserved initial objects. -/
instance initialTensorComparison_isIso {A B : LocallyCompactTopCat.{u}} (i : A ⟶ B) :
    IsIso ((locallyCompactActionTensor.map i).app (⊥_ (Action TopCat.{u} C2.{u}))) := by
  let hA := IsInitial.isInitialObj (locallyCompactActionTensor.obj A) _ initialIsInitial
  let hB := IsInitial.isInitialObj (locallyCompactActionTensor.obj B) _ initialIsInitial
  let e := hA.uniqueUpToIso hB
  have he : (locallyCompactActionTensor.map i).app (⊥_ (Action TopCat.{u} C2.{u})) =
      e.hom := hA.hom_ext _ _
  rw [he]
  infer_instance

/-- The native initial-arrow tensor pushout retains the actual source tensor object. -/
def initialTensorPushout {A B : LocallyCompactTopCat.{u}} (i : A ⟶ B)
    (E : Action TopCat.{u} C2.{u}) :
    Functor.PushoutObjObj locallyCompactActionTensor i (initial.to E) where
  pt := (locallyCompactActionTensor.obj A).obj E
  inl := inv ((locallyCompactActionTensor.map i).app (⊥_ (Action TopCat.{u} C2.{u}))) ≫
    (locallyCompactActionTensor.obj A).map (initial.to E)
  inr := 𝟙 _
  isPushout := IsPushout.of_horiz_isIso ⟨by simp⟩

/-- The initial-arrow pushout tensor is precisely the original parameter tensor map. -/
theorem initialTensorPushout_ι {A B : LocallyCompactTopCat.{u}} (i : A ⟶ B)
    (E : Action TopCat.{u} C2.{u}) :
    (initialTensorPushout i E).ι = (locallyCompactActionTensor.map i).app E := by
  have h := Functor.PushoutObjObj.inr_ι (initialTensorPushout i E)
  change (𝟙 _) ≫ (initialTensorPushout i E).ι = _ at h
  simpa only [Category.id_comp] using h

/-- The original realized parameter inclusion tensored with a Borel cofibrant action is Borel cof.
-/
theorem realizedParameterTensor_cofibration {Y : SSet.{u}} (B : Y.Subcomplex)
    [LocallyCompactSpace (SSet.toTop.obj Y)]
    [LocallyCompactSpace (SSet.toTop.obj B.toSSet)]
    (E : Action TopCat.{u} C2.{u}) [IsCofibrant E] :
    Cofibration ((locallyCompactActionTensor.map (realizedParameterInclusion B)).app E) := by
  rw [cofibration_iff_original]
  intro X Z p hp
  have h := (borelTrivialFibrations_iff p).1 hp
  have : Fibration p := (fibration_iff_underlying p).2 h.1
  have : WeakEquivalence p := (weakEquivalence_iff_underlying p).2 h.2
  let r := Functor.PullbackObjObj.ofHasPullback locallyCompactActionIhom
    (realizedParameterInclusion B) p
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).1
    (relativeActionFunction_trivialFibration B p r)
  have : Fibration r.π := hf
  have : WeakEquivalence r.π := hw
  have : Cofibration (initial.to E) := (isCofibrant_iff E).1 inferInstance
  have hl : HasLiftingProperty (initial.to E) r.π := inferInstance
  have hl' := (actionPushout_lifting_iff (realizedParameterInclusion B) (initial.to E) p
    (initialTensorPushout _ E) r).2 hl
  rwa [initialTensorPushout_ι] at hl'

end

end DaggerOriginalRealizedParameterActionCofibrations
