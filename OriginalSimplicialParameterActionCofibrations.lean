import OriginalSimplicialActionRelativeFunctionMaps
import OriginalSimplicialEquivariantParameterTensor

/-!
# Original simplicial parameter products with projectively cofibrant actions

Use the actual initial-arrow tensor pushout and relative equivariant function maps to prove
cofibration preservation at every original subcomplex inclusion and trivial-cofibration
preservation at every horn. The native simplicial braiding identifies these arrows with the
same original parameter product maps used by the enriched mapping adjunction.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalSimplicialActionRelativeFunctionMaps
open DaggerOriginalSimplicialEquivariantParameterTensor
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory

universe u

namespace DaggerOriginalSimplicialParameterActionCofibrations

noncomputable section

/-- Each original parameter tensor is the left side of the lifted native adjunction. -/
instance actionTensor_isLeftAdjoint (A : SSet.{u}) :
    (actionTensor.obj A).IsLeftAdjoint :=
  (actionAdjunction₂.adj A).isLeftAdjoint

/-- Both sides of the original parameter comparison on the initial action are initial. -/
instance initialTensorComparison_isIso {A B : SSet.{u}} (i : A ⟶ B) :
    IsIso ((actionTensor.map i).app (⊥_ (Action SSet.{u} C2.{u}))) := by
  let hA := IsInitial.isInitialObj (actionTensor.obj A) _ initialIsInitial
  let hB := IsInitial.isInitialObj (actionTensor.obj B) _ initialIsInitial
  let e := hA.uniqueUpToIso hB
  have he : (actionTensor.map i).app (⊥_ (Action SSet.{u} C2.{u})) =
      e.hom := hA.hom_ext _ _
  rw [he]
  infer_instance

/-- The initial-arrow tensor pushout has exactly the original source tensor object. -/
def initialTensorPushout {A B : SSet.{u}} (i : A ⟶ B) (E : Action SSet.{u} C2.{u}) :
    Functor.PushoutObjObj actionTensor i (initial.to E) where
  pt := (actionTensor.obj A).obj E
  inl := inv ((actionTensor.map i).app (⊥_ (Action SSet.{u} C2.{u}))) ≫
    (actionTensor.obj A).map (initial.to E)
  inr := 𝟙 _
  isPushout := IsPushout.of_horiz_isIso ⟨by simp⟩

/-- Its induced arrow is the same original parameter tensor map. -/
theorem initialTensorPushout_ι {A B : SSet.{u}} (i : A ⟶ B)
    (E : Action SSet.{u} C2.{u}) :
    (initialTensorPushout i E).ι = (actionTensor.map i).app E := by
  have h := Functor.PushoutObjObj.inr_ι (initialTensorPushout i E)
  change (𝟙 _) ≫ (initialTensorPushout i E).ι = _ at h
  simpa only [Category.id_comp] using h

/-- Every original subcomplex parameter inclusion gives a projective cofibration. -/
theorem parameterTensor_cofibration {A : SSet.{u}} (B : A.Subcomplex)
    (E : Action SSet.{u} C2.{u}) [IsCofibrant E] :
    Cofibration ((actionTensor.map B.ι).app E) := by
  rw [cofibration_iff, ← trivialFibrations_llp (Action SSet.{u} C2.{u})]
  intro X Y p hp
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).1 hp
  have : Fibration p := hf
  have : WeakEquivalence p := hw
  let r := Functor.PullbackObjObj.ofHasPullback actionIhom B.ι p
  obtain ⟨hrf, hrw⟩ := (mem_trivialFibrations_iff _).1
    (relativeActionFunction_trivialFibration B p r)
  have : Fibration r.π := hrf
  have : WeakEquivalence r.π := hrw
  have : Cofibration (initial.to E) := (isCofibrant_iff E).1 inferInstance
  have hl : HasLiftingProperty (initial.to E) r.π := inferInstance
  have hl' := (actionPushout_lifting_iff B.ι (initial.to E) p
    (initialTensorPushout _ E) r).2 hl
  rwa [initialTensorPushout_ι] at hl'

/-- Every original horn parameter gives a projective trivial cofibration. -/
theorem parameterTensor_horn_trivialCofibration (n : ℕ) (i : Fin (n + 2))
    (E : Action SSet.{u} C2.{u}) [IsCofibrant E] :
    trivialCofibrations (Action SSet.{u} C2.{u})
      ((actionTensor.map (SSet.horn (n + 1) i).ι).app E) := by
  rw [← fibrations_llp (Action SSet.{u} C2.{u})]
  intro X Y p hp
  have : Fibration p := (fibration_iff _).2 hp
  let r := Functor.PullbackObjObj.ofHasPullback actionIhom (SSet.horn (n + 1) i).ι p
  obtain ⟨hrf, hrw⟩ := (mem_trivialFibrations_iff _).1
    (relativeActionFunction_horn_trivialFibration n i p r)
  have : Fibration r.π := hrf
  have : WeakEquivalence r.π := hrw
  have : Cofibration (initial.to E) := (isCofibrant_iff E).1 inferInstance
  have hl : HasLiftingProperty (initial.to E) r.π := inferInstance
  have hl' := (actionPushout_lifting_iff (SSet.horn (n + 1) i).ι (initial.to E) p
    (initialTensorPushout _ E) r).2 hl
  rwa [initialTensorPushout_ι] at hl'

/-- The native braiding retains exactly the original action on the E factor. -/
def parameterTensorIso (A : SSet.{u}) (E : Action SSet.{u} C2.{u}) :
    (actionTensor.obj A).obj E ≅ simplicialParameterTensor E A :=
  Action.mkIso (β_ A E.V) (by
    intro g
    ext n ⟨a, e⟩
    rfl)

/-- Parameter braiding compares exactly the two original arrows, including their endpoints. -/
def parameterTensorArrowIso {A B : SSet.{u}} (i : A ⟶ B)
    (E : Action SSet.{u} C2.{u}) :
    Arrow.mk ((actionTensor.map i).app E) ≅ Arrow.mk (simplicialParameterTensorMap E i) :=
  Arrow.isoMk (parameterTensorIso A E) (parameterTensorIso B E) (by
    ext n ⟨a, e⟩
    rfl)

/-- The exact original product parameter map is a cofibration at every subcomplex inclusion. -/
theorem simplicialParameterTensorMap_cofibration {A : SSet.{u}} (B : A.Subcomplex)
    (E : Action SSet.{u} C2.{u}) [IsCofibrant E] :
    Cofibration (simplicialParameterTensorMap E B.ι) := by
  rw [cofibration_iff]
  exact (MorphismProperty.arrow_mk_iso_iff _ (parameterTensorArrowIso B.ι E)).1
    ((cofibration_iff _).1 (parameterTensor_cofibration B E))

/-- The exact original product horn parameter map is a trivial cofibration. -/
theorem simplicialParameterTensorMap_horn_trivialCofibration (n : ℕ) (i : Fin (n + 2))
    (E : Action SSet.{u} C2.{u}) [IsCofibrant E] :
    trivialCofibrations (Action SSet.{u} C2.{u})
      (simplicialParameterTensorMap E (SSet.horn (n + 1) i).ι) :=
  (MorphismProperty.arrow_mk_iso_iff _ (parameterTensorArrowIso _ E)).1
    (parameterTensor_horn_trivialCofibration n i E)

end

end DaggerOriginalSimplicialParameterActionCofibrations
