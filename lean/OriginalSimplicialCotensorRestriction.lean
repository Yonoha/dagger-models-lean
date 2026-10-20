import OriginalFixedObjectCotensorPoints
import TopCatModelCategory.SSet.AnodyneExtensionsAdjunctions
import TopCatModelCategory.ModelCategorySSet

/-!
# Actual simplicial cotensor restriction fibrations

Internal Hom into a Kan complex sends a monomorphism of parameters to a
fibration. An anodyne parameter gives a trivial fibration. Reduce to the native
relative internal-Hom pullback, whose terminal leg is constructed and proved
here. Reuse the native pushout-tensor lifting theorem and simplicial model.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerOriginalSimplicialCotensorRestriction

noncomputable section

/-- The relative internal-Hom pullback against a terminal map is the original internal Hom. -/
def terminalPullback {A B : SSet.{u}} (i : A ⟶ B) (X : SSet.{u}) :
    SSet.PullbackIhom i (terminal.from X) := by
  let tA : IsTerminal ((ihom A).obj (⊤_ SSet.{u})) :=
    IsTerminal.isTerminalObj (ihom A) _ terminalIsTerminal
  let tB : IsTerminal ((ihom B).obj (⊤_ SSet.{u})) :=
    IsTerminal.isTerminalObj (ihom B) _ terminalIsTerminal
  refine
    { pt := (ihom A).obj X
      fst := 𝟙 _
      snd := tB.from _
      isPullback := ?_ }
  refine IsPullback.of_isLimit
    (c := PullbackCone.mk (𝟙 _) (tB.from _) (tA.hom_ext _ _)) ?_
  refine PullbackCone.IsLimit.mk (tA.hom_ext _ _) (fun s ↦ s.fst) ?_ ?_ ?_
  · intro s
    exact Category.comp_id _
  · intro s
    exact tB.hom_ext _ _
  · intro s m hm _
    simpa only [Category.comp_id] using hm

/-- The native relative map is exactly the unchanged original parameter restriction. -/
theorem terminalPullback_π {A B : SSet.{u}} (i : A ⟶ B) (X : SSet.{u}) :
    (terminalPullback i X).π = (MonoidalClosed.pre i).app X := by
  simpa only [terminalPullback, Category.comp_id] using (terminalPullback i X).π_fst

/-- The actual native cotensor restriction is a fibration for every monomorphic parameter. -/
theorem pre_fibration {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (X : SSet.{u}) [X.KanComplex] : Fibration ((MonoidalClosed.pre i).app X) := by
  have : Fibration (terminal.from X) := inferInstance
  have h : Fibration (terminalPullback i X).π := inferInstance
  rwa [terminalPullback_π] at h

/-- An anodyne parameter gives a trivial native relative-function fibration. -/
theorem relative_anodyne_trivialFibration {A B X Y : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (p : X ⟶ Y) [Fibration p]
    (r : SSet.PullbackIhom i p) : trivialFibrations SSet.{u} r.π := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  rintro _ _ _ ⟨n⟩
  let h : SSet.PushoutTensor i (SSet.boundary n).ι :=
    Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i (SSet.boundary n).ι
  have ha : SSet.anodyneExtensions h.ι := SSet.anodyneExtensions.pushoutTensorι₁ h hi
  exact (SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom h r).1
    (ha.hasLeftLiftingProperty p)

/-- The actual restriction into a Kan complex is a trivial fibration for any anodyne parameter. -/
theorem pre_trivialFibration {A B : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (X : SSet.{u}) [X.KanComplex] :
    trivialFibrations SSet.{u} ((MonoidalClosed.pre i).app X) := by
  have : Fibration (terminal.from X) := inferInstance
  have h := relative_anodyne_trivialFibration i hi (terminal.from X) (terminalPullback i X)
  rwa [terminalPullback_π] at h

end

end DaggerOriginalSimplicialCotensorRestriction
