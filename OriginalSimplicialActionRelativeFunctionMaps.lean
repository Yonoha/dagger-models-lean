import OriginalSimplicialActionModelCategory
import OriginalActionAdjunctionLift
import TopCatModelCategory.SSet.AnodyneExtensionsAdjunctions

/-!
# Original simplicial parameter adjunction and relative equivariant function maps

Lift the native simplicial tensor/internal-hom parametrized adjunction through the existing
functor on actions. Forgetting its relative function square retains exactly the native
simplicial pullback. Native union products and horn anodyne extensions prove both relative
trivial-fibration assertions needed for original boundary and horn parameter products.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalActionAdjunctionLift
open DaggerOriginalSimplicialActionModelCategory
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory

universe u

namespace DaggerOriginalSimplicialActionRelativeFunctionMaps

noncomputable section

/-- The native tensor with a trivial simplicial parameter and the original action on its target.
-/
def actionTensor : SSet.{u} ⥤ Action SSet.{u} C2.{u} ⥤ Action SSet.{u} C2.{u} :=
  curriedTensor SSet.{u} ⋙ actionLift C2.{u}

/-- The native internal hom retains the original postcomposition action. -/
def actionIhom : SSet.{u}ᵒᵖ ⥤ Action SSet.{u} C2.{u} ⥤ Action SSet.{u} C2.{u} :=
  MonoidalClosed.internalHom ⋙ actionLift C2.{u}

/-- The existing ordinary parametrized adjunction lifts to the literal simplicial actions. -/
def actionAdjunction₂ : actionTensor.{u} ⊣₂ actionIhom.{u} :=
  ParametrizedAdjunction.mk'
    (fun A ↦ actionAdjunction C2.{u} (MonoidalClosed.internalHomAdjunction₂.adj A)) (by
      intro A B i E X f
      apply Action.Hom.ext
      change (MonoidalClosed.internalHomAdjunction₂.adj A).homEquiv E.V X.V
          (((curriedTensor SSet.{u}).map i).app E.V ≫ f.hom) =
        (MonoidalClosed.internalHomAdjunction₂.adj B).homEquiv E.V X.V f.hom ≫
          (MonoidalClosed.internalHom.map i.op).app X.V
      exact MonoidalClosed.internalHomAdjunction₂.homEquiv_naturality_one i f.hom)

/-- The original action pushout-tensor and relative-function lifting problems correspond. -/
theorem actionPushout_lifting_iff {A B : SSet.{u}} (i : A ⟶ B)
    {E F X Y : Action SSet.{u} C2.{u}} (j : E ⟶ F) (p : X ⟶ Y)
    (h : Functor.PushoutObjObj actionTensor i j)
    (r : Functor.PullbackObjObj actionIhom i p) :
    HasLiftingProperty h.ι p ↔ HasLiftingProperty j r.π :=
  actionAdjunction₂.hasLiftingProperty_iff h r

/-- The relative equivariant function square has the literal native underlying pullback. -/
def underlyingActionPullback {A B : SSet.{u}} (i : A ⟶ B)
    {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y)
    (r : Functor.PullbackObjObj actionIhom i p) : SSet.PullbackIhom i p.hom where
  pt := r.pt.V
  fst := r.fst.hom
  snd := r.snd.hom
  isPullback := r.isPullback.map (Action.forget SSet.{u} C2.{u})

/-- Forgetting the actual relative-function arrow retains its original native projection. -/
theorem underlyingActionPullback_π {A B : SSet.{u}} (i : A ⟶ B)
    {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y)
    (r : Functor.PullbackObjObj actionIhom i p) :
    (underlyingActionPullback i p r).π = r.π.hom := by
  apply (underlyingActionPullback i p r).isPullback.hom_ext
  · exact (Functor.PullbackObjObj.π_fst _).trans
      (congrArg Action.Hom.hom r.π_fst).symm
  · exact (Functor.PullbackObjObj.π_snd _).trans
      (congrArg Action.Hom.hom r.π_snd).symm

/-- At every original subcomplex inclusion, a trivial fibration gives a trivial function map. -/
theorem relativeFunction_trivialFibration {A : SSet.{u}} (B : A.Subcomplex)
    {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p] [WeakEquivalence p]
    (r : SSet.PullbackIhom B.ι p) : trivialFibrations SSet.{u} r.π := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  rintro _ _ _ ⟨n⟩
  let h := SSet.PushoutTensor.unionProd B (SSet.boundary n)
  have : Mono h.ι := by
    change Mono (SSet.PushoutTensor.unionProd B (SSet.boundary n)).ι
    rw [SSet.PushoutTensor.ι_unionProd]
    infer_instance
  have : Cofibration h.ι := by
    rw [cofibration_iff, SSet.modelCategoryQuillen.cofibrations_eq]
    exact MorphismProperty.monomorphisms.infer_property _
  exact (SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom h r).1 inferInstance

/-- The original horn parameter and any fibration give a trivial relative function map. -/
theorem relativeFunction_horn_trivialFibration (n : ℕ) (i : Fin (n + 2))
    {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p]
    (r : SSet.PullbackIhom (SSet.horn (n + 1) i).ι p) : trivialFibrations SSet.{u} r.π := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  rintro _ _ _ ⟨k⟩
  let h := SSet.PushoutTensor.unionProd (SSet.horn (n + 1) i) (SSet.boundary k)
  have ha : SSet.anodyneExtensions h.ι :=
    SSet.anodyneExtensions.pushoutTensorι₁ h (SSet.anodyneExtensions.horn_ι_mem n i)
  exact (SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom h r).1
    (ha.hasLeftLiftingProperty p)

/-- Original subcomplex relative function maps preserve projective trivial fibrations. -/
theorem relativeActionFunction_trivialFibration {A : SSet.{u}} (B : A.Subcomplex)
    {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) [Fibration p] [WeakEquivalence p]
    (r : Functor.PullbackObjObj actionIhom B.ι p) :
    trivialFibrations (Action SSet.{u} C2.{u}) r.π := by
  have : Fibration p.hom := (fibration_iff_underlying p).1 inferInstance
  have : WeakEquivalence p.hom := (weakEquivalence_iff_underlying p).1 inferInstance
  have h := relativeFunction_trivialFibration B p.hom (underlyingActionPullback _ p r)
  rw [underlyingActionPullback_π] at h
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).1 h
  exact (mem_trivialFibrations_iff _).2
    ⟨(fibration_iff_underlying _).2 hf, (weakEquivalence_iff_underlying _).2 hw⟩

/-- Original horn relative function maps turn projective fibrations into trivial fibrations. -/
theorem relativeActionFunction_horn_trivialFibration (n : ℕ) (i : Fin (n + 2))
    {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) [Fibration p]
    (r : Functor.PullbackObjObj actionIhom (SSet.horn (n + 1) i).ι p) :
    trivialFibrations (Action SSet.{u} C2.{u}) r.π := by
  have : Fibration p.hom := (fibration_iff_underlying p).1 inferInstance
  have h := relativeFunction_horn_trivialFibration n i p.hom (underlyingActionPullback _ p r)
  rw [underlyingActionPullback_π] at h
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).1 h
  exact (mem_trivialFibrations_iff _).2
    ⟨(fibration_iff_underlying _).2 hf, (weakEquivalence_iff_underlying _).2 hw⟩

end

end DaggerOriginalSimplicialActionRelativeFunctionMaps
