import OriginalFixedObjectFreeGroupoidQuillen
import OriginalFixedObjectDaggerActionQuillenEquivalence
import OriginalActionAdjunctionLift
import OriginalEC2SimplicialProjectiveCofibrancy

/-!
# The actual free two-object dagger groupoid and inverse-dagger Hom adjunction

Lift the proved ordinary free groupoid adjunction to literal C2 actions and compose
with the proved full dagger/action equivalence. The right adjoint is exactly the
original left-to-right Hom with action by inverse dagger. The left adjoint retains
the entire free groupoid action through the equivalence counit, not just its Hom class.
Both actual models are proved. No adjoint-existence or model-existence hypothesis.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectOrdinaryCellAdjunction DaggerOriginalFixedObjectFreeGroupoidQuillen
open DaggerOriginalFixedObjectDaggerActionEquivalence DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalStrictDaggerGroupoidSigma
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
  DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  DaggerOriginalFixedObjectStrictModel DaggerOriginalFixedObjectStrictDaggerModel
  DaggerOriginalFixedObjectStrictActionClasses DaggerOriginalFixedObjectStrictActionModel
universe u
namespace DaggerOriginalFixedObjectFreeDaggerGroupoidQuillen
noncomputable section

/-- Apply the existing ordinary free groupoid functor to the whole original C2 action. -/
def freeActionGroupoid : Action SSet.{u} C2.{u} ⥤
    Action (FixedStrictGroupoids TwoObjects) C2.{u} := freeGroupoid.mapAction C2

/-- The actual free dagger groupoid, through the proved full inverse-dagger equivalence. -/
def freeDaggerGroupoid : Action SSet.{u} C2.{u} ⥤ FixedStrictDaggerGroupoids TwoObjects :=
  freeActionGroupoid ⋙ (fixedDaggerActionEquivalence TwoObjects).inverse

/-- The actual fixed original Hom evaluation with its original inverse-dagger action. -/
def daggerEvaluation : FixedStrictDaggerGroupoids TwoObjects ⥤ Action SSet.{u} C2.{u} :=
  (fixedDaggerActionEquivalence TwoObjects).functor ⋙ strictEvaluation.mapAction C2

/-- Evaluation retains precisely the original left-to-right Hom simplicial set. -/
theorem daggerEvaluation_obj_V (C : FixedStrictDaggerGroupoids TwoObjects.{u}) :
    (daggerEvaluation.obj C).V =
      C.obj.underlying.enriched.Hom TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right := rfl

/-- Evaluation retains exactly the original full Hom map of each dagger functor. -/
theorem daggerEvaluation_map_hom {C D : FixedStrictDaggerGroupoids TwoObjects.{u}}
    (F : C ⟶ D) :
    (daggerEvaluation.map F).hom =
      F.hom.underlying.map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right := rfl

/-- The original action generator is precisely inverse of the original dagger on this Hom. -/
theorem daggerEvaluation_generator (C : FixedStrictDaggerGroupoids TwoObjects.{u}) :
    ((daggerEvaluation.obj C).ρ generator).asHom =
      strictSigmaHom (originalDagger C.obj) C.property
        TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right := by
  change (fixedDaggerRepresentation C generator).asHom.hom.map
    TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right = _
  rw [fixedDaggerRepresentation_generator]
  rfl

/-- The actual free dagger groupoid and original equivariant Hom evaluation are adjoint. -/
def freeDaggerGroupoidAdjunction : freeDaggerGroupoid.{u} ⊣ daggerEvaluation :=
  (DaggerOriginalActionAdjunctionLift.actionAdjunction C2 freeGroupoidAdjunction).comp
    (fixedDaggerActionEquivalence TwoObjects).symm.toAdjunction

/-- The full action counit identifies the left adjoint with the entire original free groupoid. -/
def freeDaggerActionComparison :
    freeDaggerGroupoid.{u} ⋙ (fixedDaggerActionEquivalence TwoObjects).functor ≅
      freeActionGroupoid :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft freeActionGroupoid
      (fixedDaggerActionEquivalence TwoObjects).counitIso ≪≫
      Functor.rightUnitor _

/-- Original inverse-dagger Hom evaluation preserves every weak equivalence in the strict model. -/
theorem evaluation_weakEquivalence {C D : FixedStrictDaggerGroupoids TwoObjects.{u}}
    (F : C ⟶ D) [WeakEquivalence F] : WeakEquivalence (daggerEvaluation.map F) := by
  apply (DaggerOriginalSimplicialActionModelCategory.weakEquivalence_iff_underlying _).2
  exact (DaggerOriginalFixedObjectGroupoidClasses.strictDagger_weakEquivalence_iff F).1
    inferInstance TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right

/-- The unchanged inverse-dagger Hom evaluation preserves fibrations in the proved strict model. -/
theorem evaluation_fibration {C D : FixedStrictDaggerGroupoids TwoObjects.{u}}
    (F : C ⟶ D) [Fibration F] : Fibration (daggerEvaluation.map F) := by
  apply (DaggerOriginalSimplicialActionModelCategory.fibration_iff_underlying _).2
  exact (DaggerOriginalFixedObjectGroupoidClasses.strictDagger_fibration_iff F).1
    inferInstance TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right

/-- The actual equivariant Hom evaluation preserves native trivial fibrations. -/
def evaluationPreservesTrivialFibrations : daggerEvaluation.{u}.PreservesTrivialFibrations := by
  constructor
  intro C D F hF
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff F).1 hF
  have : Fibration F := hf
  have : WeakEquivalence F := hw
  exact (mem_trivialFibrations_iff _).2 ⟨evaluation_fibration F, evaluation_weakEquivalence F⟩

/-- Native adjunction lifting proves the actual free dagger groupoid preserves cofibrations. -/
theorem freeDaggerGroupoid_cofibration {A B : Action SSet.{u} C2.{u}}
    (i : A ⟶ B) [Cofibration i] : Cofibration (freeDaggerGroupoid.map i) := by
  letI : daggerEvaluation.PreservesTrivialFibrations := evaluationPreservesTrivialFibrations
  letI : freeDaggerGroupoid.PreservesCofibrations :=
    freeDaggerGroupoidAdjunction.preservesTrivialFibrations_iff_preservesCofibrations.1
      inferInstance
  infer_instance

/-- The actual free dagger groupoid/equivariant Hom adjunction is native Quillen. -/
theorem freeDaggerGroupoid_isQuillen : freeDaggerGroupoidAdjunction.{u}.IsQuillenAdjunction where
  cofibration_map i := freeDaggerGroupoid_cofibration i
  fibration_map p := evaluation_fibration p

/-- The actual free dagger groupoid sends each projectively cofibrant action to a
cofibrant object. -/
theorem freeDaggerGroupoid_isCofibrant (A : Action SSet.{u} C2.{u}) [IsCofibrant A] :
    IsCofibrant (freeDaggerGroupoid.obj A) := by
  letI : freeDaggerGroupoid.IsLeftAdjoint := freeDaggerGroupoidAdjunction.isLeftAdjoint
  have : Cofibration (initial.to A) := (isCofibrant_iff A).1 inferInstance
  exact (isCofibrant_iff_of_isInitial (freeDaggerGroupoid.map (initial.to A))
    (IsInitial.isInitialObj freeDaggerGroupoid _ initialIsInitial)).2
      (freeDaggerGroupoid_cofibration (initial.to A))

/-- The manuscript's literal original EC2 gives an actual cofibrant free dagger groupoid. -/
theorem freeOriginalEC2_isCofibrant :
    IsCofibrant (freeDaggerGroupoid.obj DaggerOriginalEC2SimplicialAction.simplicialAction.{u}) :=
  freeDaggerGroupoid_isCofibrant _

/-- Ordinary simplicial cofibrancy proves preservation of every underlying equivariant weak map. -/
theorem freeDaggerGroupoid_weakEquivalence {A B : Action SSet.{u} C2.{u}}
    (f : A ⟶ B) [WeakEquivalence f] : WeakEquivalence (freeDaggerGroupoid.map f) := by
  have : WeakEquivalence f.hom :=
    (DaggerOriginalSimplicialActionModelCategory.weakEquivalence_iff_underlying f).1 inferInstance
  have : WeakEquivalence (freeGroupoid.map f.hom) := freeGroupoid_weakEquivalence f.hom
  have h : WeakEquivalence (freeActionGroupoid.map f) := by
    rw [DaggerOriginalFixedObjectStrictActionClasses.weakEquivalence_iff_underlying]
    change WeakEquivalence (freeGroupoid.map f.hom)
    infer_instance
  exact (DaggerOriginalFixedObjectDaggerActionQuillenEquivalence.inverse_weakEquivalence_iff _).2 h

end
end DaggerOriginalFixedObjectFreeDaggerGroupoidQuillen
