import OriginalFixedObjectPullbackFibrations

/-!
# Actual mapping-path endpoint fibrations on simplicial sets

Identify the full paired mapping-path map as a pullback of the native paired
endpoint fibration. The projection to the target is a fibration when the
source and target are Kan, without any model premise on original groupoids.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Simplicial
open DaggerOriginalSimplicialPullbackPairs DaggerOriginalFixedObjectCotensorPoints
open DaggerOriginalFixedObjectGroupoidInterval DaggerOriginalFixedObjectGroupoidHomPathFactorization
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalSimplicialMappingPathFibrations
noncomputable section

/-- Pair the source projection with the other endpoint of the actual path. -/
def mappingPair {X Y : SSet.{u}} (f : X ⟶ Y) :
    pairedPullback f (pointEvaluation (intervalPoint 0) Y) ⟶ X ⊗ Y :=
  CartesianMonoidalCategory.lift (pairedFst f (pointEvaluation (intervalPoint 0) Y))
    (pairedSnd f (pointEvaluation (intervalPoint 0) Y) ≫
      pointEvaluation (intervalPoint 1) Y)

/-- The exact paired mapping-path square commutes in all simplicial degrees. -/
theorem mappingPair_comm {X Y : SSet.{u}} (f : X ⟶ Y) :
    pairedSnd f (pointEvaluation (intervalPoint 0) Y) ≫ endpointPair Y =
      mappingPair f ≫ (f ⊗ₘ 𝟙 Y) := by
  apply NatTrans.ext
  funext n p
  exact Prod.ext p.2.symm rfl

/-- Lift the native paired endpoint square through the exact full path-pair constraint. -/
def mappingPairLift {W X Y : SSet.{u}} {f : X ⟶ Y}
    (a : W ⟶ (CategoryTheory.ihom Δ[1]).obj Y) (b : W ⟶ X ⊗ Y)
    (h : a ≫ endpointPair Y = b ≫ (f ⊗ₘ 𝟙 Y)) :
    W ⟶ pairedPullback f (pointEvaluation (intervalPoint 0) Y) :=
  pairedLift (b ≫ CartesianMonoidalCategory.fst X Y) a (by
    apply NatTrans.ext
    funext n w
    exact (congrArg Prod.fst (congrFun (NatTrans.congr_app h n) w)).symm)

/-- The first leg recovers the entire original path map. -/
theorem mappingPairLift_path {W X Y : SSet.{u}} {f : X ⟶ Y}
    (a : W ⟶ (CategoryTheory.ihom Δ[1]).obj Y) (b : W ⟶ X ⊗ Y)
    (h : a ≫ endpointPair Y = b ≫ (f ⊗ₘ 𝟙 Y)) :
    mappingPairLift a b h ≫ pairedSnd f (pointEvaluation (intervalPoint 0) Y) = a := rfl

/-- The second leg recovers the entire original source/target pair map. -/
theorem mappingPairLift_pair {W X Y : SSet.{u}} {f : X ⟶ Y}
    (a : W ⟶ (CategoryTheory.ihom Δ[1]).obj Y) (b : W ⟶ X ⊗ Y)
    (h : a ≫ endpointPair Y = b ≫ (f ⊗ₘ 𝟙 Y)) :
    mappingPairLift a b h ≫ mappingPair f = b := by
  apply NatTrans.ext
  funext n w
  exact Prod.ext rfl (congrArg (fun p : Y.obj n × Y.obj n ↦ p.2)
    (congrFun (NatTrans.congr_app h n) w))

/-- The paired path square has the full native limiting-cone universal property. -/
def mappingPairIsLimit {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsLimit (PullbackCone.mk (pairedSnd f (pointEvaluation (intervalPoint 0) Y))
      (mappingPair f) (mappingPair_comm f)) :=
  PullbackCone.IsLimit.mk _ (fun s ↦ mappingPairLift s.fst s.snd s.condition)
    (fun s ↦ mappingPairLift_path s.fst s.snd s.condition)
    (fun s ↦ mappingPairLift_pair s.fst s.snd s.condition) (by
      intro s m h₁ h₂
      apply paired_ext
      · apply NatTrans.ext
        funext n w
        exact congrArg (fun p : X.obj n × Y.obj n ↦ p.1)
          (congrFun (NatTrans.congr_app h₂ n) w)
      · exact h₁.trans (mappingPairLift_path s.fst s.snd s.condition).symm)

/-- The full paired map is the actual pullback of the native endpoint pair. -/
theorem mappingPairIsPullback {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsPullback (pairedSnd f (pointEvaluation (intervalPoint 0) Y)) (mappingPair f)
      (endpointPair Y) (f ⊗ₘ 𝟙 Y) := IsPullback.of_isLimit (mappingPairIsLimit f)

/-- The paired mapping-path map is a native fibration for every original Kan target. -/
theorem mappingPair_fibration {X Y : SSet.{u}} (f : X ⟶ Y) [Y.KanComplex] :
    Fibration (mappingPair f) :=
  (fibration_iff _).2 (MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (mappingPairIsPullback f) ((fibration_iff (endpointPair Y)).1 (endpointPair_fibration Y)))

/-- The native Cartesian second projection is a pullback of the first terminal map. -/
def productTerminalIsLimit (X Y : SSet.{u}) :
    IsLimit (PullbackCone.mk
      (f := CartesianMonoidalCategory.toUnit Y) (g := CartesianMonoidalCategory.toUnit X)
      (CartesianMonoidalCategory.snd X Y) (CartesianMonoidalCategory.fst X Y)
      (CartesianMonoidalCategory.toUnit_unique _ _)) :=
  PullbackCone.IsLimit.mk _
    (fun s ↦ CartesianMonoidalCategory.lift s.snd s.fst)
    (fun _ ↦ by apply NatTrans.ext; funext n w; rfl)
    (fun _ ↦ by apply NatTrans.ext; funext n w; rfl) (by
      intro s m h₁ h₂
      apply NatTrans.ext
      funext n w
      exact Prod.ext (congrFun (NatTrans.congr_app h₂ n) w)
        (congrFun (NatTrans.congr_app h₁ n) w))

/-- Projection from the original Cartesian product is a native fibration for Kan X. -/
theorem productSnd_fibration (X Y : SSet.{u}) [X.KanComplex] :
    Fibration (CartesianMonoidalCategory.snd X Y) := by
  have hx : Fibration (CartesianMonoidalCategory.toUnit X) :=
    (isFibrant_iff_of_isTerminal _ CartesianMonoidalCategory.isTerminalTensorUnit).1
      inferInstance
  apply (fibration_iff _).2
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_isLimit (productTerminalIsLimit X Y)).flip ((fibration_iff _).1 hx)

/-- The actual other-endpoint map of the mapping path is a fibration for Kan source and target. -/
theorem mappingEndpoint_fibration {X Y : SSet.{u}} (f : X ⟶ Y)
    [X.KanComplex] [Y.KanComplex] :
    Fibration (pairedSnd f (pointEvaluation (intervalPoint 0) Y) ≫
      pointEvaluation (intervalPoint 1) Y) := by
  have : Fibration (mappingPair f) := mappingPair_fibration f
  have : Fibration (CartesianMonoidalCategory.snd X Y) := productSnd_fibration X Y
  change Fibration (mappingPair f ≫ CartesianMonoidalCategory.snd X Y)
  infer_instance

end
end DaggerOriginalSimplicialMappingPathFibrations
