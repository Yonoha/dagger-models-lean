import NativeOriginalIntervalRUnitaryExistence
import ActualOriginalUnitaryIntrinsicRecognition
import ChallengeOriginalMainTheoremC

/-! Assemble the FROZEN FULL original Main C using the EXACT original standard weak class. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerUnitaryInvariance DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreComponentSurjectivity DaggerNativeOriginalIntervalRUnitaryExistence
open DaggerChallengeOriginalMainTheoremC
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalMainCRecognition
noncomputable section

variable {X Y : DaggerSSet.{u}} [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory]
variable (f : X ⟶ Y)

omit [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory] in
theorem rigidification_vertex_natural (x : X.toSSet _⦋0⦌) :
    (DaggerJoyalWeakProperties.Cd.map f).obj (RigidificationVertices.vertexEquiv X.toSSet x) =
      RigidificationVertices.vertexEquiv Y.toSSet (f.hom.app (op ⦋0⦌) x) := by
  change (rigidification.map f.hom).obj (RigidificationVertices.vertexEquiv X.toSSet x) = _
  exact RigidificationVertices.vertexEquiv_naturality f.hom x

omit [X.toSSet.Quasicategory] in
theorem coherent_essential_iff_unitary_surjective (R : FunctorialFibrantReplacement.{u}) :
    DaggerGlobalDK.CoherentlyEssentiallySurjective R (DaggerJoyalWeakProperties.Cd.map f) ↔
      Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) := by
  rw [unitary_pi0_surjective_iff_canonical]
  constructor
  · intro h y
    obtain ⟨c, hc⟩ := h (RigidificationVertices.vertexEquiv Y.toSSet y)
    obtain ⟨x, rfl⟩ := (RigidificationVertices.vertexEquiv X.toSSet).surjective c
    refine ⟨x, ?_⟩
    apply (original_coherent_iff_original_unitary_unconditional R Y
      (f.hom.app (op ⦋0⦌) x) y).1
    rw [rigidification_vertex_natural f x] at hc
    exact hc
  · intro h d
    obtain ⟨y, rfl⟩ := (RigidificationVertices.vertexEquiv Y.toSSet).surjective d
    obtain ⟨x, hxy⟩ := h y
    have hc := (original_coherent_iff_original_unitary_unconditional R Y
      (f.hom.app (op ⦋0⦌) x) y).2 hxy
    refine ⟨RigidificationVertices.vertexEquiv X.toSSet x, ?_⟩
    rw [rigidification_vertex_natural f x]
    exact hc

theorem local_weak_iff_fully_faithful :
    DaggerGlobalDK.LocalGeometricWeakEquivalence (DaggerJoyalWeakProperties.Cd.map f) ↔
      FullyFaithful f := by
  have h : DaggerGlobalDK.LocalGeometricWeakEquivalence (DaggerJoyalWeakProperties.Cd.map f) ↔
      ∀ a b : (rigidification.obj X.toSSet).Obj,
        WeakEquivalence ((rigidification.map f.hom).map a b) := by
    constructor
    · intro hw a b
      exact (DaggerSSetGluing.weakEquivalence_iff_GW _).2 (hw a b)
    · intro hw a b
      exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1 (hw a b)
  exact h.trans (DaggerActualDaggerRigLocalLeftWeak.rig_hom_weak_iff_left_maps_weak f)

theorem standard_weak_iff_condition_two :
    DaggerJoyalWeakProperties.standardJoyalWeakEquivalences f ↔ ConditionTwo f := by
  change (DaggerGlobalDK.LocalGeometricWeakEquivalence (DaggerJoyalWeakProperties.Cd.map f) ∧
    DaggerGlobalDK.CoherentlyEssentiallySurjective standardReplacement
      (DaggerJoyalWeakProperties.Cd.map f)) ↔ (FullyFaithful f ∧ _)
  exact and_congr (local_weak_iff_fully_faithful f)
    (coherent_essential_iff_unitary_surjective f standardReplacement)

theorem verified : Statement.{u} := by
  intro X Y hX hY f
  letI := hX
  letI := hY
  have h := standard_weak_iff_condition_two f
  exact ⟨h, h.trans
    (DaggerActualOriginalUnitaryIntrinsicRecognition.intrinsic_conditions_two_three f)⟩

end
end DaggerNativeOriginalMainCRecognition
