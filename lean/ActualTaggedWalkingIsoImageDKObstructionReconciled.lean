import ActualFreeWalkingIsoIntegerObstructionReconciled
import OriginalTaggedReverseGeneratorComparison
import DaggerModels.FreeDaggerCofibration
import TopCatModelCategory.QuillenAdjunction

/-!
# The actual tagged left Kan image of the original walking-isomorphism generator

The original full arrow comparison identifies this image with the literal free
dagger arrow. Its actual dagger rigidification is not a dagger DK equivalence.
The model-category bridge explicitly retains the original weak-class identity
and the still-needed DCH trivial-cofibration input.
-/

set_option autoImplicit false
open CategoryTheory Limits Simplicial DaggerModels HomotopicalAlgebra
open DaggerModels.OrdinaryRigidification
open DaggerUnitaryDiscrete DaggerUnitarySubgroupoid DaggerUnitaryInvariance
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalTaggedReverseGeneratorComparison
open DaggerModels.OriginalTaggedReverseAdjunctions
open DaggerActualFreeWalkingIsoIntegerObstruction
universe u
namespace DaggerActualTaggedWalkingIsoImageDKObstruction
noncomputable section

/-- Coherent essential surjectivity transports along the entire original arrow isomorphism. -/
theorem coherentlyEssentiallySurjective_of_arrowIso (R : FunctorialFibrantReplacement.{u})
    {X Y X' Y' : DaggerSimplicialCat.{u, u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) (hf : DaggerGlobalDK.CoherentlyEssentiallySurjective R f) :
    DaggerGlobalDK.CoherentlyEssentiallySurjective R g := by
  intro y
  obtain ⟨x, v, hv⟩ := hf (e.inv.right.obj y)
  have h := coherentlyUnitary_map R e.hom.right _ _ v hv
  have hy : e.inv.right ≫ e.hom.right = 𝟙 Y' :=
    congrArg (fun k : Arrow.mk g ⟶ Arrow.mk g ↦ k.right) e.inv_hom_id
  have hyobj := congrArg (fun k : Y' ⟶ Y' ↦ k.obj y) hy
  change e.hom.right.obj (e.inv.right.obj y) = y at hyobj
  have hx := congrArg (fun k : X ⟶ Y' ↦ k.obj x) e.hom.w
  change g.obj (e.hom.left.obj x) = e.hom.right.obj (f.obj x) at hx
  have hp : ∃ w, CoherentlyUnitary R Y'
      (e.hom.right.obj (f.obj x)) (e.hom.right.obj (e.inv.right.obj y)) w := ⟨_, h⟩
  rw [← hx, hyobj] at hp
  obtain ⟨w, hw⟩ := hp
  exact ⟨e.hom.left.obj x, w, hw⟩

/-- Both directions preserve the same full coherent ESS predicate. -/
theorem coherentlyEssentiallySurjective_arrowIso_iff (R : FunctorialFibrantReplacement.{u})
    {X Y X' Y' : DaggerSimplicialCat.{u, u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    DaggerGlobalDK.CoherentlyEssentiallySurjective R f ↔
      DaggerGlobalDK.CoherentlyEssentiallySurjective R g :=
  ⟨coherentlyEssentiallySurjective_of_arrowIso R e,
    coherentlyEssentiallySurjective_of_arrowIso R e.symm⟩

/-- The actual anti-involutive double-walking-isomorphism generator. -/
def taggedGenerator : freeAnti.obj (Δ[0] : SSet.{u}) ⟶ freeAnti.obj J.{u} :=
  freeAnti.map zeroInclusion.{u}

/-- The actual image under the original left Kan extension. -/
def imageGenerator : leftKan.obj (freeAnti.obj (Δ[0] : SSet.{u})) ⟶
    leftKan.obj (freeAnti.obj J.{u}) := leftKan.map taggedGenerator.{u}

/-- The existing comparison identifies the literal full source/image arrows. -/
def imageGeneratorIso : Arrow.mk imageGenerator.{u} ≅ Arrow.mk freeGenerator.{u} :=
  freeMapIso zeroInclusion.{u}

/-- Reuse the terminal-domain proof for the same ordinary zero-vertex inclusion. -/
instance zeroInclusion_mono : Mono zeroInclusion.{u} :=
  IsTerminal.mono_from SSet.stdSimplex.isTerminalObj₀ _

/-- The actual left Kan image is in the original free-cofibration class. -/
theorem imageGenerator_freeCofibration : DaggerSSet.FreeCofibration imageGenerator.{u} :=
  freeMap_freeCofibration zeroInclusion.{u}

/-- The same actual image fails coherent ESS after actual dagger rigidification. -/
theorem rigidified_imageGenerator_not_coherentlyEssentiallySurjective
    (R : FunctorialFibrantReplacement.{u}) :
    ¬ DaggerGlobalDK.CoherentlyEssentiallySurjective R
      (DaggerRigidification.daggerRigidification.map imageGenerator.{u}) := by
  intro h
  apply rigidified_freeGenerator_not_coherentlyEssentiallySurjective R
  exact coherentlyEssentiallySurjective_of_arrowIso R
    (DaggerRigidification.daggerRigidification.mapArrow.mapIso imageGeneratorIso.{u}) h

/-- The actual rigidified left Kan image is not dagger DK for every original replacement. -/
theorem rigidified_imageGenerator_not_daggerDK (R : FunctorialFibrantReplacement.{u}) :
    ¬ DaggerGlobalDK.daggerDK R
      (DaggerRigidification.daggerRigidification.map imageGenerator.{u}) := by
  intro h
  exact rigidified_imageGenerator_not_coherentlyEssentiallySurjective R h.2

variable [ModelCategory DaggerSSet.{u}]

/-- Non-weakness for every supplied model with the full original rigidification weak class. -/
theorem imageGenerator_not_weakEquivalence (R : FunctorialFibrantReplacement.{u})
    (hweak : ∀ {X Y : DaggerSSet.{u}} (f : X ⟶ Y),
      WeakEquivalence f ↔ DaggerGlobalDK.daggerDK R
        (DaggerRigidification.daggerRigidification.map f)) :
    ¬ WeakEquivalence imageGenerator.{u} := by
  intro h
  exact rigidified_imageGenerator_not_daggerDK R ((hweak _).1 h)

variable [ModelCategory AntiInvolutiveSSet.{u}]

/-- The model bridge keeps the particular DCH trivial-cofibration fact as an explicit input. -/
theorem leftAdjunction_not_isQuillenAdjunction (R : FunctorialFibrantReplacement.{u})
    (hweak : ∀ {X Y : DaggerSSet.{u}} (f : X ⟶ Y),
      WeakEquivalence f ↔ DaggerGlobalDK.daggerDK R
        (DaggerRigidification.daggerRigidification.map f))
    (hgenerator : (trivialCofibrations AntiInvolutiveSSet.{u}) taggedGenerator.{u}) :
    ¬ leftAdjunction.{u}.IsQuillenAdjunction := by
  intro h
  have := h
  have hpres := Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations leftAdjunction
  have hw := hpres.trivialCofibrations_le _ hgenerator
  apply imageGenerator_not_weakEquivalence R hweak
  exact (weakEquivalence_iff _).2 hw.2

end
end DaggerActualTaggedWalkingIsoImageDKObstruction
