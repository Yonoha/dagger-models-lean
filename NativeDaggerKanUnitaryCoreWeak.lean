import OriginalUnitaryCoreWeakEquivalenceRestriction
import OriginalUnitaryCoreCanonicalVertices
import NativeKanRigHomWeakRecognition

/-! Reuse original HFP weak preservation and original full canonical-vertex restriction.
The actual dagger map, original greatest core and literal unitary-core functor are retained.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalDaggerCoreCandidate DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreCanonicalVertices DaggerOriginalUnitaryCoreWeakEquivalenceRestriction
open DaggerNativeKanRigHomWeakRecognition
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeDaggerKanUnitaryCoreWeak
noncomputable section

theorem core_map_weak {X Y : DaggerSSet.{u}} [X.toSSet.KanComplex] [Y.toSSet.KanComplex]
    (f : X ⟶ Y) (hf : WeakEquivalence f.hom) : WeakEquivalence (daggerCoreMap f).hom := by
  have : IsIso (daggerCoreInclusion X).hom := core_inclusion_isIso X.toSSet
  have : IsIso (daggerCoreInclusion Y).hom := core_inclusion_isIso Y.toSSet
  have : WeakEquivalence f.hom := hf
  have : WeakEquivalence ((daggerCoreMap f).hom ≫ (daggerCoreInclusion Y).hom) := by
    rw [daggerCoreMap_comp_inclusion]
    infer_instance
  exact weakEquivalence_of_postcomp (daggerCoreMap f).hom (daggerCoreInclusion Y).hom

theorem unitary_vertices_surjective {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective (f.hom.app (op ⦋0⦌))) :
    Function.Surjective ((unitaryCoreFunctor.map f).app (op ⦋0⦌)) := by
  intro y
  obtain ⟨v, rfl⟩ := canonicalUnitaryVertex_surjective Y y
  obtain ⟨x, rfl⟩ := hf v
  exact ⟨canonicalUnitaryVertex X x, canonicalUnitaryVertex_naturality f x⟩

theorem unitary_map_weak {X Y : DaggerSSet.{u}}
    [X.toSSet.KanComplex] [Y.toSSet.KanComplex] (f : X ⟶ Y)
    (hf : WeakEquivalence f.hom) (hv : Function.Surjective (f.hom.app (op ⦋0⦌))) :
    WeakEquivalence (unitaryCoreFunctor.map f) := by
  have := core_map_weak f hf
  exact unitaryCore_map_weakEquivalence f
    (mapπ₀_surjective_of_vertices _ (unitary_vertices_surjective f hv))

end
end DaggerNativeDaggerKanUnitaryCoreWeak
