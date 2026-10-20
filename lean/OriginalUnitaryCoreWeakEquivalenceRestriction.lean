import OriginalCanonicalVertexWeakEquivalenceRestriction
import OriginalDaggerHomotopyFixedPointWeakEquivalences
import OriginalUnitaryCoreConstruction

/-!
# Recognition of the original unitary map once the original core map is weak

The antecedent is the underlying simplicial weak equivalence of the original
greatest dagger core map. Realization, the Borel model and the actual EC₂ mapping
functor prove the ambient weak equivalence. The original canonical full
subcomplex restriction then gives precisely weak equivalence if and only if
surjectivity on unitary components. This implements the final restriction step
of Theorem C; obtaining the antecedent from full faithfulness and unitary
component surjectivity remains the ordinary quasi-category recognition bridge.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels HomotopicalAlgebra
open DaggerOriginalDaggerCoreCandidate DaggerOriginalDaggerCoreCandidateFunctor
open DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalEC2HomotopyFixedPointFunctor DaggerOriginalEC2CanonicalVertexSubcomplex
open DaggerOriginalCanonicalVertexWeakEquivalenceRestriction
open DaggerOriginalDaggerHomotopyFixedPointWeakEquivalences
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalUnitaryCoreWeakEquivalenceRestriction

noncomputable section

/-- The original unitary ambient map is weak when the original greatest core map is weak. -/
theorem unitaryCoreAmbient_map_weakEquivalence {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    [WeakEquivalence (daggerCoreMap f).hom] :
    WeakEquivalence (unitaryCoreAmbientFunctor.map f) :=
  daggerHomotopyFixedPoint_map_weakEquivalence (daggerCoreMap f)

/-- The actual unitary map is weak if the actual core map is weak and unitary π₀ is covered. -/
theorem unitaryCore_map_weakEquivalence {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    [WeakEquivalence (daggerCoreMap f).hom]
    (hπ₀ : Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f))) :
    WeakEquivalence (unitaryCoreFunctor.map f) := by
  have : WeakEquivalence (daggerHomotopyFixedPointFunctor.map (daggerCoreMap f)) :=
    unitaryCoreAmbient_map_weakEquivalence f
  exact canonicalVertexMap_weakEquivalence (daggerCoreMap f) hπ₀

/-- A weak original unitary map covers the components of the original unitary core. -/
theorem unitaryCore_mapπ₀_surjective {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    [WeakEquivalence (unitaryCoreFunctor.map f)] :
    Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) := by
  have : WeakEquivalence (canonicalVertexMap (daggerCoreMap f)) := by
    change WeakEquivalence (unitaryCoreFunctor.map f)
    infer_instance
  exact canonicalVertexMap_mapπ₀_surjective (daggerCoreMap f)

/-- Under the ordinary-core weak equivalence, unitary weak equivalence is recognized by π₀. -/
theorem unitaryCore_map_weakEquivalence_iff {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    [WeakEquivalence (daggerCoreMap f).hom] :
    WeakEquivalence (unitaryCoreFunctor.map f) ↔
      Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) := by
  constructor
  · intro hf
    exact unitaryCore_mapπ₀_surjective f
  · exact unitaryCore_map_weakEquivalence f

end

end DaggerOriginalUnitaryCoreWeakEquivalenceRestriction
