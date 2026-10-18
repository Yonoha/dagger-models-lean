import OriginalCoreMappingWeakEquivalenceRecognition
import OriginalUnitaryCoreComponentSurjectivity
import OriginalUnitaryCoreWeakEquivalenceRestriction

/-!
# Weak-equivalence recognition for the original unitary core through actual mapping spaces

For inner-horn-filling inputs, actual original left mapping-space weak
equivalences and surjectivity on the actual unitary components imply weak
equivalence of the original greatest dagger core itself. The verified native
Borel and homotopy-fixed-point preservation route then gives weak equivalence
of the original unitary core map, without an assumed core weak equivalence.
This supplies the mapping-space recognition stage of Theorem C; identifying
these exact mapping-space hypotheses with the manuscript's derived hom maps
and proving the full model-category comparison are separate requirements.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalInnerHornFillers DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalDaggerCoreCandidate DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreComponentSurjectivity
open DaggerOriginalCoreMappingWeakEquivalenceRecognition
open DaggerOriginalUnitaryCoreWeakEquivalenceRestriction

universe u

namespace DaggerOriginalUnitaryMappingWeakEquivalenceRecognition

noncomputable section

/-- Actual original mapping weak equivalences and actual unitary component coverage give
 a weak equivalence of the same original greatest dagger core itself. -/
theorem daggerCore_map_weakEquivalence_of_mappingWeak_and_unitaryComponents
    {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X.toSSet) (hY : innerHornFillers Y.toSSet)
    (hmap : ∀ x y : X.toSSet.obj (op ⦋0⦌), WeakEquivalence (leftMappingMap f.hom x y))
    (hπ₀ : Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f))) :
    WeakEquivalence (daggerCoreMap f).hom :=
  ordinaryCore_map_weakEquivalence f.hom hX hY hmap
    (core_pi0_surjective_of_unitary_pi0_surjective f hπ₀)

/-- The same hypotheses give a weak equivalence of the original unitary core map itself. -/
theorem unitaryCore_map_weakEquivalence_of_mappingWeak_and_unitaryComponents
    {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X.toSSet) (hY : innerHornFillers Y.toSSet)
    (hmap : ∀ x y : X.toSSet.obj (op ⦋0⦌), WeakEquivalence (leftMappingMap f.hom x y))
    (hπ₀ : Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f))) :
    WeakEquivalence (unitaryCoreFunctor.map f) := by
  haveI := daggerCore_map_weakEquivalence_of_mappingWeak_and_unitaryComponents f hX hY hmap hπ₀
  exact unitaryCore_map_weakEquivalence f hπ₀

/-- Under actual original mapping weak equivalences, the original unitary weak equivalence
 is equivalent to coverage of the actual original unitary components. -/
theorem unitaryCore_map_weakEquivalence_iff_of_mappingWeak
    {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X.toSSet) (hY : innerHornFillers Y.toSSet)
    (hmap : ∀ x y : X.toSSet.obj (op ⦋0⦌), WeakEquivalence (leftMappingMap f.hom x y)) :
    WeakEquivalence (unitaryCoreFunctor.map f) ↔
      Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) := by
  constructor
  · intro hf
    exact unitaryCore_mapπ₀_surjective f
  · exact unitaryCore_map_weakEquivalence_of_mappingWeak_and_unitaryComponents f hX hY hmap

end

end DaggerOriginalUnitaryMappingWeakEquivalenceRecognition
