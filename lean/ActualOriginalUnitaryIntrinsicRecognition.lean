import ActualDaggerRigLocalLeftWeak
import OriginalUnitaryMappingWeakEquivalenceRecognition

/-! Conditions (2) and (3) of ORIGINAL Main C, with the SAME original unitary core.
The previously proved recognition theorem is reused byte-for-byte. The newer prefix-fiber
mapping maps are definitionally the SAME original left mapping maps, at BOTH endpoints.
This module does not claim the interval/path comparison or condition (1).
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryMappingWeakEquivalenceRecognition
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualOriginalUnitaryIntrinsicRecognition
noncomputable section

theorem leftMappingSpace_eq_original (X : SSet.{u}) (x y : X.obj (op ⦋0⦌)) :
    DaggerActualQuasicategoryMappingFibres.leftMapping X x y =
      DaggerOriginalQuasicategoryLeftMappingSpace.leftMappingSpace X x y := rfl

theorem leftMappingMap_eq_original {X Y : SSet.{u}} (f : X ⟶ Y)
    (x y : X.obj (op ⦋0⦌)) :
    DaggerActualQuasicategoryMappingFibres.map f ⦋0⦌ x y =
      DaggerOriginalLeftMappingFunctoriality.leftMappingMap f x y := rfl

theorem unitary_weak_iff_components_of_left_mapping_weak {X Y : DaggerSSet.{u}}
    [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory] (f : X ⟶ Y)
    (hf : ∀ x y : X.toSSet.obj (op ⦋0⦌),
      WeakEquivalence (DaggerActualQuasicategoryMappingFibres.map f.hom ⦋0⦌ x y)) :
    WeakEquivalence (unitaryCoreFunctor.map f) ↔
      Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) := by
  exact unitaryCore_map_weakEquivalence_iff_of_mappingWeak f
      (DaggerNativeHoIsoTriangles.native_inner_fillers X.toSSet)
      (DaggerNativeHoIsoTriangles.native_inner_fillers Y.toSSet) hf

theorem unitary_weak_iff_components_of_rig_hom_weak {X Y : DaggerSSet.{u}}
    [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory] (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X.toSSet).Obj,
      WeakEquivalence ((rigidification.map f.hom).map a b)) :
    WeakEquivalence (unitaryCoreFunctor.map f) ↔
      Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) :=
  unitary_weak_iff_components_of_left_mapping_weak f
    ((DaggerActualDaggerRigLocalLeftWeak.rig_hom_weak_iff_left_maps_weak f).mp hf)

theorem intrinsic_conditions_two_three {X Y : DaggerSSet.{u}}
    [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory] (f : X ⟶ Y) :
    ((∀ x y : X.toSSet.obj (op ⦋0⦌),
      WeakEquivalence (DaggerActualQuasicategoryMappingFibres.map f.hom ⦋0⦌ x y)) ∧
      Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f))) ↔
    ((∀ x y : X.toSSet.obj (op ⦋0⦌),
      WeakEquivalence (DaggerActualQuasicategoryMappingFibres.map f.hom ⦋0⦌ x y)) ∧
      WeakEquivalence (unitaryCoreFunctor.map f)) := by
  constructor
  · rintro ⟨hf, hπ⟩
    exact ⟨hf, (unitary_weak_iff_components_of_left_mapping_weak f hf).mpr hπ⟩
  · rintro ⟨hf, hw⟩
    exact ⟨hf, (unitary_weak_iff_components_of_left_mapping_weak f hf).mp hw⟩

theorem rig_intrinsic_conditions_two_three {X Y : DaggerSSet.{u}}
    [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory] (f : X ⟶ Y) :
    ((∀ a b : (rigidification.obj X.toSSet).Obj,
      WeakEquivalence ((rigidification.map f.hom).map a b)) ∧
      Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f))) ↔
    ((∀ a b : (rigidification.obj X.toSSet).Obj,
      WeakEquivalence ((rigidification.map f.hom).map a b)) ∧
      WeakEquivalence (unitaryCoreFunctor.map f)) := by
  constructor
  · rintro ⟨hf, hπ⟩
    exact ⟨hf, (unitary_weak_iff_components_of_rig_hom_weak f hf).mpr hπ⟩
  · rintro ⟨hf, hw⟩
    exact ⟨hf, (unitary_weak_iff_components_of_rig_hom_weak f hf).mp hw⟩

end
end DaggerActualOriginalUnitaryIntrinsicRecognition
