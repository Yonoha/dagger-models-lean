import NativeOriginalFreeEC2UnitaryExistence
import ActualNativeIntervalFreeCoreMappingComparison
import NativeOriginalCoherentUnitaryExistence

/-! ACTUAL interval vertices in the FULL ORIGINAL R target detect SAME ORIGINAL U(X) components. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerActualNativeDaggerIntervalPresentation DaggerActualOriginalCoreEnrichedMappingZigzag
open DaggerActualOriginalGroupoidalCoreRMappingComparison DaggerOriginalStrictPathFiberVertices
open DaggerNativeOriginalFreeEC2UnitaryExistence DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerOriginalFixedObjectLegacyDaggerEquivalence OrdinaryRigidification
open DaggerNativeOriginalCoherentUnitaryExistence
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeOriginalIntervalRUnitaryExistence
noncomputable section

variable (R : FunctorialFibrantReplacement.{u}) (H : DaggerUnitaryInterval.Interval.{u})
variable (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet _⦋0⦌)

theorem core_R_vertices_iff :
    Nonempty (((obj H) ⟶[SSet.{u}] DaggerActualDaggerCoreEndpointRestriction.target X x y) _⦋0⦌) ↔
      Nonempty (((obj H) ⟶[SSet.{u}] fullTarget R X x y) _⦋0⦌) := by
  have : IsCofibrant (obj H) := obj_cofibrant H
  have : WeakEquivalence (augmentation H) := augmentation_weak H
  have hk := all_nodes_kan R (obj H) X x y
  have := hk.1
  have := hk.2.1
  have := hk.2.2.1
  have := hk.2.2.2.1
  have := hk.2.2.2.2.1
  have := hk.2.2.2.2.2
  have hw := all_maps_weak R (obj H) X x y
  have := hw.1
  have := hw.2.1
  have := hw.2.2.1
  have := hw.2.2.2.1
  have := hw.2.2.2.2
  have hl := @vertices_nonempty_iff_of_weakEquivalence _ _ hk.1 hk.2.1
    (leftUnit R (obj H) X x y) hw.1
  have hp := @vertices_nonempty_iff_of_weakEquivalence _ _ hk.2.2.1 hk.2.1
    (postMap R (obj H) X x y) hw.2.1
  have hf := @vertices_nonempty_iff_of_weakEquivalence _ _ hk.2.2.2.1 hk.2.2.1
    (firstMap R (obj H) X x y) hw.2.2.1
  have hc := @vertices_nonempty_iff_of_weakEquivalence _ _ hk.2.2.2.1 hk.2.2.2.2.1
    (completionMap R (obj H) X x y) hw.2.2.2.1
  have hr := @vertices_nonempty_iff_of_weakEquivalence _ _ hk.2.2.2.2.2 hk.2.2.2.2.1
    (rightUnit R (obj H) X x y) hw.2.2.2.2
  let e := partIso R (obj H) (interval_hasActualComponentGroupoid (augmentation H)) X x y
  have he : Nonempty (((obj H) ⟶[SSet.{u}]
      DaggerActualOriginalFixedRCoreZigzag.replacedPart R X
        (DaggerActualOriginalBipointedRCoreZigzag.labels X x y)) _⦋0⦌) ↔
      Nonempty (((obj H) ⟶[SSet.{u}] fullTarget R X x y) _⦋0⦌) :=
    ⟨fun ⟨v⟩ ↦ ⟨e.hom.app (op ⦋0⦌) v⟩, fun ⟨v⟩ ↦ ⟨e.inv.app (op ⦋0⦌) v⟩⟩
  exact (hr.trans (hc.symm.trans (hf.trans (hp.trans hl.symm)))).trans he

theorem interval_R_vertices_iff_original_unitary :
    Nonempty (((obj H) ⟶[SSet.{u}] fullTarget R X x y) _⦋0⦌) ↔
      SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) := by
  have : IsCofibrant (obj H) := obj_cofibrant H
  have hk := all_nodes_kan R (obj H) X x y
  have := hk.2.2.2.2.2
  have := DaggerActualNativeIntervalFreeCoreMappingComparison.free_mapping_kan X x y
  have := DaggerActualNativeIntervalFreeCoreMappingComparison.freeToCoreMap_weak H X x y
  have hf := vertices_nonempty_iff_of_weakEquivalence
    (DaggerActualNativeIntervalFreeCoreMappingComparison.freeToCoreMap H X x y)
  exact ((core_R_vertices_iff R H X x y).symm.trans hf.symm).trans
    (free_vertices_iff_original_unitary X x y)

def intervalMapVertexEquiv :
    (H.C ⟶ R.functor.obj (twoObjectCopy (DaggerRigidification.obj X)
      (RigidificationVertices.vertexEquiv X.toSSet x)
      (RigidificationVertices.vertexEquiv X.toSSet y))) ≃
        (((obj H) ⟶[SSet.{u}] fullTarget R X x y) _⦋0⦌) :=
  ((legacyDaggerEquivalence DaggerUnitaryInterval.Vertex).toAdjunction.homEquiv (obj H)
    (R.functor.obj (twoObjectCopy (DaggerRigidification.obj X)
      (RigidificationVertices.vertexEquiv X.toSSet x)
      (RigidificationVertices.vertexEquiv X.toSSet y)))).trans
    (SimplicialCategory.homEquiv' (obj H) (fullTarget R X x y))

include H

theorem original_coherent_iff_original_unitary :
    (∃ z, CoherentlyUnitary R (DaggerRigidification.obj X)
      (RigidificationVertices.vertexEquiv X.toSSet x)
      (RigidificationVertices.vertexEquiv X.toSSet y) z) ↔
        SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) := by
  have hc := some_coherent_component_iff_interval_map R (DaggerRigidification.obj X)
    (RigidificationVertices.vertexEquiv X.toSSet x) (RigidificationVertices.vertexEquiv X.toSSet y)
  constructor
  · intro h
    obtain ⟨K, ⟨f⟩⟩ := hc.1 h
    exact (interval_R_vertices_iff_original_unitary R K X x y).1
      ⟨intervalMapVertexEquiv R K X x y f⟩
  · intro h
    obtain ⟨v⟩ := (interval_R_vertices_iff_original_unitary R H X x y).2 h
    exact hc.2 ⟨H, ⟨(intervalMapVertexEquiv R H X x y).symm v⟩⟩

omit H

theorem original_coherent_iff_original_unitary_unconditional :
    (∃ z, CoherentlyUnitary R (DaggerRigidification.obj X)
      (RigidificationVertices.vertexEquiv X.toSSet x)
      (RigidificationVertices.vertexEquiv X.toSSet y) z) ↔
        SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) := by
  obtain ⟨K⟩ := DaggerUnitaryInterval.exists_interval.{u}
  exact original_coherent_iff_original_unitary R K X x y

end
end DaggerNativeOriginalIntervalRUnitaryExistence
