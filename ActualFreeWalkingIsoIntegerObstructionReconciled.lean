import OriginalWalkingIsoCounitIntegerMapReconciled
import OriginalTaggedFreeZeroNativeWitness
import DaggerModels.DaggerAdjunction
import OriginalUnitaryCoherentAlgebraRecovered
import OriginalActualCoherentUnitaryIdentityRecovered
import OriginalActualGlobalWeakDefinitionsRecovered
import OriginalActualGlobalWeakPropertiesRecovered

/-!
# The literal free walking-isomorphism generator under actual dagger rigidification

The two adjoint transposes use the actual free dagger simplicial-set adjunction
and actual dagger rigidification adjunction. The target is the existing discrete
integer dagger groupoid. No ordinary free simplicial-category functor or free
comparison is introduced. The original two walking vertices are retained.
-/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels HomotopicalAlgebra
open DaggerUnitaryDiscrete DaggerUnitarySubgroupoid DaggerUnitaryInvariance
open DaggerModels.OrdinaryRigidification
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerModels.OriginalWalkingIsoCounitIntegerMap
open DaggerModels.OriginalWalkingIsoCoherentObstruction
open DaggerOriginalTaggedFreeZeroNativeWitness
universe u
namespace DaggerActualFreeWalkingIsoIntegerObstruction
noncomputable section

/-- The same ordinary walking-isomorphism nerve as in the manuscript. -/
abbrev J : SSet.{u} := nerve walkingIso.{u}

/-- The original integer dagger groupoid with discrete simplicial Hom spaces. -/
abbrev integerEnrichment : DaggerSimplicialCat.{u, u} := ordinaryEnrichment integerTarget.{u}

/-- The literal zero-vertex inclusion, before either free construction. -/
def zeroInclusion : (Δ[0] : SSet.{u}) ⟶ J.{u} :=
  SSet.const (ComposableArrows.mk₀ walkingZero.{u})

/-- The manuscript's literal free dagger simplicial-set arrow. -/
def freeGenerator : freeDagger.obj (Δ[0] : SSet.{u}) ⟶ freeDagger.obj J.{u} :=
  freeDagger.map zeroInclusion.{u}

/-- Extend the actual ordinary nerve map by the existing free--forgetful adjunction. -/
def freeNerveIntegerMap :
    freeDagger.obj J.{u} ⟶ DaggerNerve.daggerCoherentNerve.obj integerEnrichment.{u} :=
  (freeDaggerAdjunction.homEquiv J.{u}
    (DaggerNerve.daggerCoherentNerve.obj integerEnrichment.{u})).symm nerveZeroMap.{u}

/-- Restriction along the actual unit gives precisely the original ordinary nerve map. -/
theorem freeNerveIntegerMap_under_unit :
    freeDaggerAdjunction.unit.app J.{u} ≫ freeNerveIntegerMap.{u}.hom = nerveZeroMap.{u} := by
  exact (freeDaggerAdjunction.homEquiv_unit _ _ freeNerveIntegerMap.{u}).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- The actual dagger rigidification transpose of that full dagger map. -/
def integerMap : DaggerRigidification.daggerRigidification.obj (freeDagger.obj J.{u}) ⟶
    integerEnrichment.{u} :=
  (DaggerAdjunction.homEquiv _ _).symm freeNerveIntegerMap.{u}

/-- Its object formula uses the original unit-based rigidification vertex equivalence. -/
theorem integerMap_vertex
    (v : (freeDagger.obj J.{u}).toSSet.obj (op ⦋0⦌)) :
    integerMap.{u}.obj (RigidificationVertices.vertexEquiv _ v) =
      NerveVertices.vertexEquiv integerEnrichment.{u}.toSimplicialCat
        (freeNerveIntegerMap.{u}.hom.app (op ⦋0⦌) v) := by
  change ((rigidificationCoherentNerveAdjunction.homEquiv _ _).symm
    freeNerveIntegerMap.{u}.hom).obj _ = _
  rw [rigidificationCoherentNerveAdjunction.homEquiv_counit]
  change (rigidificationCoherentNerveAdjunction.counit.app _).obj
    ((rigidification.map freeNerveIntegerMap.{u}.hom).obj
      (RigidificationVertices.vertexEquiv _ v)) = _
  rw [RigidificationVertices.vertexEquiv_naturality]
  exact DaggerOriginalCounitObjects.counit_obj_vertex _ _

/-- Original vertices included by the actual free unit keep their original integer objects. -/
theorem integerMap_original_vertex (x : walkingIso.{u}) :
    integerMap.{u}.obj (RigidificationVertices.vertexEquiv _
      ((freeDaggerAdjunction.unit.app J.{u}).app (op ⦋0⦌) (ComposableArrows.mk₀ x))) =
        walkingToInteger.{u}.obj x := by
  rw [integerMap_vertex]
  have h := congrFun (NatTrans.congr_app freeNerveIntegerMap_under_unit.{u}
    (op ⦋0⦌)) (ComposableArrows.mk₀ x)
  change freeNerveIntegerMap.{u}.hom.app (op ⦋0⦌)
    ((freeDaggerAdjunction.unit.app J.{u}).app (op ⦋0⦌) (ComposableArrows.mk₀ x)) = _ at h
  rw [h]
  change NerveVertices.vertexEquiv _
    ((OrdinaryRigidification.coherentNerve.map walkingZeroEnriched.{u}).app (op ⦋0⦌)
      (OriginalWalkingIsoNerveComparison.comparisonIso.{u}.hom.app (op ⦋0⦌)
        (ComposableArrows.mk₀ x))) = _
  rw [NerveVertices.vertexEquiv_naturality]
  congr 1

/-- The original zero vertex inside the actual dagger rigidification of the free nerve. -/
def freeZero : (DaggerRigidification.daggerRigidification.obj (freeDagger.obj J.{u})).Obj :=
  RigidificationVertices.vertexEquiv _
    ((freeDaggerAdjunction.unit.app J.{u}).app (op ⦋0⦌) (ComposableArrows.mk₀ walkingZero))

/-- The original one vertex inside the same actual target. -/
def freeOne : (DaggerRigidification.daggerRigidification.obj (freeDagger.obj J.{u})).Obj :=
  RigidificationVertices.vertexEquiv _
    ((freeDaggerAdjunction.unit.app J.{u}).app (op ⦋0⦌) (ComposableArrows.mk₀ walkingOne))

/-- The transpose sends the original zero endpoint to the exact integer zero. -/
theorem integerMap_zero : integerMap.{u}.obj freeZero.{u} = integerZero.{u} :=
  integerMap_original_vertex walkingZero

/-- The transpose sends the original one endpoint to the exact integer one. -/
theorem integerMap_one : integerMap.{u}.obj freeOne.{u} = integerOne.{u} :=
  integerMap_original_vertex walkingOne

/-- Every simplex of the literal free zero-simplex is unique, by the specified point iso. -/
theorem freeZeroSimplex_subsingleton (q : SimplexCategoryᵒᵖ) :
    Subsingleton ((freeDagger.obj (Δ[0] : SSet.{u})).toSSet.obj q) := by
  constructor
  intro x y
  let e := DaggerSSet.forget.mapIso pointFreeZeroIso.{u}
  apply ((isIso_iff_bijective (e.inv.app q)).1 inferInstance).1
  change (e.inv.app q x : PUnit) = e.inv.app q y
  exact @Subsingleton.elim PUnit inferInstance _ _

/-- The rigidified literal free generator sends every source object to the original zero. -/
theorem rigidified_freeGenerator_obj
    (c : (DaggerRigidification.daggerRigidification.obj
      (freeDagger.obj (Δ[0] : SSet.{u}))).Obj) :
    (DaggerRigidification.daggerRigidification.map freeGenerator.{u}).obj c = freeZero.{u} := by
  let z : (Δ[0] : SSet.{u}).obj (op ⦋0⦌) := SSet.stdSimplex.obj₀Equiv.symm 0
  have : Subsingleton ((freeDagger.obj (Δ[0] : SSet.{u})).toSSet.obj (op ⦋0⦌)) :=
    freeZeroSimplex_subsingleton _
  obtain ⟨v, rfl⟩ := (RigidificationVertices.vertexEquiv
    (freeDagger.obj (Δ[0] : SSet.{u})).toSSet).surjective c
  have hv : v = (freeDaggerAdjunction.unit.app (Δ[0] : SSet.{u})).app (op ⦋0⦌) z :=
    Subsingleton.elim _ _
  change (rigidification.map freeGenerator.{u}.hom).obj _ = _
  rw [RigidificationVertices.vertexEquiv_naturality, hv]
  have h := congrFun (NatTrans.congr_app
    (freeDaggerAdjunction.unit.naturality zeroInclusion.{u}).symm (op ⦋0⦌)) z
  change freeGenerator.{u}.hom.app (op ⦋0⦌)
    ((freeDaggerAdjunction.unit.app (Δ[0] : SSet.{u})).app (op ⦋0⦌) z) =
      (freeDaggerAdjunction.unit.app J.{u}).app (op ⦋0⦌)
        (zeroInclusion.{u}.app (op ⦋0⦌) z) at h
  rw [h]
  congr 1

/-- The two retained endpoints have no coherent unitary in the actual rigidified target. -/
theorem free_noCoherentUnitary (R : FunctorialFibrantReplacement.{u})
    (v : SSet.π₀ ((DaggerRigidification.daggerRigidification.obj
      (freeDagger.obj J.{u})).enriched.Hom freeZero.{u} freeOne.{u})) :
    ¬ CoherentlyUnitary R (DaggerRigidification.daggerRigidification.obj
      (freeDagger.obj J.{u})) freeZero.{u} freeOne.{u} v := by
  intro hv
  have h := coherentlyUnitary_map R integerMap.{u} _ _ v hv
  rw [integerMap_zero, integerMap_one] at h
  exact integerTarget_noCoherentUnitary R _ h

/-- The actual rigidification of the literal manuscript generator fails coherent ESS. -/
theorem rigidified_freeGenerator_not_coherentlyEssentiallySurjective
    (R : FunctorialFibrantReplacement.{u}) :
    ¬ DaggerGlobalDK.CoherentlyEssentiallySurjective R
      (DaggerRigidification.daggerRigidification.map freeGenerator.{u}) := by
  intro h
  obtain ⟨c, v, hv⟩ := h freeOne.{u}
  generalize heq : (DaggerRigidification.daggerRigidification.map freeGenerator.{u}).obj c =
    z at v hv
  have hz : z = freeZero.{u} := heq.symm.trans (rigidified_freeGenerator_obj c)
  cases hz
  exact free_noCoherentUnitary R v hv

/-- Consequently the same actual map is not a dagger DK equivalence, for every replacement. -/
theorem rigidified_freeGenerator_not_daggerDK (R : FunctorialFibrantReplacement.{u}) :
    ¬ DaggerGlobalDK.daggerDK R
      (DaggerRigidification.daggerRigidification.map freeGenerator.{u}) := by
  intro h
  exact rigidified_freeGenerator_not_coherentlyEssentiallySurjective R h.2

end
end DaggerActualFreeWalkingIsoIntegerObstruction
