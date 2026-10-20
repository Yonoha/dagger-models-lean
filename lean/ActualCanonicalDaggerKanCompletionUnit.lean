import ActualNativeIntervalFreeCoreMappingComparison
import NativeKanRigHomWeakRecognition
import ActualLocallyKanGroupoidalCoherentNerve

/-! Canonical ORIGINAL dagger adjunction mate of the full completion localization.
The whole underlying map, counit triangle and every original vertex are retained.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialGroupoidCompletionDagger
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualCanonicalDaggerKanCompletionUnit
noncomputable section

def target (K : DaggerSSet.{u}) : DaggerSimplicialCat.{u, u} :=
  daggerCompletion (DaggerRigidification.obj K)

def unit (K : DaggerSSet.{u}) : K ⟶ DaggerNerve.daggerCoherentNerve.obj (target K) :=
  DaggerActualRigidificationQuillen.adjunction.homEquiv K (target K)
    (daggerLocalization (DaggerRigidification.obj K))

theorem underlying (K : DaggerSSet.{u}) :
    (unit K).hom = rigidificationCoherentNerveAdjunction.homEquiv K.toSSet
      (target K).toSimplicialCat
      (daggerLocalization (DaggerRigidification.obj K)).toEnrichedFunctor := by
  simpa [unit] using (daggerRigidificationLiftWitness.homEquiv_compatibility K (target K)
    (daggerLocalization (DaggerRigidification.obj K))).symm

theorem triangle (K : DaggerSSet.{u}) :
    rigidification.map (unit K).hom ≫
        rigidificationCoherentNerveAdjunction.counit.app (target K).toSimplicialCat =
      (daggerLocalization (DaggerRigidification.obj K)).toEnrichedFunctor := by
  rw [underlying]
  let e := rigidificationCoherentNerveAdjunction.homEquiv K.toSSet
    (target K).toSimplicialCat
  exact (rigidificationCoherentNerveAdjunction.homEquiv_counit K.toSSet
    (target K).toSimplicialCat
    (e (daggerLocalization (DaggerRigidification.obj K)).toEnrichedFunctor)).symm.trans
      (e.symm_apply_apply _)

theorem vertex (K : DaggerSSet.{u}) (x : K.toSSet.obj (op ⦋0⦌)) :
    NerveVertices.vertexEquiv (target K).toSimplicialCat ((unit K).hom.app (op ⦋0⦌) x) =
      RigidificationVertices.vertexEquiv K.toSSet x := by
  rw [underlying]
  rfl

end
end DaggerActualCanonicalDaggerKanCompletionUnit
