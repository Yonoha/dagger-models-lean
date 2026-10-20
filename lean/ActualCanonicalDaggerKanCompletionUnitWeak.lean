import ActualCanonicalDaggerKanCompletionUnit

/-! Native Kan weakness of the SAME canonical dagger completion unit.
No dagger cofibrancy or arbitrary choice of a replacement dagger is assumed.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialGroupoidCompletionDagger
open DaggerActualCanonicalDaggerKanCompletionUnit
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualCanonicalDaggerKanCompletionUnitWeak
noncomputable section

theorem target_locallyKan (K : DaggerSSet.{u}) (a b : (target K).Obj) :
    ((target K).enriched.Hom a b).KanComplex :=
  DaggerOriginalStrictSimplicialGroupoidMappingKan.completedHom_kan
    (DaggerRigidification.obj K).toSimplicialCat a b

theorem target_component_groupoid (K : DaggerSSet.{u}) [K.toSSet.KanComplex] :
    DaggerOriginalAmbientDaggerPiZeroGroupoid.HasActualComponentGroupoid
      (target K).toSimplicialCat :=
  DaggerOriginalPiZeroGroupoidLocalWeakInvariance.preserved
    (daggerLocalization (DaggerRigidification.obj K)).toEnrichedFunctor
    (fun a ↦ ⟨a, rfl⟩)
    (DaggerActualKanRigidificationCompletionWeak.localizationHom_weak K.toSSet)
    (DaggerActualKanRigidificationCompletionWeak.component_groupoid K.toSSet)

theorem target_nerve_kan (K : DaggerSSet.{u}) [K.toSSet.KanComplex] :
    (DaggerNerve.daggerCoherentNerve.obj (target K)).toSSet.KanComplex :=
  DaggerActualLocallyKanGroupoidalCoherentNerve.kan (target K).toSimplicialCat
    (target_locallyKan K) (target_component_groupoid K)

theorem unit_vertex_bijective (K : DaggerSSet.{u}) :
    Function.Bijective ((unit K).hom.app (op ⦋0⦌)) := by
  have he : (unit K).hom.app (op ⦋0⦌) =
      (NerveVertices.vertexEquiv (target K).toSimplicialCat).symm ∘
        RigidificationVertices.vertexEquiv K.toSSet := by
    funext x
    apply (NerveVertices.vertexEquiv (target K).toSimplicialCat).injective
    rw [vertex]
    exact (Equiv.apply_symm_apply _ _).symm
  rw [he]
  exact (NerveVertices.vertexEquiv (target K).toSimplicialCat).symm.bijective.comp
    (RigidificationVertices.vertexEquiv K.toSSet).bijective

theorem unit_rig_hom_weak (K : DaggerSSet.{u}) [K.toSSet.KanComplex]
    (a b : (rigidification.obj K.toSSet).Obj) :
    WeakEquivalence ((rigidification.map (unit K).hom).map a b) := by
  let F := rigidification.map (unit K).hom
  let e := rigidificationCoherentNerveAdjunction.counit.app (target K).toSimplicialCat
  have : WeakEquivalence (e.map (F.obj a) (F.obj b)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerActualRightConeRigidificationWeak.ordinary_counit_local
        (target K).toSimplicialCat (target_locallyKan K) (F.obj a) (F.obj b))
  have ht : ∀ c d, WeakEquivalence ((F ≫ e).map c d) := by
    change ∀ c d, WeakEquivalence
      ((rigidification.map (unit K).hom ≫
        rigidificationCoherentNerveAdjunction.counit.app (target K).toSimplicialCat).map c d)
    rw [triangle]
    exact DaggerActualKanRigidificationCompletionWeak.localizationHom_weak K.toSSet
  have : WeakEquivalence (F.map a b ≫ e.map (F.obj a) (F.obj b)) := ht a b
  exact weakEquivalence_of_postcomp (F.map a b) (e.map (F.obj a) (F.obj b))

theorem unit_weak (K : DaggerSSet.{u}) [K.toSSet.KanComplex] :
    WeakEquivalence (unit K).hom := by
  have := target_nerve_kan K
  exact DaggerNativeKanRigHomWeakRecognition.weak_of_rig_hom_weak_and_vertices
    (unit K).hom (unit_rig_hom_weak K) (unit_vertex_bijective K).surjective

end
end DaggerActualCanonicalDaggerKanCompletionUnitWeak
