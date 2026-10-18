import OriginalStrictGroupoidObjectFixedC2Actions

/-!
# Full categorical correspondence with actual object-fixing C2 actions

Use the native action category on the original strict simplicial groupoids, restricted
by the explicitly object-fixing generator. Morphisms are full native equivariant
functors. The comparison is full, faithful and essentially surjective; composing it
with inverse dagger gives the full original strict dagger category equivalence.
Fixed-object model structures and their transport are separate, unproved obligations.
-/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionAdjunction
open DaggerOriginalSimplicialDaggerGroupoidCompletionAdjunction
open DaggerOriginalStrictGroupoidDaggerInvolutionEquivalence
open DaggerOriginalStrictDaggerInvolutionCategoryEquivalence
open DaggerOriginalStrictGroupoidObjectFixedC2Actions
universe u

namespace DaggerOriginalStrictDaggerObjectFixedActionCategory

noncomputable section

/-- Native actions whose original generator fixes all objects of the original groupoid. -/
def IsObjectFixedAction (A : Action StrictSimplicialGroupoids.{u} C2.{u}) : Prop :=
  ∀ x, (A.ρ generator).asHom.hom.obj x = x

/-- The actual full subcategory of the native original-groupoid C2 action category. -/
abbrev ObjectFixedActions := ObjectProperty.FullSubcategory IsObjectFixedAction.{u}

/-- Hom-wise original equivariance is equality of the full original enriched functors. -/
theorem involutionFunctor_comm {C D : SimplicialCat.{u, u}}
    (s : ObjectFixedInvolution C) (t : ObjectFixedInvolution D) (F : C ⟶ D)
    (h : PreservesInvolution s t F) :
    involutionFunctor C s ≫ F = F ≫ involutionFunctor D t := by
  apply EnrichedFunctor.ext SSet.{u}
    (F := involutionFunctor C s ≫ F) (G := F ≫ involutionFunctor D t) (fun _ ↦ rfl)
  intro x y
  simpa only [eqToHom_refl, Category.comp_id] using h x y

/-- The covariant original involution gives an actual object-fixing native action object. -/
def actionOfInvolutiveGroupoid (C : StrictInvolutiveGroupoid.{u}) : ObjectFixedActions.{u} :=
  ⟨nativeFixedAction C.underlying C.strict
    (fixedRepresentationOfInvolution C.underlying C.strict C.involution), by
      intro x
      change (involutionC2Representation C.underlying C.strict C.involution generator).asHom.hom.obj
        x = x
      rw [involutionC2Representation_generator]
      rfl⟩

/-- The comparison retains each full original enriched functor as the native equivariant map. -/
def involutionToFixedAction : StrictInvolutiveGroupoid.{u} ⥤ ObjectFixedActions.{u} where
  obj := actionOfInvolutiveGroupoid
  map {C D} F := ObjectProperty.homMk
    { hom := ObjectProperty.homMk F.underlying
      comm g := by
        rcases originalC2_cases g with rfl | rfl
        · simp
        · apply (strictHomEquiv _ _).injective
          change (involutionC2Representation C.underlying C.strict C.involution
              generator).asHom.hom ≫ F.underlying =
            F.underlying ≫ (involutionC2Representation D.underlying D.strict D.involution
              generator).asHom.hom
          rw [involutionC2Representation_generator, involutionC2Representation_generator]
          exact involutionFunctor_comm C.involution D.involution F.underlying F.equivariant }

/-- Faithfulness retains equality of each full original enriched functor. -/
instance involutionToFixedAction_faithful : involutionToFixedAction.{u}.Faithful where
  map_injective h := involutiveHom_ext (congrArg (fun G ↦ G.hom.hom.hom) h)

/-- Every native equivariant arrow between these action objects is an original equivariant map. -/
instance involutionToFixedAction_full : involutionToFixedAction.{u}.Full where
  map_surjective {C D} G := by
    let F := G.hom.hom.hom
    have h : PreservesInvolution C.involution D.involution F := by
      have hc := congrArg (fun k : strictObject C.underlying C.strict ⟶
        strictObject D.underlying D.strict ↦ k.hom) (G.hom.comm generator)
      change (involutionC2Representation C.underlying C.strict C.involution
          generator).asHom.hom ≫ F =
        F ≫ (involutionC2Representation D.underlying D.strict D.involution
          generator).asHom.hom at hc
      rw [involutionC2Representation_generator, involutionC2Representation_generator] at hc
      intro x y
      exact eq_of_heq (enrichedFunctor_map_heq hc x y)
    exact ⟨⟨F, h⟩, rfl⟩

/-- Any original object-fixing native action reconstructs a full original involutive groupoid. -/
def involutiveGroupoidOfAction (A : ObjectFixedActions.{u}) : StrictInvolutiveGroupoid.{u} :=
  ⟨A.obj.V.obj, A.obj.V.property,
    involutionOfFixedRepresentation A.obj.V.obj A.obj.V.property ⟨A.obj.ρ, A.property⟩⟩

/-- Reconstruction returns the entire actual action object, including its whole representation. -/
theorem actionOfInvolutiveGroupoid_ofAction (A : ObjectFixedActions.{u}) :
    actionOfInvolutiveGroupoid (involutiveGroupoidOfAction A) = A := by
  apply ObjectProperty.FullSubcategory.ext
  have hr := congrArg Subtype.val
    (fixedRepresentationOfInvolution_ofRepresentation A.obj.V.obj A.obj.V.property
      ⟨A.obj.ρ, A.property⟩)
  apply (Action.mk.injEq _ _ _ _).mpr
  exact ⟨rfl, heq_of_eq hr⟩

/-- Essential surjectivity is witnessed by the exact reconstruction of each native action. -/
instance involutionToFixedAction_essSurj : involutionToFixedAction.{u}.EssSurj where
  mem_essImage A := ⟨involutiveGroupoidOfAction A,
    ⟨eqToIso (actionOfInvolutiveGroupoid_ofAction A)⟩⟩

instance involutionToFixedAction_isEquivalence : involutionToFixedAction.{u}.IsEquivalence := {}

/-- Full category equivalence with actual native actions satisfying the object-fixing condition.
-/
def involutionFixedActionEquivalence : StrictInvolutiveGroupoid.{u} ≌ ObjectFixedActions.{u} :=
  involutionToFixedAction.asEquivalence

/-- The full original strict dagger category corresponds to the full native object-fixing actions.
-/
def strictDaggerFixedActionEquivalence :
    StrictDaggerSimplicialGroupoids.{u} ≌ ObjectFixedActions.{u} :=
  strictDaggerInvolutionEquivalence.trans involutionFixedActionEquivalence

end

end DaggerOriginalStrictDaggerObjectFixedActionCategory
