import OriginalFixedObjectDaggerCategories
import Mathlib.CategoryTheory.Action.Basic

/-!
# Original fixed-object dagger groupoids and Fun(BC2, sGpd_O)

Each category has exactly O as object type, and each arrow has the identity object
function. The actual native C2 action category therefore fixes objects automatically.
Native inversion gives the full, faithful and essentially surjective comparison;
Mathlib's existing action-functor-category equivalence gives the actual BC2 diagram
category. No fixed-object model structure or simplicial enrichment is postulated.
-/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalStrictDaggerGroupoidSigma
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictGroupoidDaggerInvolutionEquivalence
open DaggerOriginalStrictGroupoidObjectFixedC2Actions
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
universe u

namespace DaggerOriginalFixedObjectDaggerActionEquivalence

noncomputable section

/-- The inverse of the original fixed dagger is an original identity-object-function functor. -/
def fixedSigmaHom {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    FixedHom C.obj.underlying C.obj.underlying where
  map := strictSigmaHom (originalDagger C.obj) C.property
  map_id := (strictSigmaFunctor (originalDagger C.obj) C.property).map_id
  map_comp := (strictSigmaFunctor (originalDagger C.obj) C.property).map_comp

/-- The whole inverse-dagger functor is an endomorphism in the actual fixed-object groupoid
category.
-/
def fixedSigmaEnd {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    End ((fixedStrictDaggerForget O).obj C) := End.of (ObjectProperty.homMk (fixedSigmaHom C))

/-- Its square is the original identity in the fixed-object category. -/
theorem fixedSigmaEnd_mul_self {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    fixedSigmaEnd C * fixedSigmaEnd C = 1 := by
  apply ObjectProperty.hom_ext _
  apply originalHom_injective
  exact strictSigmaFunctor_involutive (originalDagger C.obj) C.property

/-- The unchanged original C2 acts on the entire actual fixed-object groupoid. -/
def fixedDaggerRepresentation {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    C2.{u} →* End ((fixedStrictDaggerForget O).obj C) where
  toFun g := if g = 1 then 1 else fixedSigmaEnd C
  map_one' := by simp
  map_mul' g h := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    rcases originalC2_cases h with rfl | rfl
    · simp
    change (if generator * generator = 1 then 1 else fixedSigmaEnd C) =
      (if generator = 1 then 1 else fixedSigmaEnd C) *
        (if generator = 1 then 1 else fixedSigmaEnd C)
    rw [originalGenerator_mul_self, if_pos rfl, if_neg originalGenerator_ne_one]
    exact (fixedSigmaEnd_mul_self C).symm

/-- The native fixed-object action generator is exactly the whole original inverse dagger. -/
theorem fixedDaggerRepresentation_generator {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    fixedDaggerRepresentation C generator = fixedSigmaEnd C := by
  simp [fixedDaggerRepresentation, originalGenerator_ne_one]

/-- The generator retains the exact original enriched functor after forgetting fixed-object data. -/
theorem fixedDaggerRepresentation_generator_original {O : Type u}
    (C : FixedStrictDaggerGroupoids O) :
    originalHom ((fixedDaggerRepresentation C generator).asHom.hom) =
      strictSigmaFunctor (originalDagger C.obj) C.property := by
  rw [fixedDaggerRepresentation_generator]
  rfl

/-- The comparison into the actual full native C2 action category on sGpd_O. -/
def fixedDaggerToAction (O : Type u) :
    FixedStrictDaggerGroupoids O ⥤ Action (FixedStrictGroupoids O) C2.{u} where
  obj C := ⟨(fixedStrictDaggerForget O).obj C, fixedDaggerRepresentation C⟩
  map {C D} F :=
    { hom := ObjectProperty.homMk F.hom.underlying
      comm g := by
        rcases originalC2_cases g with rfl | rfl
        · simp
        · apply ObjectProperty.hom_ext _
          apply originalHom_injective
          change originalHom ((fixedDaggerRepresentation C generator).asHom.hom) ≫
              originalHom F.hom.underlying =
            originalHom F.hom.underlying ≫
              originalHom ((fixedDaggerRepresentation D generator).asHom.hom)
          rw [fixedDaggerRepresentation_generator_original,
            fixedDaggerRepresentation_generator_original]
          apply EnrichedFunctor.ext SSet.{u}
            (F := strictSigmaFunctor (originalDagger C.obj) C.property ≫
              originalHom F.hom.underlying)
            (G := originalHom F.hom.underlying ≫
              strictSigmaFunctor (originalDagger D.obj) D.property) (fun _ ↦ rfl)
          intro x y
          simpa only [eqToHom_refl, Category.comp_id] using
            strictSigmaHom_functor (C := originalDagger C.obj) (D := originalDagger D.obj)
              C.property D.property (originalDaggerHom F.hom) x y }

/-- The native action comparison is faithful on the same original fixed dagger functors. -/
instance fixedDaggerToAction_faithful (O : Type u) : (fixedDaggerToAction O).Faithful where
  map_injective h := ObjectProperty.hom_ext _
    (fixedDaggerHom_ext (congrArg (fun G ↦ G.hom.hom) h))

/-- Every native equivariant fixed-object arrow is an original fixed dagger arrow. -/
instance fixedDaggerToAction_full (O : Type u) : (fixedDaggerToAction O).Full where
  map_surjective {C D} G := by
    let F := G.hom.hom
    have hd : PreservesDagger C.obj.dagger D.obj.dagger (originalHom F) := by
      apply (preservesDagger_iff_preservesInvolution C.property D.property
        C.obj.dagger D.obj.dagger (originalHom F)).mpr
      have hc := congrArg (fun k : (fixedStrictDaggerForget O).obj C ⟶
        (fixedStrictDaggerForget O).obj D ↦ originalHom k.hom) (G.comm generator)
      change originalHom ((fixedDaggerRepresentation C generator).asHom.hom) ≫ originalHom F =
        originalHom F ≫ originalHom ((fixedDaggerRepresentation D generator).asHom.hom) at hc
      rw [fixedDaggerRepresentation_generator_original,
        fixedDaggerRepresentation_generator_original] at hc
      intro x y
      exact eq_of_heq (enrichedFunctor_map_heq hc x y)
    exact ⟨ObjectProperty.homMk ⟨F, hd⟩, rfl⟩

/-- Native group action laws make the same original fixed-object generator involutive. -/
theorem fixedActionGenerator_square {O : Type u}
    (A : Action (FixedStrictGroupoids O) C2.{u}) :
    originalHom (A.ρ generator).asHom.hom ≫ originalHom (A.ρ generator).asHom.hom =
      𝟙 (original O A.V.obj) := by
  have h : A.ρ generator * A.ρ generator = 1 := by
    rw [← A.ρ.map_mul, originalGenerator_mul_self, A.ρ.map_one]
  exact congrArg (fun k : End A.V ↦ originalHom k.asHom.hom) h

/-- The complete native fixed-object action recovers the same original covariant involution. -/
def involutionOfFixedAction {O : Type u} (A : Action (FixedStrictGroupoids O) C2.{u}) :
    ObjectFixedInvolution (original O A.V.obj) :=
  involutionOfFixedFunctor (original O A.V.obj) (originalHom (A.ρ generator).asHom.hom)
    (fun _ ↦ rfl) (fixedActionGenerator_square A)

/-- Recover the original dagger on the exact fixed-object groupoid of a native action. -/
def fixedDaggerOfAction {O : Type u} (A : Action (FixedStrictGroupoids O) C2.{u}) :
    FixedStrictDaggerGroupoids O :=
  ⟨⟨A.V.obj,
    daggerOfInvolution (original O A.V.obj) A.V.property (involutionOfFixedAction A)⟩,
    A.V.property⟩

/-- Recovery preserves the entire original generator enriched functor on the fixed objects. -/
theorem recovered_fixedSigmaFunctor {O : Type u}
    (A : Action (FixedStrictGroupoids O) C2.{u}) :
    strictSigmaFunctor (originalDagger (fixedDaggerOfAction A).obj)
      (fixedDaggerOfAction A).property = originalHom (A.ρ generator).asHom.hom := by
  change involutionFunctor (original O A.V.obj)
    (involutionOfDagger (original O A.V.obj) A.V.property
      (daggerOfInvolution (original O A.V.obj) A.V.property (involutionOfFixedAction A))) = _
  rw [involutionOfDagger_ofInvolution]
  exact involutionOfFixedFunctor_functor _ _ _ _

/-- The actual fixed-object native action is recovered exactly, including the whole representation.
-/
theorem fixedDaggerToAction_ofAction {O : Type u}
    (A : Action (FixedStrictGroupoids O) C2.{u}) :
    (fixedDaggerToAction O).obj (fixedDaggerOfAction A) = A := by
  apply (Action.mk.injEq _ _ _ _).mpr
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  apply MonoidHom.ext
  intro g
  rcases originalC2_cases g with rfl | rfl
  · exact (fixedDaggerRepresentation (fixedDaggerOfAction A)).map_one.trans A.ρ.map_one.symm
  · apply ObjectProperty.hom_ext _
    apply originalHom_injective
    change originalHom ((fixedDaggerRepresentation (fixedDaggerOfAction A) generator).asHom.hom) =
      originalHom (A.ρ generator).asHom.hom
    rw [fixedDaggerRepresentation_generator_original]
    exact recovered_fixedSigmaFunctor A

/-- Every actual BC2 action on an original fixed-object groupoid comes from a fixed dagger. -/
instance fixedDaggerToAction_essSurj (O : Type u) : (fixedDaggerToAction O).EssSurj where
  mem_essImage A := ⟨fixedDaggerOfAction A, ⟨eqToIso (fixedDaggerToAction_ofAction A)⟩⟩

instance fixedDaggerToAction_isEquivalence (O : Type u) :
    (fixedDaggerToAction O).IsEquivalence := {}

/-- Full equivalence of the original fixed-object dagger groupoids with the actual C2 action
category.
-/
def fixedDaggerActionEquivalence (O : Type u) :
    FixedStrictDaggerGroupoids O ≌ Action (FixedStrictGroupoids O) C2.{u} :=
  (fixedDaggerToAction O).asEquivalence

/-- The exact ordinary-category version of the paper's Fun(BC2,sGpd_O) correspondence. -/
def fixedDaggerFunctorCategoryEquivalence (O : Type u) :
    FixedStrictDaggerGroupoids O ≌ (SingleObj C2.{u} ⥤ FixedStrictGroupoids O) :=
  (fixedDaggerActionEquivalence O).trans
    (Action.functorCategoryEquivalence (FixedStrictGroupoids O) C2.{u})

end

end DaggerOriginalFixedObjectDaggerActionEquivalence
