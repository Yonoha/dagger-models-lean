import OrdinaryRigidificationCof
import OriginalCofibrantLocalizationCriterion

/-! The actual ordinary rigidification is cofibrant with its original object set fixed. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerOriginalFixedObjectSimplicialCategories
open DaggerOriginalAmbientDaggerForgetCofibrancy
open DaggerOriginalCofibrantDegreeFreeRetract DaggerSSetGluing
open scoped SSet.modelCategoryQuillen DaggerOriginalAmbientDaggerForgetCofibrancy
universe u
namespace DaggerActualOrdinaryRigidificationFixedCofibrancy
noncomputable section

/-- Keep the entire actual enrichment and the original rigidification objects. -/
def fixed (X : SSet.{u}) : FixedSimplicialCategory (rigidification.obj X).Obj :=
  ⟨(rigidification.obj X).enriched⟩

theorem original_fixed (X : SSet.{u}) :
    original (rigidification.obj X).Obj (fixed X) = rigidification.obj X := rfl

/-- The actual adjunction proves initiality of the rigidification of the empty input. -/
def initialIsInitial : IsInitial (rigidification.obj (⊥_ SSet.{u})) :=
  IsInitial.ofUniqueHom
    (fun D ↦ (rigidificationCoherentNerveAdjunction.homEquiv _ D).symm
      (initial.to (coherentNerve.obj D))) (by
        intro D F
        apply (rigidificationCoherentNerveAdjunction.homEquiv _ D).injective
        exact Limits.initialIsInitial.hom_ext _ _)

theorem originalHom_fixedHomOfIdentity {O : Type u} {C D : FixedSimplicialCategory O}
    (F : original O C ⟶ original O D) (hF : F.obj = id) :
    originalHom (fixedHomOfIdentity F hF) = F := by
  rcases F with ⟨obj, map, hi, hc⟩
  change obj = id at hF
  subst obj
  rfl

/-- The native global lift has identity object map because the tested fixed map does. -/
theorem exists_fixed_lift (X : SSet.{u})
    {A B : FixedSimplicialCategory (rigidification.obj X).Obj} (p : A ⟶ B)
    (hp : ordinaryTrivialFibrations _ p) (g : fixed X ⟶ B) :
    ∃ l : fixed X ⟶ A, l ≫ p = g := by
  have hlp : HasLiftingProperty (rigidification.map (initial.to X)) (originalHom p) :=
    DaggerOrdinaryRigidificationCof.mono_rigidification_lifting (initial.to X)
      (originalHom p) (fun x ↦ ⟨x, rfl⟩) (by
        intro x y
        obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp (hp x y)
        exact ⟨hf, (weakEquivalence_iff_GW _).mp hw⟩)
  let sq : CommSq (initialIsInitial.to (original _ A))
      (rigidification.map (initial.to X)) (originalHom p) (originalHom g) :=
    ⟨initialIsInitial.hom_ext _ _⟩
  have : sq.HasLift := hlp.sq_hasLift sq
  have ho : sq.lift.obj = id := by
    funext x
    exact congrFun (congrArg (fun F ↦ F.obj) sq.fac_right) x
  refine ⟨fixedHomOfIdentity (C := fixed X) (D := A) sq.lift ho, ?_⟩
  apply originalHom_injective
  change originalHom (fixedHomOfIdentity (C := fixed X) (D := A) sq.lift ho) ≫
    originalHom p = originalHom g
  rw [originalHom_fixedHomOfIdentity]
  exact sq.fac_right

/-- This is the original fixed-object LLP cofibrancy, with no extra hypothesis on `X`. -/
theorem fixed_isCofibrant (X : SSet.{u}) : IsCofibrant (fixed X) := by
  rw [isCofibrant_iff, cofibration_iff]
  intro A B p hp
  constructor
  intro t g sq
  obtain ⟨l, hl⟩ := exists_fixed_lift X p hp g
  exact CommSq.HasLift.mk' ⟨l, Limits.initialIsInitial.hom_ext _ _, hl⟩

end
end DaggerActualOrdinaryRigidificationFixedCofibrancy
