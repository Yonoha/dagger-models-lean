import OriginalStrictDaggerInvolutionCategoryEquivalence
import OriginalSimplicialGroupoidCompletionAdjunction

/-!
# Object-fixing C2 actions on the actual original strict simplicial groupoid

Actions use Mathlib's original End monoid in the full subcategory of the original
strict simplicial groupoids. Only the explicitly object-fixing actions correspond
to dagger on the same category. The equivalence is on complete action data, not just
on Hom-wise involutions, and retains the original C2 and the exact original functors.
-/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionAdjunction
open DaggerOriginalStrictGroupoidDaggerInvolutionEquivalence
universe u

namespace DaggerOriginalStrictGroupoidObjectFixedC2Actions

noncomputable section

/-- Whole original enriched-functor equality retains its dependent original Hom maps. -/
theorem enrichedFunctor_map_heq {C D : SimplicialCat.{u, u}} {F G : C ⟶ D}
    (h : F = G) (x y : C.Obj) : HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

/-- Normalize an actual object-fixing involutive original enriched functor on its exact Hom. -/
def involutionOfFixedFunctor (C : SimplicialCat.{u, u}) (F : C ⟶ C)
    (hobj : ∀ x, F.obj x = x) (hsquare : F ≫ F = 𝟙 C) : ObjectFixedInvolution C := by
  cases F with
  | mk obj map hid hcomp =>
      have ho : obj = id := funext hobj
      cases ho
      refine ⟨map, hid, hcomp, ?_⟩
      intro x y
      exact eq_of_heq (enrichedFunctor_map_heq hsquare x y)

/-- Normalization preserves the entire actual original enriched functor. -/
theorem involutionOfFixedFunctor_functor (C : SimplicialCat.{u, u}) (F : C ⟶ C)
    (hobj : ∀ x, F.obj x = x) (hsquare : F ≫ F = 𝟙 C) :
    involutionFunctor C (involutionOfFixedFunctor C F hobj hsquare) = F := by
  cases F with
  | mk obj map hid hcomp =>
      have ho : obj = id := funext hobj
      cases ho
      rfl

/-- The actual groupoid object, with its unchanged original enriched category. -/
def strictObject (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :
    StrictSimplicialGroupoids.{u} := ⟨C, hC⟩

/-- The whole original object-fixing involution is an actual strict-groupoid endomorphism. -/
def involutionEnd (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (s : ObjectFixedInvolution C) : End (strictObject C hC) :=
  End.of (ObjectProperty.homMk (involutionFunctor C s))

/-- The actual original strict-groupoid endomorphism squares to the identity. -/
theorem involutionEnd_mul_self (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (s : ObjectFixedInvolution C) : involutionEnd C hC s * involutionEnd C hC s = 1 := by
  apply (strictHomEquiv _ _).injective
  exact involutionFunctor_involutive C s

/-- The original acting group acts on the entire original strict simplicial groupoid. -/
def involutionC2Representation (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (s : ObjectFixedInvolution C) : C2.{u} →* End (strictObject C hC) where
  toFun g := if g = 1 then 1 else involutionEnd C hC s
  map_one' := by simp
  map_mul' g h := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    rcases originalC2_cases h with rfl | rfl
    · simp
    change (if generator * generator = 1 then 1 else involutionEnd C hC s) =
      (if generator = 1 then 1 else involutionEnd C hC s) *
        (if generator = 1 then 1 else involutionEnd C hC s)
    rw [originalGenerator_mul_self, if_pos rfl, if_neg originalGenerator_ne_one]
    exact (involutionEnd_mul_self C hC s).symm

/-- The original generator is exactly the whole original enriched involution. -/
theorem involutionC2Representation_generator (C : SimplicialCat.{u, u})
    (hC : IsStrictGroupoid C) (s : ObjectFixedInvolution C) :
    ((involutionC2Representation C hC s generator).asHom).hom = involutionFunctor C s := by
  simp [involutionC2Representation, originalGenerator_ne_one, involutionEnd]

/-- Only representations fixing all original objects are included in the dagger correspondence. -/
def ObjectFixedC2Representation (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :=
  {ρ : C2.{u} →* End (strictObject C hC) // ∀ x, (ρ generator).asHom.hom.obj x = x}

/-- The constructed whole representation fixes every original object. -/
def fixedRepresentationOfInvolution (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (s : ObjectFixedInvolution C) : ObjectFixedC2Representation C hC :=
  ⟨involutionC2Representation C hC s, by
    intro x
    rw [involutionC2Representation_generator]
    rfl⟩

/-- The actual original generator of any C2 representation is a whole involutive functor. -/
theorem representationGenerator_square (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (ρ : C2.{u} →* End (strictObject C hC)) :
    (ρ generator).asHom.hom ≫ (ρ generator).asHom.hom = 𝟙 C := by
  have h : ρ generator * ρ generator = 1 := by
    rw [← ρ.map_mul, originalGenerator_mul_self, ρ.map_one]
  exact congrArg (fun k : End (strictObject C hC) ↦ k.asHom.hom) h

/-- Recover the original object-fixing involution from the entire actual representation. -/
def involutionOfFixedRepresentation (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (ρ : ObjectFixedC2Representation C hC) : ObjectFixedInvolution C :=
  involutionOfFixedFunctor C (ρ.val generator).asHom.hom ρ.property
    (representationGenerator_square C hC ρ.val)

/-- Recovery retains exactly the actual original generator functor, including all Hom maps. -/
theorem involutionOfFixedRepresentation_functor (C : SimplicialCat.{u, u})
    (hC : IsStrictGroupoid C) (ρ : ObjectFixedC2Representation C hC) :
    involutionFunctor C (involutionOfFixedRepresentation C hC ρ) =
      (ρ.val generator).asHom.hom :=
  involutionOfFixedFunctor_functor C _ _ _

/-- Recovering from the action returns the complete original involution data. -/
theorem involutionOfFixedRepresentation_ofInvolution (C : SimplicialCat.{u, u})
    (hC : IsStrictGroupoid C) (s : ObjectFixedInvolution C) :
    involutionOfFixedRepresentation C hC (fixedRepresentationOfInvolution C hC s) = s := by
  apply objectFixedInvolution_ext C
  intro x y
  have hf := involutionOfFixedRepresentation_functor C hC
    (fixedRepresentationOfInvolution C hC s)
  change involutionFunctor C (involutionOfFixedRepresentation C hC
      (fixedRepresentationOfInvolution C hC s)) =
    (involutionC2Representation C hC s generator).asHom.hom at hf
  rw [involutionC2Representation_generator] at hf
  exact eq_of_heq (enrichedFunctor_map_heq hf x y)

/-- Recovering from the involution returns the entire original C2 representation. -/
theorem fixedRepresentationOfInvolution_ofRepresentation (C : SimplicialCat.{u, u})
    (hC : IsStrictGroupoid C) (ρ : ObjectFixedC2Representation C hC) :
    fixedRepresentationOfInvolution C hC (involutionOfFixedRepresentation C hC ρ) = ρ := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro g
  rcases originalC2_cases g with rfl | rfl
  · exact (involutionC2Representation C hC _).map_one.trans ρ.val.map_one.symm
  · apply (strictHomEquiv _ _).injective
    change (involutionC2Representation C hC (involutionOfFixedRepresentation C hC ρ)
      generator).asHom.hom = (ρ.val generator).asHom.hom
    rw [involutionC2Representation_generator, involutionOfFixedRepresentation_functor]

/-- The full covariant structure is equivalent to the full object-fixing native representation.
-/
def involutionFixedC2Equiv (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :
    ObjectFixedInvolution C ≃ ObjectFixedC2Representation C hC where
  toFun := fixedRepresentationOfInvolution C hC
  invFun := involutionOfFixedRepresentation C hC
  left_inv := involutionOfFixedRepresentation_ofInvolution C hC
  right_inv := fixedRepresentationOfInvolution_ofRepresentation C hC

/-- Dagger on the exact original strict groupoid is equivalent to an object-fixing C2 action. -/
def daggerFixedC2Equiv (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :
    (@DaggerSimplicialStructure C.Obj C.enriched) ≃ ObjectFixedC2Representation C hC :=
  (daggerInvolutionEquiv C hC).trans (involutionFixedC2Equiv C hC)

/-- Bundle the same original representation into Mathlib's native action category. -/
def nativeFixedAction (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (ρ : ObjectFixedC2Representation C hC) : Action StrictSimplicialGroupoids.{u} C2.{u} :=
  ⟨strictObject C hC, ρ.val⟩

end

end DaggerOriginalStrictGroupoidObjectFixedC2Actions
