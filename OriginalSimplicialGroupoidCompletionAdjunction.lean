import OriginalSimplicialGroupoidCompletionUniversal
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The actual completion-inclusion adjunction for original simplicial groupoids

The native groupoid-completion uniqueness theorem proves uniqueness of the full original
simplicial extension, including all object and Hom maps. Its full Hom equivalence is natural
on the original simplicial categories and strict simplicial groupoids. Bundle the actual
strict-groupoid full subcategory and the original completion functor into their adjunction.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionFunctor
open DaggerOriginalSimplicialGroupoidCompletionUniversal

universe u

namespace DaggerOriginalSimplicialGroupoidCompletionAdjunction

noncomputable section

/-- The original completed degree category has exactly the native free-groupoid objects and maps.
-/
def completedDegreeProjection (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    FreeGroupoid (degreeObjects C n) ⥤ degreeObjects (completion C) n where
  obj x := x.as.as
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original full simplicial extension is uniquely determined by its localization composite.
-/
theorem lift_unique {C D : SimplicialCat.{u, u}} (hD : IsStrictGroupoid D) (F : C ⟶ D)
    (Φ : completion C ⟶ D) (hΦ : localization C ≫ Φ = F) : Φ = lift hD F := by
  subst F
  refine EnrichedFunctor.ext SSet.{u} (F := Φ) (G := lift hD (localization C ≫ Φ))
    (fun _ ↦ rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  ext n f
  letI := strictDegreeGroupoid D hD n
  have h := FreeGroupoid.lift_unique (degreeFunctor (localization C ≫ Φ) n)
    (completedDegreeProjection C n ⋙ degreeFunctor Φ n) (by rfl)
  have hh := CategoryTheory.Functor.congr_hom h f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.comp_map] using hh

/-- The full original completion-inclusion Hom equivalence has no preservation assumptions. -/
def completionHomEquiv (C D : SimplicialCat.{u, u}) (hD : IsStrictGroupoid D) :
    (completion C ⟶ D) ≃ (C ⟶ D) where
  toFun Φ := localization C ≫ Φ
  invFun := lift hD
  left_inv Φ := (lift_unique hD (localization C ≫ Φ) Φ rfl).symm
  right_inv F := lift_spec hD F

/-- The original strict simplicial groupoids form the actual full subcategory. -/
abbrev StrictSimplicialGroupoids := ObjectProperty.FullSubcategory IsStrictGroupoid.{u}

/-- Native full-subcategory morphisms retain the exact full original simplicial functors. -/
def strictHomEquiv (C D : StrictSimplicialGroupoids.{u}) : (C ⟶ D) ≃ (C.obj ⟶ D.obj) where
  toFun f := f.hom
  invFun := ObjectProperty.homMk
  left_inv f := by cases f; rfl
  right_inv _ := rfl

/-- Inclusion retains each original simplicial groupoid and every original simplicial functor.
-/
def inclusion : StrictSimplicialGroupoids.{u} ⥤ SimplicialCat.{u, u} :=
  ObjectProperty.ι IsStrictGroupoid

/-- Original completion lands in strict simplicial groupoids by its proved degree groupoid laws.
-/
def strictCompletion : SimplicialCat.{u, u} ⥤ StrictSimplicialGroupoids.{u} :=
  ObjectProperty.lift IsStrictGroupoid completionFunctor completion_isStrictGroupoid

/-- The same original full completion and inclusion are actually adjoint. -/
def completionInclusionAdjunction : strictCompletion.{u} ⊣ inclusion.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv C D := (strictHomEquiv (strictCompletion.obj C) D).trans
        (completionHomEquiv C D.obj D.property)
      homEquiv_naturality_left_symm := by
        intro C C' D F G
        apply (strictHomEquiv _ _).injective
        change lift D.property (F ≫ G) = completionMap F ≫ lift D.property G
        symm
        apply lift_unique D.property
        rw [← Category.assoc, localization_naturality, Category.assoc, lift_spec]
      homEquiv_naturality_right := by
        intro C D D' F G
        exact Category.assoc (localization C) F.hom G.hom }

end

end DaggerOriginalSimplicialGroupoidCompletionAdjunction
