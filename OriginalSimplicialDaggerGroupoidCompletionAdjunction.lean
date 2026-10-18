import OriginalSimplicialDaggerGroupoidCompletionUniversal

/-!
# The actual dagger completion-inclusion adjunction

Bundle the proved dagger extension equivalence and its naturality into an ordinary
adjunction on the original dagger simplicial categories and their full subcategory
of strict dagger simplicial groupoids. This does not assert an enriched or Quillen
adjunction or any local weak equivalence of the original localization.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionDagger
open DaggerOriginalSimplicialGroupoidCompletionDaggerFunctor
open DaggerOriginalSimplicialDaggerGroupoidCompletionUniversal

universe u

namespace DaggerOriginalSimplicialDaggerGroupoidCompletionAdjunction

noncomputable section

/-- Strictness is exactly invertibility in the original underlying degree categories. -/
def IsStrictDaggerGroupoid (C : DaggerSimplicialCat.{u, u}) : Prop :=
  IsStrictGroupoid C.toSimplicialCat

/-- The actual original dagger completion is a strict dagger simplicial groupoid. -/
theorem daggerCompletion_isStrict (C : DaggerSimplicialCat.{u, u}) :
    IsStrictDaggerGroupoid (daggerCompletion C) := completion_isStrictGroupoid _

/-- The original strict dagger simplicial groupoids form their actual full subcategory. -/
abbrev StrictDaggerSimplicialGroupoids :=
  ObjectProperty.FullSubcategory IsStrictDaggerGroupoid.{u}

/-- The native full-subcategory arrows retain the exact full original dagger functors. -/
def strictDaggerHomEquiv (C D : StrictDaggerSimplicialGroupoids.{u}) :
    (C ⟶ D) ≃ (C.obj ⟶ D.obj) where
  toFun F := F.hom
  invFun := ObjectProperty.homMk
  left_inv F := by cases F; rfl
  right_inv _ := rfl

/-- Include the original strict dagger simplicial groupoids with their full dagger functors. -/
def daggerInclusion : StrictDaggerSimplicialGroupoids.{u} ⥤ DaggerSimplicialCat.{u, u} :=
  ObjectProperty.ι IsStrictDaggerGroupoid

/-- The actual original dagger completion lands in strict dagger simplicial groupoids. -/
def strictDaggerCompletion : DaggerSimplicialCat.{u, u} ⥤ StrictDaggerSimplicialGroupoids.{u} :=
  ObjectProperty.lift IsStrictDaggerGroupoid daggerCompletionFunctor daggerCompletion_isStrict

/-- The original full dagger completion and inclusion are actually adjoint. -/
def daggerCompletionInclusionAdjunction : strictDaggerCompletion.{u} ⊣ daggerInclusion.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv C D := (strictDaggerHomEquiv (strictDaggerCompletion.obj C) D).trans
        (daggerCompletionHomEquiv C D.obj D.property)
      homEquiv_naturality_left_symm := by
        intro C C' D F G
        apply (strictDaggerHomEquiv _ _).injective
        change daggerLift D.property (F ≫ G) = daggerCompletionMap F ≫ daggerLift D.property G
        symm
        apply daggerLift_unique D.property
        rw [← Category.assoc, daggerLocalization_naturality, Category.assoc, daggerLift_spec]
      homEquiv_naturality_right := by
        intro C D D' F G
        exact Category.assoc (daggerLocalization C) F.hom G.hom }

end

end DaggerOriginalSimplicialDaggerGroupoidCompletionAdjunction
