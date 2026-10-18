import OriginalSimplicialDaggerDegreeLaws

/-!
# Covariant involution on the actual degreewise groupoid completion

Extend the inverse of the original dagger using Mathlib's free-groupoid universal
property. The extension fixes every original object, commutes with every original
simplicial operator, and squares to the identity on the full completed Hom, not just
on the original generating arrows.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialDaggerDegreeLaws
open DaggerOriginalSimplicialGroupoidCompletion

universe u

namespace DaggerOriginalSimplicialGroupoidCompletionSigma

noncomputable section

/-- The inverse-dagger seed commutes with every original simplicial operator. -/
theorem degreeSigmaSeed_naturality (C : DaggerSimplicialCat.{u, u})
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    degreeMap C.toSimplicialCat i ⋙ degreeSigmaSeed C m =
      degreeSigmaSeed C n ⋙ FreeGroupoid.map (degreeMap C.toSimplicialCat i) := by
  refine CategoryTheory.Functor.hext
    (F := degreeMap C.toSimplicialCat i ⋙ degreeSigmaSeed C m)
    (G := degreeSigmaSeed C n ⋙ FreeGroupoid.map (degreeMap C.toSimplicialCat i))
    (fun _ ↦ rfl) ?_
  intro x y f
  apply heq_of_eq
  change inv ((FreeGroupoid.of _).map
      (degreeDagger C m ((degreeMap C.toSimplicialCat i).map f))) =
    (FreeGroupoid.map (degreeMap C.toSimplicialCat i)).map
      (inv ((FreeGroupoid.of _).map (degreeDagger C n f)))
  rw [CategoryTheory.Functor.map_inv]
  change inv ((FreeGroupoid.of _).map
      (degreeDagger C m ((degreeMap C.toSimplicialCat i).map f))) =
    inv ((FreeGroupoid.of _).map
      ((degreeMap C.toSimplicialCat i).map (degreeDagger C n f)))
  rw [degreeDagger_naturality]

/-- Extend the covariant inverse dagger over the same native completed degree groupoid. -/
def completedSigmaDegree (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    FreeGroupoid (degreeObjects C.toSimplicialCat n) ⥤
      FreeGroupoid (degreeObjects C.toSimplicialCat n) :=
  FreeGroupoid.lift (degreeSigmaSeed C n)

/-- The extended involution fixes the actual native completed objects. -/
theorem completedSigmaDegree_obj (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (x : FreeGroupoid (degreeObjects C.toSimplicialCat n)) :
    (completedSigmaDegree C n).obj x = x := rfl

/-- On every original arrow the extension is exactly inverse localized dagger. -/
theorem completedSigmaDegree_generator (C : DaggerSimplicialCat.{u, u})
    (n : SimplexCategoryᵒᵖ) {x y : degreeObjects C.toSimplicialCat n} (f : x ⟶ y) :
    (completedSigmaDegree C n).map ((FreeGroupoid.of _).map f) =
      inv ((FreeGroupoid.of _).map (degreeDagger C n f)) :=
  FreeGroupoid.lift_map_homMk (degreeSigmaSeed C n) f

/-- The full degree extension commutes with every original simplicial operator. -/
theorem completedSigmaDegree_naturality (C : DaggerSimplicialCat.{u, u})
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    FreeGroupoid.map (degreeMap C.toSimplicialCat i) ⋙ completedSigmaDegree C m =
      completedSigmaDegree C n ⋙ FreeGroupoid.map (degreeMap C.toSimplicialCat i) := by
  change FreeGroupoid.map (degreeMap C.toSimplicialCat i) ⋙
      FreeGroupoid.lift (degreeSigmaSeed C m) =
    FreeGroupoid.lift (degreeSigmaSeed C n) ⋙ FreeGroupoid.map (degreeMap C.toSimplicialCat i)
  rw [FreeGroupoid.map_comp_lift, ← FreeGroupoid.lift_comp, degreeSigmaSeed_naturality]

/-- Native uniqueness proves involutivity on all completed arrows. -/
theorem completedSigmaDegree_involutive (C : DaggerSimplicialCat.{u, u})
    (n : SimplexCategoryᵒᵖ) :
    completedSigmaDegree C n ⋙ completedSigmaDegree C n =
      𝟭 (FreeGroupoid (degreeObjects C.toSimplicialCat n)) := by
  have h : FreeGroupoid.of (degreeObjects C.toSimplicialCat n) ⋙
      (completedSigmaDegree C n ⋙ completedSigmaDegree C n) =
        FreeGroupoid.of (degreeObjects C.toSimplicialCat n) := by
    refine CategoryTheory.Functor.hext
      (F := FreeGroupoid.of _ ⋙ (completedSigmaDegree C n ⋙ completedSigmaDegree C n))
      (G := FreeGroupoid.of _) (fun _ ↦ rfl) ?_
    intro x y f
    apply heq_of_eq
    change (completedSigmaDegree C n).map
        ((completedSigmaDegree C n).map ((FreeGroupoid.of _).map f)) =
      (FreeGroupoid.of _).map f
    simp only [completedSigmaDegree_generator, CategoryTheory.Functor.map_inv,
      degreeDagger_involutive, IsIso.inv_inv]
  exact (FreeGroupoid.lift_unique (FreeGroupoid.of _) _ h).trans
    (FreeGroupoid.lift_unique (FreeGroupoid.of _) (𝟭 _) (by rfl)).symm

/-- The degreewise covariant involution is a map of the actual completed simplicial Hom. -/
def completedSigmaHom (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    completedHom C.toSimplicialCat x y ⟶ completedHom C.toSimplicialCat x y where
  app n f := (completedSigmaDegree C n).map f
  naturality n m i := by
    funext f
    have h := CategoryTheory.Functor.congr_hom (completedSigmaDegree_naturality C i) f
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
      CategoryTheory.Functor.comp_map] using h

/-- The involution squares to the identity on the entire completed simplicial Hom. -/
theorem completedSigmaHom_involutive (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    completedSigmaHom C x y ≫ completedSigmaHom C x y = 𝟙 _ := by
  ext n f
  have h := CategoryTheory.Functor.congr_hom (completedSigmaDegree_involutive C n) f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] using h

end

end DaggerOriginalSimplicialGroupoidCompletionSigma
