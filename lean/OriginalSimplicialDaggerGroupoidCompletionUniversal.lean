import OriginalSimplicialGroupoidCompletionDaggerFunctor

/-!
# The dagger universal property of the actual original completion

For an original dagger simplicial functor to a strict dagger simplicial groupoid,
the previously proved full simplicial extension preserves dagger. Native uniqueness
compares the full degreewise covariant involutions. The extension and its uniqueness
keep the original object and Hom maps and do not assume a mapping-space comparison.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialDaggerDegreeLaws
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionAdjunction
open DaggerOriginalSimplicialGroupoidCompletionSigma
open DaggerOriginalSimplicialGroupoidCompletionDagger
open DaggerOriginalSimplicialGroupoidCompletionDaggerFunctor

universe u

namespace DaggerOriginalSimplicialDaggerGroupoidCompletionUniversal

noncomputable section

/-- In a strict original dagger groupoid, inverse dagger is a covariant degree functor. -/
def strictSigmaDegree (D : DaggerSimplicialCat.{u, u})
    (hD : IsStrictGroupoid D.toSimplicialCat) (n : SimplexCategoryᵒᵖ) :
    degreeObjects D.toSimplicialCat n ⥤ degreeObjects D.toSimplicialCat n := by
  letI := strictDegreeGroupoid D.toSimplicialCat hD n
  exact
    { obj := fun x ↦ x
      map := fun f ↦ inv (degreeDagger D n f)
      map_id := fun x ↦ by simp only [degreeDagger_id, IsIso.inv_id]
      map_comp := fun f g ↦ by simp only [degreeDagger_comp, IsIso.inv_comp] }

/-- The full original extension intertwines the full completed and original involutions. -/
theorem liftedDegreeFunctor_sigma {C D : DaggerSimplicialCat.{u, u}}
    (hD : IsStrictGroupoid D.toSimplicialCat) (F : C ⟶ D) (n : SimplexCategoryᵒᵖ) :
    completedSigmaDegree C n ⋙ liftedDegreeFunctor hD F.toEnrichedFunctor n =
      liftedDegreeFunctor hD F.toEnrichedFunctor n ⋙ strictSigmaDegree D hD n := by
  letI := strictDegreeGroupoid D.toSimplicialCat hD n
  have hL : FreeGroupoid.of (degreeObjects C.toSimplicialCat n) ⋙
      (completedSigmaDegree C n ⋙ liftedDegreeFunctor hD F.toEnrichedFunctor n) =
        degreeFunctor F.toEnrichedFunctor n ⋙ strictSigmaDegree D hD n := by
    refine CategoryTheory.Functor.hext
      (F := FreeGroupoid.of _ ⋙
        (completedSigmaDegree C n ⋙ liftedDegreeFunctor hD F.toEnrichedFunctor n))
      (G := degreeFunctor F.toEnrichedFunctor n ⋙ strictSigmaDegree D hD n)
      (fun _ ↦ rfl) ?_
    intro x y f
    apply heq_of_eq
    change (FreeGroupoid.lift (degreeFunctor F.toEnrichedFunctor n)).map
        ((completedSigmaDegree C n).map ((FreeGroupoid.of _).map f)) =
      inv (degreeDagger D n ((degreeFunctor F.toEnrichedFunctor n).map f))
    simp only [completedSigmaDegree_generator, CategoryTheory.Functor.map_inv,
      FreeGroupoid.lift_map_homMk, degreeDagger_functor]
  have hR : FreeGroupoid.of (degreeObjects C.toSimplicialCat n) ⋙
      (liftedDegreeFunctor hD F.toEnrichedFunctor n ⋙ strictSigmaDegree D hD n) =
        degreeFunctor F.toEnrichedFunctor n ⋙ strictSigmaDegree D hD n := by
    rw [← CategoryTheory.Functor.assoc]
    change (FreeGroupoid.of _ ⋙ FreeGroupoid.lift (degreeFunctor F.toEnrichedFunctor n)) ⋙
      strictSigmaDegree D hD n = _
    rw [FreeGroupoid.lift_spec]
  exact (FreeGroupoid.lift_unique
    (degreeFunctor F.toEnrichedFunctor n ⋙ strictSigmaDegree D hD n) _ hL).trans
    (FreeGroupoid.lift_unique
      (degreeFunctor F.toEnrichedFunctor n ⋙ strictSigmaDegree D hD n) _ hR).symm

/-- The unique original simplicial extension is an actual dagger simplicial functor. -/
def daggerLift {C D : DaggerSimplicialCat.{u, u}}
    (hD : IsStrictGroupoid D.toSimplicialCat) (F : C ⟶ D) : daggerCompletion C ⟶ D where
  __ := lift hD F.toEnrichedFunctor
  map_dagger x y := by
    ext n f
    letI := strictDegreeGroupoid D.toSimplicialCat hD n
    change degreeDagger D n ((liftedDegreeFunctor hD F.toEnrichedFunctor n).map f) =
      (liftedDegreeFunctor hD F.toEnrichedFunctor n).map
        (inv ((completedSigmaDegree C n).map f))
    have h := CategoryTheory.Functor.congr_hom (liftedDegreeFunctor_sigma hD F n) f
    have hh : (liftedDegreeFunctor hD F.toEnrichedFunctor n).map
        ((completedSigmaDegree C n).map f) =
      inv (degreeDagger D n ((liftedDegreeFunctor hD F.toEnrichedFunctor n).map f)) := by
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
        CategoryTheory.Functor.comp_map] using h
    calc
      degreeDagger D n ((liftedDegreeFunctor hD F.toEnrichedFunctor n).map f) =
          inv (inv (degreeDagger D n
            ((liftedDegreeFunctor hD F.toEnrichedFunctor n).map f))) := IsIso.inv_inv.symm
      _ = inv ((liftedDegreeFunctor hD F.toEnrichedFunctor n).map
          ((completedSigmaDegree C n).map f)) := congrArg (fun g ↦ inv g) hh.symm
      _ = (liftedDegreeFunctor hD F.toEnrichedFunctor n).map
          (inv ((completedSigmaDegree C n).map f)) :=
        ((liftedDegreeFunctor hD F.toEnrichedFunctor n).map_inv _).symm

/-- The actual dagger extension factors the full original dagger functor. -/
theorem daggerLift_spec {C D : DaggerSimplicialCat.{u, u}}
    (hD : IsStrictGroupoid D.toSimplicialCat) (F : C ⟶ D) :
    daggerLocalization C ≫ daggerLift hD F = F := by
  apply DaggerSimplicialCat.Hom.ext
  exact lift_spec hD F.toEnrichedFunctor

/-- The actual dagger extension is unique among full original dagger simplicial functors. -/
theorem daggerLift_unique {C D : DaggerSimplicialCat.{u, u}}
    (hD : IsStrictGroupoid D.toSimplicialCat) (F : C ⟶ D)
    (Φ : daggerCompletion C ⟶ D) (hΦ : daggerLocalization C ≫ Φ = F) :
    Φ = daggerLift hD F := by
  apply DaggerSimplicialCat.Hom.ext
  apply lift_unique hD F.toEnrichedFunctor Φ.toEnrichedFunctor
  exact congrArg DaggerSimplicialCat.Hom.toEnrichedFunctor hΦ

/-- The full dagger completion-inclusion Hom equivalence uses the actual original functors. -/
def daggerCompletionHomEquiv (C D : DaggerSimplicialCat.{u, u})
    (hD : IsStrictGroupoid D.toSimplicialCat) : (daggerCompletion C ⟶ D) ≃ (C ⟶ D) where
  toFun Φ := daggerLocalization C ≫ Φ
  invFun := daggerLift hD
  left_inv Φ := (daggerLift_unique hD (daggerLocalization C ≫ Φ) Φ rfl).symm
  right_inv F := daggerLift_spec hD F

end

end DaggerOriginalSimplicialDaggerGroupoidCompletionUniversal
