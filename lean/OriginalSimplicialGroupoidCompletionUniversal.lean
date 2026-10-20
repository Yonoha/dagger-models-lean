import OriginalSimplicialGroupoidCompletionFunctor

/-!
# The original degreewise completion is universal among strict simplicial groupoids

Keep the original degree category structures. Completed degrees are groupoids by native
pointwise inversion. For any original target with groupoid degree categories, the native
free-groupoid lift of each original degree functor is simplicially natural, giving the
actual simplicial extension. Its factorization and uniqueness retain the full original
object and Hom maps, without any Kan or weak-equivalence premise.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionFunctor

universe u

namespace DaggerOriginalSimplicialGroupoidCompletionUniversal

noncomputable section

/-- The original completed degree category is a groupoid with the same pointwise category laws.
-/
instance completedDegreeGroupoid (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    Groupoid (degreeObjects (completion C) n) where
  __ := degreeCategory (completion C) n
  inv {x y} f := @Groupoid.inv (FreeGroupoid (degreeObjects C n)) inferInstance
    (completedObject C n x) (completedObject C n y) f
  inv_comp {x y} f := @Groupoid.inv_comp (FreeGroupoid (degreeObjects C n)) inferInstance
    (completedObject C n x) (completedObject C n y) f
  comp_inv {x y} f := @Groupoid.comp_inv (FreeGroupoid (degreeObjects C n)) inferInstance
    (completedObject C n x) (completedObject C n y) f

/-- The strict groupoid property concerns exactly the original ordinary degree categories. -/
def IsStrictGroupoid (C : SimplicialCat.{u, u}) : Prop :=
  ∀ (n : SimplexCategoryᵒᵖ) (x y : degreeObjects C n) (f : x ⟶ y), IsIso f

/-- The actual original degreewise completion is a strict simplicial groupoid. -/
theorem completion_isStrictGroupoid (C : SimplicialCat.{u, u}) : IsStrictGroupoid (completion C) :=
  fun _ _ _ _ ↦ inferInstance

/-- The same target degree category has its groupoid structure from its actual invertible maps.
-/
def strictDegreeGroupoid (D : SimplicialCat.{u, u}) (hD : IsStrictGroupoid D)
    (n : SimplexCategoryᵒᵖ) : Groupoid (degreeObjects D n) :=
  Groupoid.ofIsIso (fun {x y} f ↦ hD n x y f)

/-- Lift precisely the original degree functor through the native groupoid localization. -/
def liftedDegreeFunctor {C D : SimplicialCat.{u, u}} (hD : IsStrictGroupoid D)
    (F : C ⟶ D) (n : SimplexCategoryᵒᵖ) :
    FreeGroupoid (degreeObjects C n) ⥤ degreeObjects D n := by
  letI := strictDegreeGroupoid D hD n
  exact FreeGroupoid.lift (degreeFunctor F n)

/-- The lifted original degree functors commute with every original simplicial operator. -/
theorem liftedDegreeFunctor_naturality {C D : SimplicialCat.{u, u}} (hD : IsStrictGroupoid D)
    (F : C ⟶ D) {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    FreeGroupoid.map (degreeMap C i) ⋙ liftedDegreeFunctor hD F m =
      liftedDegreeFunctor hD F n ⋙ degreeMap D i := by
  letI := strictDegreeGroupoid D hD n
  letI := strictDegreeGroupoid D hD m
  change FreeGroupoid.map (degreeMap C i) ⋙ FreeGroupoid.lift (degreeFunctor F m) =
    FreeGroupoid.lift (degreeFunctor F n) ⋙ degreeMap D i
  rw [FreeGroupoid.map_comp_lift, ← FreeGroupoid.lift_comp, degreeFunctor_naturality]

/-- The same original Hom functor extends degreewise over its actual completed Hom. -/
def liftedHomMap {C D : SimplicialCat.{u, u}} (hD : IsStrictGroupoid D) (F : C ⟶ D)
    (x y : C.Obj) : completedHom C x y ⟶ D.enriched.Hom (F.obj x) (F.obj y) where
  app n f := (liftedDegreeFunctor hD F n).map f
  naturality n m i := by
    funext f
    have h := CategoryTheory.Functor.congr_hom (liftedDegreeFunctor_naturality hD F i) f
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
      CategoryTheory.Functor.comp_map] using h

/-- The actual original simplicial functor extends to its degreewise completion. -/
def lift {C D : SimplicialCat.{u, u}} (hD : IsStrictGroupoid D) (F : C ⟶ D) :
    completion C ⟶ D where
  obj := F.obj
  map := liftedHomMap hD F
  map_id x := by
    ext n p
    exact (liftedDegreeFunctor hD F n).map_id (completedObject C n x)
  map_comp x y z := by
    ext n ⟨f, g⟩
    exact (liftedDegreeFunctor hD F n).map_comp f g

/-- The original localization followed by its extension is exactly the original functor. -/
theorem lift_spec {C D : SimplicialCat.{u, u}} (hD : IsStrictGroupoid D) (F : C ⟶ D) :
    localization C ≫ lift hD F = F := by
  refine EnrichedFunctor.ext SSet.{u} (F := localization C ≫ lift hD F) (G := F)
    (fun _ ↦ rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  ext n f
  letI := strictDegreeGroupoid D hD n
  exact FreeGroupoid.lift_map_homMk (degreeFunctor F n) f

end

end DaggerOriginalSimplicialGroupoidCompletionUniversal
