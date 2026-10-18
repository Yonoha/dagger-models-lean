import OriginalSimplicialGroupoidCompletionDaggerFunctor
import OriginalStrictSimplicialGroupoidMappingKan

/-!
# Inverse dagger on the original strict dagger simplicial groupoid

Use inversion in the original degree category, without replacing its objects or Hom.
The inverse of the original dagger is a covariant, object-fixing, involutive simplicial
functor. Every original dagger functor between strict groupoids intertwines these maps.
-/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialDaggerDegreeLaws
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionDaggerFunctor
universe u

namespace DaggerOriginalStrictDaggerGroupoidSigma

noncomputable section

/-- Native inversion on the exact original strict groupoid mapping simplicial set. -/
def strictInversionHom (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (x y : C.Obj) :
    C.enriched.Hom x y ⟶ C.enriched.Hom y x where
  app n f := @inv (degreeObjects C n) (degreeCategory C n) x y f (hC n x y f)
  naturality n m i := by
    funext f
    letI := strictDegreeGroupoid C hC n
    letI := strictDegreeGroupoid C hC m
    exact ((degreeMap C i).map_inv f).symm

/-- Original inversion is an involution on the full original mapping simplicial set. -/
theorem strictInversionHom_involutive (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (x y : C.Obj) : strictInversionHom C hC x y ≫ strictInversionHom C hC y x = 𝟙 _ := by
  ext n f
  letI := strictDegreeGroupoid C hC n
  exact @IsIso.inv_inv (degreeObjects C n) (degreeCategory C n) x y f (hC n x y f)

/-- The original dagger commutes with native inversion on all original degree arrows. -/
theorem degreeDagger_inv (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat)
    (n : SimplexCategoryᵒᵖ) {x y : degreeObjects C.toSimplicialCat n} (f : x ⟶ y) :
    letI := strictDegreeGroupoid C.toSimplicialCat hC n
    degreeDagger C n (inv f) = inv (degreeDagger C n f) := by
  letI := strictDegreeGroupoid C.toSimplicialCat hC n
  apply IsIso.eq_inv_of_inv_hom_id
  rw [← degreeDagger_comp, IsIso.hom_inv_id, degreeDagger_id]

/-- The actual inverse of the actual original dagger, on its original mapping object. -/
def strictSigmaHom (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat)
    (x y : C.Obj) : C.toSimplicialCat.enriched.Hom x y ⟶ C.toSimplicialCat.enriched.Hom x y :=
  (@DaggerSimplicialStructure.dagger C.Obj C.toSimplicialCat.enriched
    C.daggerStructure x y) ≫ strictInversionHom C.toSimplicialCat hC y x

/-- In every degree the covariant involution is precisely inverse original dagger. -/
theorem strictSigmaHom_degree (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) (n : SimplexCategoryᵒᵖ)
    (f : (C.toSimplicialCat.enriched.Hom x y).obj n) :
    letI := strictDegreeGroupoid C.toSimplicialCat hC n
    (strictSigmaHom C hC x y).app n f = inv (degreeDagger C n f) := rfl

/-- The inverse-dagger map squares to the identity on every original simplex. -/
theorem strictSigmaHom_involutive (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    strictSigmaHom C hC x y ≫ strictSigmaHom C hC x y = 𝟙 _ := by
  ext n f
  letI := strictDegreeGroupoid C.toSimplicialCat hC n
  change inv (degreeDagger C n (inv (degreeDagger C n f))) = f
  rw [degreeDagger_inv C hC n, degreeDagger_involutive, IsIso.inv_inv]

/-- Inverse dagger is a genuine enriched functor fixing each original object. -/
def strictSigmaFunctor (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) : C.toSimplicialCat ⟶ C.toSimplicialCat where
  obj x := x
  map := strictSigmaHom C hC
  map_id x := by
    ext n p
    letI := strictDegreeGroupoid C.toSimplicialCat hC n
    change inv (degreeDagger C n
      (@CategoryStruct.id (degreeObjects C.toSimplicialCat n)
        (degreeCategory C.toSimplicialCat n).toCategoryStruct x)) =
      @CategoryStruct.id (degreeObjects C.toSimplicialCat n)
        (degreeCategory C.toSimplicialCat n).toCategoryStruct x
    rw [degreeDagger_id, IsIso.inv_id]
  map_comp x y z := by
    ext n ⟨f, g⟩
    letI := strictDegreeGroupoid C.toSimplicialCat hC n
    change inv (degreeDagger C n (f ≫ g)) =
      inv (degreeDagger C n f) ≫ inv (degreeDagger C n g)
    rw [degreeDagger_comp, IsIso.inv_comp]

/-- The full original object-fixing functor is involutive, including all Hom maps. -/
theorem strictSigmaFunctor_involutive (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    strictSigmaFunctor C hC ≫ strictSigmaFunctor C hC = 𝟙 C.toSimplicialCat := by
  apply EnrichedFunctor.ext SSet.{u}
    (F := strictSigmaFunctor C hC ≫ strictSigmaFunctor C hC)
    (G := 𝟙 C.toSimplicialCat) (fun _ ↦ rfl)
  intro x y
  simpa only [eqToHom_refl, Category.comp_id] using strictSigmaHom_involutive C hC x y

/-- Every original dagger functor commutes with inverse dagger on the unchanged Hom. -/
theorem strictSigmaHom_functor {C D : DaggerSimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C.toSimplicialCat) (hD : IsStrictGroupoid D.toSimplicialCat)
    (F : C ⟶ D) (x y : C.Obj) :
    strictSigmaHom C hC x y ≫ F.map x y =
      F.map x y ≫ strictSigmaHom D hD (F.obj x) (F.obj y) := by
  ext n f
  letI := strictDegreeGroupoid C.toSimplicialCat hC n
  letI := strictDegreeGroupoid D.toSimplicialCat hD n
  change (degreeFunctor F.toEnrichedFunctor n).map (inv (degreeDagger C n f)) =
    inv (degreeDagger D n ((degreeFunctor F.toEnrichedFunctor n).map f))
  rw [CategoryTheory.Functor.map_inv, degreeDagger_functor]

end

end DaggerOriginalStrictDaggerGroupoidSigma
