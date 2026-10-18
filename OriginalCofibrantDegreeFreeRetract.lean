import OriginalDegreeCofreeCounit
import OriginalAmbientDaggerForgetCofibrancy
import Mathlib.CategoryTheory.PathCategory.Basic

/-! Cofibrancy in the original fixed-object lifting class gives actual free degree retracts. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Opposite DaggerModels
open DaggerOriginalDegreeCofreeEnrichment DaggerOriginalDegreeCofreeUnit
open DaggerOriginalDegreeCofreeMaps DaggerOriginalDegreeCofreeCounit
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalFixedObjectSimplicialCategories
open DaggerOriginalSimplicialGroupoidCompletionFunctor
open DaggerOriginalAmbientDaggerForgetCofibrancy
open scoped SSet.modelCategoryQuillen DaggerOriginalAmbientDaggerForgetCofibrancy
universe u
namespace DaggerOriginalCofibrantDegreeFreeRetract
noncomputable section

/-- Restrict a whole original functor whose object function is the original identity. -/
def fixedHomOfIdentity {O : Type u} {C D : FixedSimplicialCategory O}
    (F : original O C ⟶ original O D) (hF : F.obj = id) : C ⟶ D := by
  rcases F with ⟨obj, map, hi, hc⟩
  change obj = id at hF
  subst obj
  exact ⟨map, hi, hc⟩

def degreeCofree {O : Type u} (C : FixedSimplicialCategory O) (n : SimplexCategoryᵒᵖ) :
    FixedSimplicialCategory O :=
  ⟨(cofreeCategory n (degreeObjects (original O C) n)).enriched⟩

def freeDegreeCofree {O : Type u} (C : FixedSimplicialCategory O) (n : SimplexCategoryᵒᵖ) :
    FixedSimplicialCategory O :=
  ⟨(cofreeCategory n (Paths (degreeObjects (original O C) n))).enriched⟩

def fixedDegreeUnit {O : Type u} (C : FixedSimplicialCategory O) (n : SimplexCategoryᵒᵖ) :
    C ⟶ degreeCofree C n := fixedHomOfIdentity (degreeUnit (original O C) n) rfl

def augmentation {O : Type u} (C : FixedSimplicialCategory O) (n : SimplexCategoryᵒᵖ) :
    freeDegreeCofree C n ⟶ degreeCofree C n :=
  fixedHomOfIdentity (cofreeMap n (D := Paths (degreeObjects (original O C) n))
    (E := degreeObjects (original O C) n) (pathComposition _)) rfl

theorem augmentation_trivial {O : Type u} (C : FixedSimplicialCategory O)
    (n : SimplexCategoryᵒᵖ) : ordinaryTrivialFibrations O (augmentation C n) := by
  intro x y
  change trivialFibrations SSet.{u}
    ((cofreeMap n (D := Paths (degreeObjects (original O C) n))
      (E := degreeObjects (original O C) n) (pathComposition _)).map x y)
  apply cofreeMap_hom_trivialFibration
  intro a b f
  exact ⟨f.toPath, composePath_toPath f⟩

def liftSquare {O : Type u} (C : FixedSimplicialCategory O) (n : SimplexCategoryᵒᵖ) :
    CommSq (initial.to (freeDegreeCofree C n)) (initial.to C)
      (augmentation C n) (fixedDegreeUnit C n) :=
  ⟨initialIsInitial.hom_ext _ _⟩

theorem liftSquare_hasLift {O : Type u} (C : FixedSimplicialCategory O) [IsCofibrant C]
    (n : SimplexCategoryᵒᵖ) : (liftSquare C n).HasLift := by
  have hi : Cofibration (initial.to C) := (isCofibrant_iff C).mp inferInstance
  have h : ordinaryCofibrations O (initial.to C) := (cofibration_iff _).mp hi
  have : HasLiftingProperty (initial.to C) (augmentation C n) :=
    h _ (augmentation_trivial C n)
  infer_instance

def degreeLift {O : Type u} (C : FixedSimplicialCategory O) [IsCofibrant C]
    (n : SimplexCategoryᵒᵖ) : C ⟶ freeDegreeCofree C n := by
  have := liftSquare_hasLift C n
  exact (liftSquare C n).lift

theorem degreeLift_fac {O : Type u} (C : FixedSimplicialCategory O) [IsCofibrant C]
    (n : SimplexCategoryᵒᵖ) : degreeLift C n ≫ augmentation C n = fixedDegreeUnit C n := by
  have := liftSquare_hasLift C n
  change (liftSquare C n).lift ≫ augmentation C n = fixedDegreeUnit C n
  exact (liftSquare C n).fac_right

def degreeSection {O : Type u} (C : FixedSimplicialCategory O) [IsCofibrant C]
    (n : SimplexCategoryᵒᵖ) :
    degreeObjects (original O C) n ⥤ Paths (degreeObjects (original O C) n) :=
  degreeFunctor (originalHom (degreeLift C n)) n ⋙
    degreeCounit n (Paths (degreeObjects (original O C) n))

theorem degreeSection_obj {O : Type u} (C : FixedSimplicialCategory O) [IsCofibrant C]
    (n : SimplexCategoryᵒᵖ) (x : O) : (degreeSection C n).obj x = x := rfl

theorem degreeSection_retract {O : Type u} (C : FixedSimplicialCategory O) [IsCofibrant C]
    (n : SimplexCategoryᵒᵖ) :
    degreeSection C n ⋙ pathComposition (degreeObjects (original O C) n) =
      𝟭 (degreeObjects (original O C) n) := by
  have hn : originalHom (degreeLift C n) ≫
      cofreeMap n (D := Paths (degreeObjects (original O C) n))
        (E := degreeObjects (original O C) n) (pathComposition _) =
      degreeUnit (original O C) n := by
    change originalHom (degreeLift C n ≫ augmentation C n) = originalHom (fixedDegreeUnit C n)
    exact congrArg originalHom (degreeLift_fac C n)
  change (degreeFunctor (originalHom (degreeLift C n)) n ⋙
    degreeCounit n (Paths (degreeObjects (original O C) n))) ⋙ _ = _
  rw [Functor.assoc, ← degreeCounit_naturality, ← Functor.assoc,
    ← degreeFunctor_comp, hn, degreeUnit_counit]

end
end DaggerOriginalCofibrantDegreeFreeRetract
