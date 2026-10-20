import OriginalSimplicialCategoryBarWeakFunctor
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Native degreewise decomposition of the entire original bar coproduct

Evaluation preserves the native coproduct. Mathlib's native cofan equivalence
therefore identifies every whole coproduct degree with the actual indexed family
of component degrees. The equivalence retains inclusions, all degree operators,
and the entire original enriched-functor map with its original endpoint image.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFunctor
universe u
namespace DaggerOriginalSimplicialCategoryBarCoproductDegrees
noncomputable section

/-- Evaluate the native simplicial coproduct cofan in its actual degree. -/
def coproductDegreeCofan {I : Type u} (X : I → SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Cofan (fun i ↦ (X i).obj n) :=
  Cofan.mk ((∐ X).obj n) (fun i ↦ (Sigma.ι X i).app n)

/-- The native evaluation functor preserves the actual coproduct universal property. -/
def coproductDegreeCofanIsColimit {I : Type u} (X : I → SSet.{u})
    (n : SimplexCategoryᵒᵖ) : IsColimit (coproductDegreeCofan X n) :=
  isColimitOfHasCoproductOfPreservesColimit
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n) X

/-- The native cofan equivalence retains the actual component index and entire simplex. -/
def coproductDegreeEquiv {I : Type u} (X : I → SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (Σ i, (X i).obj n) ≃ (∐ X).obj n :=
  CofanTypes.equivOfIsColimit ((Cofan.isColimit_cofanTypes_iff _).mpr
    ⟨coproductDegreeCofanIsColimit X n⟩)

/-- The native degree equivalence is exactly the actual coproduct inclusion. -/
theorem coproductDegreeEquiv_apply {I : Type u} (X : I → SSet.{u})
    (n : SimplexCategoryᵒᵖ) (i : I) (a : (X i).obj n) :
    coproductDegreeEquiv X n ⟨i, a⟩ = (Sigma.ι X i).app n a := rfl

/-- The native inverse of an actual inclusion retains its original index. -/
theorem coproductDegreeEquiv_symm_inclusion {I : Type u} (X : I → SSet.{u})
    (n : SimplexCategoryᵒᵖ) (i : I) (a : (X i).obj n) :
    (coproductDegreeEquiv X n).symm ((Sigma.ι X i).app n a) = ⟨i, a⟩ :=
  (coproductDegreeEquiv X n).symm_apply_apply ⟨i, a⟩

/-- All original degree operators retain the actual coproduct component. -/
theorem coproductDegreeEquiv_map {I : Type u} (X : I → SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (i : I) (a : (X i).obj n) :
    (∐ X).map f (coproductDegreeEquiv X n ⟨i, a⟩) =
      coproductDegreeEquiv X m ⟨i, (X i).map f a⟩ :=
  (congrFun ((Sigma.ι X i).naturality f) a).symm

/-- Descending native maps from the whole coproduct retains each entire component map. -/
theorem coproductDegreeEquiv_desc {I : Type u} {X : I → SSet.{u}} {Y : SSet.{u}}
    (f : ∀ i, X i ⟶ Y) (n : SimplexCategoryᵒᵖ) (i : I) (a : (X i).obj n) :
    (Sigma.desc f).app n (coproductDegreeEquiv X n ⟨i, a⟩) = (f i).app n a :=
  congrFun (NatTrans.congr_app (Sigma.ι_desc f i) n) a

/-- Every whole original bar degree is indexed by the unchanged original endpoints. -/
def barDegreeEquiv (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    (Σ y, (barComponent C y).obj n) ≃ (bar C).obj n :=
  coproductDegreeEquiv (barComponent C) n

/-- The original whole bar projection is exactly the original component projection. -/
theorem barDegreeEquiv_projection (C : SimplicialCat.{u, u})
    (n : SimplexCategoryᵒᵖ) (y : C.Obj) (a : (barComponent C y).obj n) :
    (barProjection C).app n (barDegreeEquiv C n ⟨y, a⟩) =
      (barComponentProjection C y).app n a :=
  coproductDegreeEquiv_desc (barComponentProjection C) n y a

/-- The full original enriched functor retains its actual endpoint image and whole map. -/
theorem barDegreeEquiv_functor {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) (y : C.Obj) (a : (barComponent C y).obj n) :
    (barMap F).app n (barDegreeEquiv C n ⟨y, a⟩) =
      barDegreeEquiv D n ⟨F.obj y, (barComponentMap F y).app n a⟩ :=
  congrFun (NatTrans.congr_app (barInclusion_map F y) n) a

end
end DaggerOriginalSimplicialCategoryBarCoproductDegrees
