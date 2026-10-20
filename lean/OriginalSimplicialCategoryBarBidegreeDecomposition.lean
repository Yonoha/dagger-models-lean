import NativeOverChainDecomposition
import OriginalSimplicialCategoryWholeBarFibreVertexHomotopy

/-!
# Every original bar bidegree retains its base chain and last original Hom arrow

Apply the native over-chain decomposition to precisely the original degree
category. Both horizontal nerve operators and vertical original simplicial
operators act on the full lifts by their exact original composition and maps.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeOverChainDecomposition
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFunctor
universe u
namespace DaggerOriginalSimplicialCategoryBarBidegreeDecomposition
noncomputable section

/-- Every original bar bidegree is the original chain with its last original Hom simplex. -/
def barBidegreeEquiv (C : SimplicialCat.{u, u}) (z : C.Obj)
    (v : SimplexCategoryᵒᵖ) (k : ℕ) :
    (nerve (overObjects C z v)).obj (op ⦋k⦌) ≃
      Σ A : Fin (k + 1) ⥤ degreeObjects C v,
        (C.enriched.Hom (A.obj (Fin.last k)) z).obj v :=
  overChainEquiv (degreeObjects C v) z k

/-- Lift the exact original base chain using its exact last original Hom simplex. -/
def barBidegreeLift (C : SimplicialCat.{u, u}) (z : C.Obj)
    (v : SimplexCategoryᵒᵖ) (k : ℕ) (A : Fin (k + 1) ⥤ degreeObjects C v)
    (f : (C.enriched.Hom (A.obj (Fin.last k)) z).obj v) :
    (nerve (overObjects C z v)).obj (op ⦋k⦌) :=
  chainLift A f

/-- The inverse decomposition is the full native original lift. -/
theorem barBidegreeEquiv_symm_apply (C : SimplicialCat.{u, u}) (z : C.Obj)
    (v : SimplexCategoryᵒᵖ) (k : ℕ) (A : Fin (k + 1) ⥤ degreeObjects C v)
    (f : (C.enriched.Hom (A.obj (Fin.last k)) z).obj v) :
    (barBidegreeEquiv C z v k).symm ⟨A, f⟩ = barBidegreeLift C z v k A f := rfl

/-- Forgetting the full original lift retains its entire original base chain. -/
theorem barBidegreeLift_projection (C : SimplicialCat.{u, u}) (z : C.Obj)
    (v : SimplexCategoryᵒᵖ) (k : ℕ) (A : Fin (k + 1) ⥤ degreeObjects C v)
    (f : (C.enriched.Hom (A.obj (Fin.last k)) z).obj v) :
    (nerveMap (Over.forget (T := degreeObjects C v) z)).app (op ⦋k⦌)
      (barBidegreeLift C z v k A f) = A := chainLift_forget A f

/-- Horizontal original nerve operators precompose the final arrow along the original chain. -/
theorem barBidegreeLift_horizontal (C : SimplicialCat.{u, u}) (z : C.Obj)
    (v : SimplexCategoryᵒᵖ) {k l : ℕ} (A : Fin (k + 1) ⥤ degreeObjects C v)
    (f : (C.enriched.Hom (A.obj (Fin.last k)) z).obj v)
    (K : Fin (l + 1) ⥤ Fin (k + 1)) :
    K ⋙ barBidegreeLift C z v k A f = barBidegreeLift C z v l (K ⋙ A)
      (@CategoryStruct.comp (degreeObjects C v) (degreeCategory C v).toCategoryStruct
        (A.obj (K.obj (Fin.last l))) (A.obj (Fin.last k)) z
        (A.map (homOfLE (Fin.le_last (K.obj (Fin.last l))))) f) :=
  chainLift_precompose A f K

/-- Vertical original simplicial operators act by the exact original Hom map. -/
theorem barBidegreeLift_vertical (C : SimplicialCat.{u, u}) (z : C.Obj)
    {v w : SimplexCategoryᵒᵖ} (i : v ⟶ w) (k : ℕ)
    (A : Fin (k + 1) ⥤ degreeObjects C v)
    (f : (C.enriched.Hom (A.obj (Fin.last k)) z).obj v) :
    barBidegreeLift C z v k A f ⋙ overDegreeMap C z i =
      barBidegreeLift C z w k (A ⋙ degreeMap C i)
        ((C.enriched.Hom (A.obj (Fin.last k)) z).map i f) :=
  chainLift_post A f (degreeMap C i)

/-- The actual original diagonal bar degree retains the full chain and its original last arrow. -/
def barComponentDegreeChainEquiv (C : SimplicialCat.{u, u}) (z : C.Obj)
    (v : SimplexCategoryᵒᵖ) :
    (barComponent C z).obj v ≃ Σ A : Fin (v.unop.len + 1) ⥤ degreeObjects C v,
      (C.enriched.Hom (A.obj (Fin.last v.unop.len)) z).obj v :=
  barBidegreeEquiv C z v v.unop.len

/-- The original diagonal projection is exactly the base-chain coordinate of the decomposition. -/
theorem barComponentDegreeChainEquiv_projection (C : SimplicialCat.{u, u}) (z : C.Obj)
    (v : SimplexCategoryᵒᵖ) (B : (barComponent C z).obj v) :
    (barComponentDegreeChainEquiv C z v B).1 = (barComponentProjection C z).app v B := rfl

/-- Every actual diagonal operator restricts the base chain and precomposes the final arrow. -/
theorem barComponentDegreeLift_map (C : SimplicialCat.{u, u}) (z : C.Obj)
    {v w : SimplexCategoryᵒᵖ} (i : v ⟶ w)
    (A : Fin (v.unop.len + 1) ⥤ degreeObjects C v)
    (f : (C.enriched.Hom (A.obj (Fin.last v.unop.len)) z).obj v) :
    (barComponent C z).map i (barBidegreeLift C z v v.unop.len A f) =
      barBidegreeLift C z w w.unop.len
        ((SimplexCategory.toCat.map i.unop).toFunctor ⋙ A ⋙ degreeMap C i)
        ((C.enriched.Hom
          (A.obj ((SimplexCategory.toCat.map i.unop).toFunctor.obj (Fin.last w.unop.len)))
          z).map i
          (@CategoryStruct.comp (degreeObjects C v) (degreeCategory C v).toCategoryStruct
            (A.obj ((SimplexCategory.toCat.map i.unop).toFunctor.obj (Fin.last w.unop.len)))
            (A.obj (Fin.last v.unop.len)) z
            (A.map (homOfLE (Fin.le_last
              ((SimplexCategory.toCat.map i.unop).toFunctor.obj (Fin.last w.unop.len))))) f)) := by
  change ((SimplexCategory.toCat.map i.unop).toFunctor ⋙
    barBidegreeLift C z v v.unop.len A f) ⋙ overDegreeMap C z i = _
  rw [barBidegreeLift_horizontal, barBidegreeLift_vertical]
  rfl

/-- Every original enriched functor maps the full lift by its actual Hom map at the last object. -/
theorem barComponentDegreeLift_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (z : C.Obj) (v : SimplexCategoryᵒᵖ)
    (A : Fin (v.unop.len + 1) ⥤ degreeObjects C v)
    (f : (C.enriched.Hom (A.obj (Fin.last v.unop.len)) z).obj v) :
    (barComponentMap F z).app v (barBidegreeLift C z v v.unop.len A f) =
      barBidegreeLift D (F.obj z) v v.unop.len (A ⋙ degreeFunctor F v)
        ((F.map (A.obj (Fin.last v.unop.len)) z).app v f) :=
  chainLift_post A f (degreeFunctor F v)

end
end DaggerOriginalSimplicialCategoryBarBidegreeDecomposition
