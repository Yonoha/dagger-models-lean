import OriginalSimplicialCategoryBarRowSimplexFamily
import OriginalSimplicialCategorySimplexTransportWeakEquivalence

/-!
# Original horizontal row restrictions are the full original simplex transports

For every actual original chain and every horizontal simplex operator, use the
original arrow from the restricted last object to the original last object.
The comparison on the exact product fibers retains the standard-simplex
parameter. It is weak when the actual original pi0 category is a groupoid.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels HomotopicalAlgebra
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalSimplicialCategoryBarRowSimplexFamily
open DaggerOriginalSimplicialCategorySimplexTransport
open DaggerOriginalSimplicialCategorySimplexTransportWeakEquivalence
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerNativeOverChainDecomposition
universe u
namespace DaggerOriginalSimplicialCategoryBarRowHorizontalTransport
noncomputable section

/-- The exact original Hom simplex between the restricted and original last base objects. -/
def lastChainArrow (C : SimplicialCat.{u, u}) {k l n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    (C.enriched.Hom
      (A.obj ((SimplexCategory.toCat.map α).toFunctor.obj (Fin.last l)))
      (A.obj (Fin.last k))).obj (op ⦋n⦌) :=
  A.map (homOfLE (Fin.le_last ((SimplexCategory.toCat.map α).toFunctor.obj (Fin.last l))))

/-- Restricting the full original row family is exactly original relative simplex precomposition. -/
theorem rowSimplexFamily_horizontal (C : SimplicialCat.{u, u}) (z : C.Obj) {k l n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    rowSimplexFamily C z A ≫ (barRows C z).map α.op =
      relativeSimplexPrecompose C (lastChainArrow C A α) z ≫
        rowSimplexFamily C z ((SimplexCategory.toCat.map α).toFunctor ⋙ A) := by
  apply NatTrans.ext
  funext v p
  change (SimplexCategory.toCat.map α).toFunctor ⋙
      chainLift (A ⋙ degreeMap C (SSet.stdSimplex.objEquiv p.1).op) p.2 = _
  rw [chainLift_precompose]
  change chainLift
      (((SimplexCategory.toCat.map α).toFunctor ⋙ A) ⋙
        degreeMap C (SSet.stdSimplex.objEquiv p.1).op)
      ((C.enriched.comp
        (A.obj ((SimplexCategory.toCat.map α).toFunctor.obj (Fin.last l)))
        (A.obj (Fin.last k)) z).app v
          ((C.enriched.Hom
            (A.obj ((SimplexCategory.toCat.map α).toFunctor.obj (Fin.last l)))
            (A.obj (Fin.last k))).map (SSet.stdSimplex.objEquiv p.1).op
              (lastChainArrow C A α), p.2)) =
    chainLift
      (((SimplexCategory.toCat.map α).toFunctor ⋙ A) ⋙
        degreeMap C (SSet.stdSimplex.objEquiv p.1).op)
      ((simplexPrecompose C (lastChainArrow C A α) z).app v p)
  rw [show p = (p.1, p.2) from rfl, simplexPrecompose_apply,
    SSet.yonedaEquiv_symm_app_apply (X := C.enriched.Hom
      (A.obj ((SimplexCategory.toCat.map α).toFunctor.obj (Fin.last l)))
      (A.obj (Fin.last k))) (n := op ⦋n⦌) (m := v) (lastChainArrow C A α)]

/-- The exact relative comparison between original row fibers is weak under actual pi0 groupoid. -/
theorem rowHorizontalTransport_weakEquivalence (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : C.Obj) {k l n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    WeakEquivalence (relativeSimplexPrecompose C (lastChainArrow C A α) z) :=
  relativeSimplexPrecompose_weakEquivalence_of_actualGroupoid C hC (lastChainArrow C A α) z

end
end DaggerOriginalSimplicialCategoryBarRowHorizontalTransport
