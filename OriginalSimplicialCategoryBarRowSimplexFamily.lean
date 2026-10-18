import OriginalSimplicialCategoryBarRows

/-!
# Original over-chain families over every original base-row simplex

An original k-chain in enrichment degree n gives its actual native Yoneda map
into the base row. The original last Hom supplies full lifts for every simplex
parameter. All vertical operators retain the original chain and original Hom.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalSimplicialCategoryBarBidegreeDecomposition
universe u
namespace DaggerOriginalSimplicialCategoryBarRowSimplexFamily
noncomputable section

/-- The exact original base-row simplex gives its native Yoneda parameter map. -/
def baseRowSimplexMap (C : SimplicialCat.{u, u}) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) : (Δ[n] : SSet.{u}) ⟶ baseRow C k :=
  (SSet.yonedaEquiv (X := baseRow C k) (n := ⦋n⦌)).symm A

/-- The actual parameter simplex restricts the entire original base chain by its degree map. -/
theorem baseRowYoneda_apply (C : SimplicialCat.{u, u}) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (v : SimplexCategoryᵒᵖ)
    (t : (Δ[n] : SSet.{u}).obj v) :
    (baseRowSimplexMap C A).app v t =
      A ⋙ degreeMap C (SSet.stdSimplex.objEquiv t).op := by
  unfold baseRowSimplexMap
  rw [SSet.yonedaEquiv_symm_app_apply (X := baseRow C k) (n := op ⦋n⦌) (m := v) A]
  rfl

/-- The entire original parameter and final original Hom arrow determine the row lift. -/
def rowSimplexFamily (C : SimplicialCat.{u, u}) (z : C.Obj) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) :
    (Δ[n] : SSet.{u}) ⊗ C.enriched.Hom (A.obj (Fin.last k)) z ⟶ barRow C z k where
  app v p := barBidegreeLift C z v k
    (A ⋙ degreeMap C (SSet.stdSimplex.objEquiv p.1).op) p.2
  naturality v w i := by
    funext p
    change barBidegreeLift C z w k
        (A ⋙ degreeMap C (SSet.stdSimplex.objEquiv (Δ[n].map i p.1)).op)
        ((C.enriched.Hom (A.obj (Fin.last k)) z).map i p.2) =
      barBidegreeLift C z v k
        (A ⋙ degreeMap C (SSet.stdSimplex.objEquiv p.1).op) p.2 ⋙ overDegreeMap C z i
    rw [barBidegreeLift_vertical]
    change (barBidegreeEquiv C z w k).symm ⟨_, _⟩ =
      (barBidegreeEquiv C z w k).symm ⟨_, _⟩
    apply congrArg (barBidegreeEquiv C z w k).symm
    refine Sigma.ext ?_ HEq.rfl
    change A ⋙ degreeMap C (SSet.stdSimplex.objEquiv (Δ[n].map i p.1)).op =
      (A ⋙ degreeMap C (SSet.stdSimplex.objEquiv p.1).op) ⋙ degreeMap C i
    rw [Functor.assoc, ← degreeMap_comp]
    rfl

/-- Each row-family value is the full native lift of the original restricted base chain. -/
theorem rowSimplexFamily_apply (C : SimplicialCat.{u, u}) (z : C.Obj) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (v : SimplexCategoryᵒᵖ)
    (t : (Δ[n] : SSet.{u}).obj v)
    (f : (C.enriched.Hom (A.obj (Fin.last k)) z).obj v) :
    (rowSimplexFamily C z A).app v (t, f) =
      barBidegreeLift C z v k (A ⋙ degreeMap C (SSet.stdSimplex.objEquiv t).op) f := rfl

/-- The family projection is precisely the native Yoneda map of the original base-row simplex. -/
theorem rowSimplexFamily_projection (C : SimplicialCat.{u, u}) (z : C.Obj) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) :
    rowSimplexFamily C z A ≫ rowProjection C z k =
      fst (Δ[n] : SSet.{u}) (C.enriched.Hom (A.obj (Fin.last k)) z) ≫
        baseRowSimplexMap C A := by
  apply NatTrans.ext
  funext v p
  change (barBidegreeLift C z v k
      (A ⋙ degreeMap C (SSet.stdSimplex.objEquiv p.1).op) p.2) ⋙
        Over.forget (T := degreeObjects C v) z =
      (baseRowSimplexMap C A).app v p.1
  rw [baseRowYoneda_apply]
  exact DaggerNativeOverChainDecomposition.chainLift_forget _ _

end
end DaggerOriginalSimplicialCategoryBarRowSimplexFamily
