import OriginalSimplicialCategoryBarRowSimplexFamily
import NativeOverChainFixedProjection

/-!
# Actual pullbacks of the original row projection over every original base simplex

All vertical degrees and original maps are retained. The product with the
original last Hom has the native IsPullback universal property over the native
Yoneda map of the entire original base chain, without any homotopical premise.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalSimplicialCategoryBarRowSimplexFamily
open DaggerNativeOverChainDecomposition DaggerNativeOverChainFixedProjection
universe u
namespace DaggerOriginalSimplicialCategoryBarRowSimplexPullback
noncomputable section

/-- The entire original chain and parameter give the exact pointwise pullback in every degree. -/
theorem rowSimplexFamily_app_isPullback (C : SimplicialCat.{u, u}) (z : C.Obj) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (v : SimplexCategoryᵒᵖ) :
    IsPullback ((rowSimplexFamily C z A).app v)
      ((fst (Δ[n] : SSet.{u}) (C.enriched.Hom (A.obj (Fin.last k)) z)).app v)
      ((rowProjection C z k).app v) ((baseRowSimplexMap C A).app v) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (rowSimplexFamily_projection C z A) v, ?_, ?_⟩
  · rintro ⟨t, f⟩ ⟨s, g⟩ ⟨hf, ht⟩
    change t = s at ht
    subst s
    apply Prod.ext
    · rfl
    · exact chainLift_injective (A ⋙ degreeMap C (SSet.stdSimplex.objEquiv t).op) hf
  · intro B t h
    have hb : B ⋙ Over.forget (T := degreeObjects C v) z =
        A ⋙ degreeMap C (SSet.stdSimplex.objEquiv t).op :=
      h.trans (baseRowYoneda_apply C A v t)
    obtain ⟨f, hf⟩ := chainLift_surjective_on_fibre
      (A ⋙ degreeMap C (SSet.stdSimplex.objEquiv t).op) B hb
    exact ⟨(t, f), hf, rfl⟩

/-- The unchanged original product and maps form an actual native simplicial pullback. -/
theorem rowSimplexFamily_isPullback (C : SimplicialCat.{u, u}) (z : C.Obj) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) :
    IsPullback (rowSimplexFamily C z A)
      (fst (Δ[n] : SSet.{u}) (C.enriched.Hom (A.obj (Fin.last k)) z))
      (rowProjection C z k) (baseRowSimplexMap C A) := by
  let c := PullbackCone.mk (rowSimplexFamily C z A)
    (fst (Δ[n] : SSet.{u}) (C.enriched.Hom (A.obj (Fin.last k)) z))
    (rowSimplexFamily_projection C z A)
  apply IsPullback.of_isLimit (c := c)
  apply evaluationJointlyReflectsLimits
  intro v
  let h := rowSimplexFamily_app_isPullback C z A v
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ h.isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cones.ext (Iso.refl _) ?_
    rintro (_ | _ | _) <;> rfl

end
end DaggerOriginalSimplicialCategoryBarRowSimplexPullback
