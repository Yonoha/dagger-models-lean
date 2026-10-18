import OriginalSimplicialCategoryBarRowSimplexPullback
import OriginalSimplicialCategoryBarRowHorizontalTransport

/-!
# Actual native pullback maps of every original horizontal bar-row restriction are weak

Define the comparison by Mathlib's pullback.map using the actual original bar
row map, actual base row map and unchanged simplex parameter. The original
product-fiber isomorphisms identify this exact comparison with the original
relative simplex precomposition. Actual original pi0 groupoid suffices.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite Simplicial DaggerModels HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalSimplicialCategoryBarRowSimplexFamily
open DaggerOriginalSimplicialCategoryBarRowSimplexPullback
open DaggerOriginalSimplicialCategoryBarRowHorizontalTransport
open DaggerOriginalSimplicialCategorySimplexTransport DaggerOriginalAmbientDaggerPiZeroGroupoid
universe u
namespace DaggerOriginalSimplicialCategoryBarRowPullbackTransport
noncomputable section

/-- The actual base-row restriction sends the entire original simplex to its restriction. -/
theorem baseRowSimplexMap_horizontal (C : SimplicialCat.{u, u}) {k l n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    baseRowSimplexMap C A ≫ (baseRows C).map α.op =
      baseRowSimplexMap C ((SimplexCategory.toCat.map α).toFunctor ⋙ A) := by
  unfold baseRowSimplexMap
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

/-- The actual native pullback of the original row projection along the entire original simplex. -/
abbrev rowSimplexPullback (C : SimplicialCat.{u, u}) (z : C.Obj) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) : SSet.{u} :=
  pullback (rowProjection C z k) (baseRowSimplexMap C A)

/-- The original product fiber is isomorphic to the native pullback over this simplex. -/
def rowSimplexPullbackIso (C : SimplicialCat.{u, u}) (z : C.Obj) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) :
    (Δ[n] : SSet.{u}) ⊗ C.enriched.Hom (A.obj (Fin.last k)) z ≅ rowSimplexPullback C z A :=
  (rowSimplexFamily_isPullback C z A).isoPullback

/-- The native pullback identification retains exactly the original row-family inclusion. -/
theorem rowSimplexPullbackIso_hom_fst (C : SimplicialCat.{u, u}) (z : C.Obj) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) :
    (rowSimplexPullbackIso C z A).hom ≫
      pullback.fst (rowProjection C z k) (baseRowSimplexMap C A) = rowSimplexFamily C z A :=
  (rowSimplexFamily_isPullback C z A).isoPullback_hom_fst

/-- The native pullback identification retains exactly the original simplex parameter projection. -/
theorem rowSimplexPullbackIso_hom_snd (C : SimplicialCat.{u, u}) (z : C.Obj) {k n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) :
    (rowSimplexPullbackIso C z A).hom ≫
      pullback.snd (rowProjection C z k) (baseRowSimplexMap C A) =
        fst (Δ[n] : SSet.{u}) (C.enriched.Hom (A.obj (Fin.last k)) z) :=
  (rowSimplexFamily_isPullback C z A).isoPullback_hom_snd

/-- Native pullback.map of the original horizontal bar and base maps, keeping the parameter. -/
def rowHorizontalPullbackMap (C : SimplicialCat.{u, u}) (z : C.Obj) {k l n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    rowSimplexPullback C z A ⟶
      rowSimplexPullback C z ((SimplexCategory.toCat.map α).toFunctor ⋙ A) :=
  pullback.map (rowProjection C z k) (baseRowSimplexMap C A)
    (rowProjection C z l)
    (baseRowSimplexMap C ((SimplexCategory.toCat.map α).toFunctor ⋙ A))
    ((barRows C z).map α.op) (𝟙 (Δ[n] : SSet.{u})) ((baseRows C).map α.op)
    (rowProjection_horizontal C z α).symm (by
      rw [Category.id_comp]
      exact baseRowSimplexMap_horizontal C A α)

/-- The comparison is induced by the actual original row map on its entire first leg. -/
theorem rowHorizontalPullbackMap_fst (C : SimplicialCat.{u, u}) (z : C.Obj) {k l n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    rowHorizontalPullbackMap C z A α ≫ pullback.fst (rowProjection C z l)
      (baseRowSimplexMap C ((SimplexCategory.toCat.map α).toFunctor ⋙ A)) =
        pullback.fst (rowProjection C z k) (baseRowSimplexMap C A) ≫
          (barRows C z).map α.op := by
  unfold rowHorizontalPullbackMap pullback.map
  rw [pullback.lift_fst]

/-- The comparison keeps exactly the same original parameter on its entire second leg. -/
theorem rowHorizontalPullbackMap_snd (C : SimplicialCat.{u, u}) (z : C.Obj) {k l n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    rowHorizontalPullbackMap C z A α ≫ pullback.snd (rowProjection C z l)
      (baseRowSimplexMap C ((SimplexCategory.toCat.map α).toFunctor ⋙ A)) =
        pullback.snd (rowProjection C z k) (baseRowSimplexMap C A) := by
  unfold rowHorizontalPullbackMap pullback.map
  rw [pullback.lift_snd, Category.comp_id]

/-- The native pullback comparison is original relative simplex transport under the actual iso. -/
theorem rowSimplexPullbackIso_horizontal (C : SimplicialCat.{u, u}) (z : C.Obj) {k l n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    (rowSimplexPullbackIso C z A).hom ≫ rowHorizontalPullbackMap C z A α =
      relativeSimplexPrecompose C (lastChainArrow C A α) z ≫
        (rowSimplexPullbackIso C z ((SimplexCategory.toCat.map α).toFunctor ⋙ A)).hom := by
  apply pullback.hom_ext
  · change ((rowSimplexPullbackIso C z A).hom ≫ rowHorizontalPullbackMap C z A α) ≫
        pullback.fst (rowProjection C z l)
          (baseRowSimplexMap C ((SimplexCategory.toCat.map α).toFunctor ⋙ A)) =
      (relativeSimplexPrecompose C (lastChainArrow C A α) z ≫
        (rowSimplexPullbackIso C z ((SimplexCategory.toCat.map α).toFunctor ⋙ A)).hom) ≫
          pullback.fst (rowProjection C z l)
            (baseRowSimplexMap C ((SimplexCategory.toCat.map α).toFunctor ⋙ A))
    rw [Category.assoc, rowHorizontalPullbackMap_fst C z A α, ← Category.assoc,
      rowSimplexPullbackIso_hom_fst, Category.assoc,
      rowSimplexPullbackIso_hom_fst C z (k := l) (n := n)
        ((SimplexCategory.toCat.map α).toFunctor ⋙ A)]
    exact rowSimplexFamily_horizontal C z A α
  · change ((rowSimplexPullbackIso C z A).hom ≫ rowHorizontalPullbackMap C z A α) ≫
        pullback.snd (rowProjection C z l)
          (baseRowSimplexMap C ((SimplexCategory.toCat.map α).toFunctor ⋙ A)) =
      (relativeSimplexPrecompose C (lastChainArrow C A α) z ≫
        (rowSimplexPullbackIso C z ((SimplexCategory.toCat.map α).toFunctor ⋙ A)).hom) ≫
          pullback.snd (rowProjection C z l)
            (baseRowSimplexMap C ((SimplexCategory.toCat.map α).toFunctor ⋙ A))
    rw [Category.assoc, rowHorizontalPullbackMap_snd C z A α, rowSimplexPullbackIso_hom_snd,
      Category.assoc, rowSimplexPullbackIso_hom_snd C z (k := l) (n := n)
        ((SimplexCategory.toCat.map α).toFunctor ⋙ A)]
    exact (relativeSimplexPrecompose_fst C (lastChainArrow C A α) z).symm

/-- Every native horizontal pullback comparison is weak for the actual original pi0 groupoid. -/
theorem rowHorizontalPullbackMap_weakEquivalence (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : C.Obj) {k l n : ℕ}
    (A : Fin (k + 1) ⥤ degreeObjects C (op ⦋n⦌)) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    WeakEquivalence (rowHorizontalPullbackMap C z A α) := by
  have : WeakEquivalence (relativeSimplexPrecompose C (lastChainArrow C A α) z) :=
    rowHorizontalTransport_weakEquivalence C hC z A α
  have : WeakEquivalence ((rowSimplexPullbackIso C z A).hom) := inferInstance
  have : WeakEquivalence (relativeSimplexPrecompose C (lastChainArrow C A α) z ≫
      (rowSimplexPullbackIso C z ((SimplexCategory.toCat.map α).toFunctor ⋙ A)).hom) :=
    inferInstance
  exact weakEquivalence_of_precomp_of_fac (rowSimplexPullbackIso_horizontal C z A α)

end
end DaggerOriginalSimplicialCategoryBarRowPullbackTransport
