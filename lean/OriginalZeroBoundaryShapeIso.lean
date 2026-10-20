import OriginalJoinedBoundaryProjection

/-!
# The actual zero-prefix boundary is the original right standard simplex

Use the native face representability and the original right ordinal block.
The order isomorphism includes the exact cast for 0+n=n. Its induced native
face isomorphism has precisely the original boundary suffix inclusion as its
forward map. The resulting isomorphism is natural in every simplex operator.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalJoinedBoundarySuffixInclusion

universe u

namespace DaggerOriginalZeroBoundaryShapeIso

noncomputable section

/-- The literal zero-prefix boundary is the face omitting its sole prefix vertex. -/
theorem prefixBoundary_zero (n : ℕ) :
    prefixBoundary.{u} 0 n = SSet.stdSimplex.face {(0 : Fin (0 + n + 2))}ᶜ := by
  apply le_antisymm
  · rw [prefixBoundary, iSup_le_iff]
    intro j
    have hj : j = 0 := Fin.ext (by have h := j.isLt; change j.val = 0; omega)
    rw [hj]
    exact le_rfl
  · exact le_iSup (fun j : Fin 1 ↦ SSet.stdSimplex.face {prefixIndex 0 n j}ᶜ) 0

/-- The original right vertices are order isomorphic to the actual suffix-only face. -/
def zeroSuffixOrderIso (n : ℕ) : Fin (n + 1) ≃o ({0}ᶜ : Finset (Fin (0 + n + 2))) :=
  (Fin.castOrderIso (show n + 1 = 0 + n + 1 by omega)).trans
    (SSet.stdSimplex.finSuccAboveOrderIsoFinset (0 : Fin (0 + n + 2)))

/-- The order isomorphism is exactly the native original right-block map on vertices. -/
theorem zeroSuffixOrderIso_eval (n : ℕ) (a : Fin (n + 1)) :
    (zeroSuffixOrderIso n a).val = (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌).toOrderHom a := by
  rw [AugmentedSimplexCategory.inr'_eval]
  change (0 : Fin (0 + n + 2)).succAbove (Fin.cast (by omega) a) = _
  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.zero_le _)]
  apply Fin.ext
  change a.val + 1 = ⦋0⦌.len.succ + a.val
  rw [SimplexCategory.len_mk]
  omega

/-- The native original standard simplex represents the actual zero-prefix boundary. -/
def zeroBoundaryShapeIso (n : ℕ) :
    (Δ[n] : SSet.{u}) ≅ (prefixBoundary 0 n : SSet.{u}) :=
  (SSet.stdSimplex.isoOfRepresentableBy
    (SSet.stdSimplex.faceRepresentableBy _ n (zeroSuffixOrderIso n))).trans
      (SSet.Subcomplex.eqToIso (prefixBoundary_zero n).symm)

/-- Its forward map followed by inclusion is exactly the original right-block simplex map. -/
theorem zeroBoundaryShapeIso_hom_comp (n : ℕ) :
    (zeroBoundaryShapeIso.{u} n).hom ≫ (prefixBoundary 0 n).ι =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌) := by
  change (SSet.stdSimplex.isoOfRepresentableBy
    (SSet.stdSimplex.faceRepresentableBy _ n (zeroSuffixOrderIso n))).hom ≫
      (SSet.Subcomplex.homOfLE (prefixBoundary_zero n).symm.le ≫
        (prefixBoundary 0 n).ι) = _
  rw [SSet.Subcomplex.homOfLE_ι]
  ext q s
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext a
  exact zeroSuffixOrderIso_eval n ((SSet.stdSimplex.objEquiv s).toOrderHom a)

/-- The original suffix inclusion itself, without replacing its forward map, is the native iso. -/
theorem boundarySuffixInclusion_zero_eq (n : ℕ) :
    boundarySuffixInclusion.{u} 0 ⦋n⦌ = (zeroBoundaryShapeIso n).hom := by
  apply (cancel_mono (prefixBoundary 0 n).ι).mp
  have h := boundarySuffixInclusion_comp.{u} 0 ⦋n⦌
  exact h.trans (zeroBoundaryShapeIso_hom_comp n).symm

/-- Every actual zero-prefix suffix inclusion is an isomorphism in arbitrary universe. -/
theorem boundarySuffixInclusion_zero_isIso (n : SimplexCategory) :
    IsIso (boundarySuffixInclusion.{u} 0 n) := by
  induction n using SimplexCategory.rec with | h n =>
    rw [boundarySuffixInclusion_zero_eq]
    infer_instance

/-- The entire original zero-prefix shape functor is naturally isomorphic to the standard simplex.
-/
def zeroBoundaryShapeNaturalIso : SSet.stdSimplex.{u} ≅ prefixBoundaryFunctor 0 := by
  haveI : IsIso (boundarySuffixNatural.{u} 0) :=
    (NatTrans.isIso_iff_isIso_app _).mpr boundarySuffixInclusion_zero_isIso
  exact asIso (boundarySuffixNatural 0)

/-- Its forward natural transformation is exactly the original lifted suffix inclusion. -/
theorem zeroBoundaryShapeNaturalIso_hom :
    zeroBoundaryShapeNaturalIso.{u}.hom = boundarySuffixNatural 0 := rfl

end

end DaggerOriginalZeroBoundaryShapeIso
