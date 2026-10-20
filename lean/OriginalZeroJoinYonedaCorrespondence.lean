import OriginalPrefixBoundarySuccessorMappingPullback

/-!
# Exact Yoneda correspondence for the original vertex-join presheaf

Maps from an original standard simplex into J_0 X correspond to maps from
its native vertex join into X. Original Yoneda gives this correspondence
and its naturality in both original simplex operators and target maps.
No boundary, Kan or filling assumption is used.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornPrefix

universe u

namespace DaggerOriginalZeroJoinYonedaCorrespondence

/-- Original Yoneda evaluation commutes with every actual simplex-category operator. -/
theorem yonedaEquiv_precomp_actual {X : SSet.{u}} {d e : SimplexCategory}
    (α : d ⟶ e) (σ : SSet.stdSimplex.obj e ⟶ X) :
    SSet.yonedaEquiv (SSet.stdSimplex.map α ≫ σ) = X.map α.op (SSet.yonedaEquiv σ) := by
  induction d using SimplexCategory.rec with | h d =>
    induction e using SimplexCategory.rec with | h e =>
      exact yonedaEquiv_precomp_operator σ α

/-- The native vertex-join Yoneda correspondence, retaining the actual joined object. -/
def zeroJoinYonedaEquiv (d : SimplexCategory) (X : SSet.{u}) :
    (SSet.stdSimplex.obj d ⟶ joinedPresheaf ⦋0⦌ X) ≃
      (SSet.stdSimplex.obj ((ordinalJoinLeft ⦋0⦌).obj d) ⟶ X) :=
  (SSet.yonedaEquiv (X := joinedPresheaf ⦋0⦌ X) (n := d)).trans
    (SSet.yonedaEquiv (X := X) (n := (ordinalJoinLeft ⦋0⦌).obj d)).symm

/-- The correspondence is exactly Yoneda at the same original joined degree. -/
theorem zeroJoinYonedaEquiv_eval (d : SimplexCategory) (X : SSet.{u})
    (a : SSet.stdSimplex.obj d ⟶ joinedPresheaf ⦋0⦌ X) :
    SSet.yonedaEquiv (zeroJoinYonedaEquiv d X a) = SSet.yonedaEquiv a := by
  exact Equiv.apply_symm_apply _ _

/-- Precomposition is the exact native joined operator under the same correspondence. -/
theorem zeroJoinYonedaEquiv_precomp {X : SSet.{u}} {d e : SimplexCategory}
    (α : d ⟶ e) (a : SSet.stdSimplex.obj e ⟶ joinedPresheaf ⦋0⦌ X) :
    zeroJoinYonedaEquiv d X (SSet.stdSimplex.map α ≫ a) =
      SSet.stdSimplex.map ((ordinalJoinLeft ⦋0⦌).map α) ≫ zeroJoinYonedaEquiv e X a := by
  apply (SSet.yonedaEquiv (X := X) (n := (ordinalJoinLeft ⦋0⦌).obj d)).injective
  rw [zeroJoinYonedaEquiv_eval, yonedaEquiv_precomp_actual,
    yonedaEquiv_precomp_actual, zeroJoinYonedaEquiv_eval]
  rfl

/-- The correspondence commutes with the original target map, with its exact image retained. -/
theorem zeroJoinYonedaEquiv_postcomp {X Y : SSet.{u}} (p : X ⟶ Y)
    (d : SimplexCategory) (a : SSet.stdSimplex.obj d ⟶ joinedPresheaf ⦋0⦌ X) :
    zeroJoinYonedaEquiv d Y (a ≫ Functor.whiskerLeft (ordinalJoinLeft ⦋0⦌).op p) =
      zeroJoinYonedaEquiv d X a ≫ p := by
  apply (SSet.yonedaEquiv (X := Y) (n := (ordinalJoinLeft ⦋0⦌).obj d)).injective
  rw [zeroJoinYonedaEquiv_eval, SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp,
    zeroJoinYonedaEquiv_eval]
  rfl

end DaggerOriginalZeroJoinYonedaCorrespondence
