import OriginalRestBoundaryConeInverseIdentities
import OriginalSuccessorBoundaryProjectionFactorization

/-!
# The actual natural original boundary cone isomorphism and successor pullback

The proved original forward transpose and native glued inverse are mutual
inverses in every degree. Native componentwise isomorphism detection makes the
same natural transpose an actual simplicial-set isomorphism. Transporting the
verified successor pullback through it gives the exact recursive boundary
pullback, with original joined restriction and vertex-projection target map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalSimplexCoslice DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalPrefixBoundaryConeTransposition
open DaggerOriginalRestBoundaryInverseGluing DaggerOriginalRestBoundaryConeInverseIdentities
open DaggerOriginalSuccessorBoundaryPresheafPullback
open DaggerOriginalSuccessorBoundaryProjectionFactorization

universe u

namespace DaggerOriginalRestBoundaryConeIsomorphism

noncomputable section

/-- The same actual original natural cone transpose is bijective in every presheaf degree. -/
theorem restConeTransposition_app_bijective (k : ℕ) (X : SSet.{u})
    (q : SimplexCategoryᵒᵖ) : Function.Bijective ((restBoundaryConeTransposition k X).app q) :=
  (restConeTransposeEquiv k q.unop.len X).bijective

/-- The original natural cone transpose itself is an isomorphism of actual simplicial sets. -/
theorem restConeTransposition_isIso (k : ℕ) (X : SSet.{u}) :
    IsIso (restBoundaryConeTransposition k X) :=
  (NatTrans.isIso_iff_isIso_app _).mpr (fun q ↦
    (isIso_iff_bijective _).mpr (restConeTransposition_app_bijective k X q))

/-- The actual remaining mapping presheaf and original vertex-join boundary presheaf are iso.
-/
def restBoundaryConeIso (k : ℕ) (X : SSet.{u}) :
    restBoundaryJoinedPresheaf k X ≅ boundaryJoinedPresheaf k (joinedPresheaf ⦋0⦌ X) := by
  haveI := restConeTransposition_isIso k X
  exact asIso (restBoundaryConeTransposition k X)

/-- The forward isomorphism map is exactly the previously constructed original cone transpose.
-/
theorem restBoundaryConeIso_hom (k : ℕ) (X : SSet.{u}) :
    (restBoundaryConeIso k X).hom = restBoundaryConeTransposition k X := rfl

/-- The actual natural inverse has exactly the original native glued map in every degree. -/
theorem restBoundaryConeIso_inv_app (k : ℕ) (X : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (t : (boundaryJoinedPresheaf k (joinedPresheaf ⦋0⦌ X)).obj q) :
    (restBoundaryConeIso k X).inv.app q t = inverseRestBoundaryMap k q.unop.len t := by
  apply (restConeTransposeEquiv k q.unop.len X).injective
  change prefixConeTranspose k q.unop.len ((restBoundaryConeIso k X).inv.app q t) =
    prefixConeTranspose k q.unop.len (inverseRestBoundaryMap k q.unop.len t)
  rw [prefixConeTranspose_inverse]
  have h := congrFun (congrArg (fun f ↦ f.app q) (restBoundaryConeIso k X).inv_hom_id) t
  exact h

/-- The original successor boundary satisfies the exact recursive simplicial-set pullback. -/
theorem successorBoundaryConeRestriction_isPullback (k : ℕ) (X : SSet.{u}) :
    IsPullback (successorFirstRestriction k X)
      (successorRestRestriction k X ≫ restBoundaryConeTransposition k X)
      (joinedBoundaryRestriction k X) (boundaryPostcompose k (suffixProjection ⦋0⦌ X)) := by
  apply (successorBoundaryRestriction_isPullback k X).of_iso
    (Iso.refl _) (Iso.refl _) (restBoundaryConeIso k X) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, restBoundaryConeIso_hom]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, restBoundaryConeIso_hom]
    exact (restConeTransposition_comp_postcompose k X).symm

end

end DaggerOriginalRestBoundaryConeIsomorphism
