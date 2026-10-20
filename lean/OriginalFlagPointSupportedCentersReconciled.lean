import OriginalCounitRightConeQCenterSupportReconciled
import ChosenNecklacePointMaps
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Original normalized necklaces supported on point images

A totally nondegenerate original necklace whose entire image is contained
in a union of images of zero-simplices has no positive beads. Its actual
endpoints therefore coincide. This supplies the zero-dimensional overlap
obstruction without replacing the original necklace quotient or its centers.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace NecklaceCode
open DaggerOriginalFlagFlankification
open DaggerOriginalCounitRightConeQCenterSupport

universe u v

namespace DaggerOriginalFlagPointSupportedCenters

noncomputable section

/-- Every positive-degree simplex in the image of an actual point map is degenerate. -/
theorem point_image_degenerate {X : SSet.{u}} (f : (Δ[0] : SSet.{u}) ⟶ X)
    {n : ℕ} (hn : 0 < n) (x : X.obj (op ⦋n⦌))
    (hx : x ∈ Set.range (f.app (op ⦋n⦌))) : x ∈ X.degenerate n := by
  obtain ⟨s, rfl⟩ := hx
  let θ : ⦋n⦌ ⟶ ⦋0⦌ := SimplexCategory.const _ _ 0
  have hs : (Δ[0] : SSet.{u}).map θ.op (zeroSimplex 0) = s :=
    (zeroSimplex_unique _).trans (zeroSimplex_unique s).symm
  refine ⟨0, hn, θ, f.app (op ⦋0⦌) (zeroSimplex 0), ?_⟩
  have h := congrFun (f.naturality θ.op) (zeroSimplex 0)
  change f.app (op ⦋n⦌) ((Δ[0] : SSet.{u}).map θ.op (zeroSimplex 0)) =
    X.map θ.op (f.app (op ⦋0⦌) (zeroSimplex 0)) at h
  rw [hs] at h
  exact h.symm

private theorem bead_length_positive {T : NecklaceCode} (c : T.Bead) :
    0 < c.length := by
  have hc : c.left.val < c.right.val := c.lt
  simp only [Bead.length, Bead.interval, Fin.card_Icc]
  omega

/-- The original nondegenerate condition rules out every bead in a point-supported map. -/
theorem point_supported_nondegenerate_length_zero
    {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}
    (p : Degree X a b n) (hnd : TotallyNondegenerate X a b n p)
    {J : Type v} (points : J → ((Δ[0] : SSet.{u}) ⟶ X))
    (hsupport : SSet.Subcomplex.range p.1.map ≤
      ⨆ j, SSet.Subcomplex.range (points j)) : p.1.code.len = 0 := by
  by_contra hlen
  have hv : (0 : Fin (p.1.code.len + 1)) < Fin.last p.1.code.len := by
    change 0 < p.1.code.len
    omega
  obtain ⟨c, _, _⟩ := p.1.code.exists_bead_at (Fin.last p.1.code.len) hv
  have hbead : beadElement p.1 c ∈ (SSet.Subcomplex.range p.1.map).obj
      (op ⦋c.length⦌) := by
    refine ⟨SSet.yonedaEquiv (p.1.code.beadSimplex c), ?_⟩
    exact (SSet.yonedaEquiv_comp (p.1.code.beadSimplex c) p.1.map).symm
  have hs := hsupport (op ⦋c.length⦌) hbead
  simp only [Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion] at hs
  obtain ⟨j, hj⟩ := hs
  have hd := point_image_degenerate (points j) (bead_length_positive c)
    (beadElement p.1 c) hj
  exact ((X.mem_nonDegenerate_iff_notMem_degenerate _).1 (hnd c)) hd

/-- A point-supported original normalized necklace cannot join distinct endpoints. -/
theorem point_supported_nondegenerate_endpoints_eq
    {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}
    (p : Degree X a b n) (hnd : TotallyNondegenerate X a b n p)
    {J : Type v} (points : J → ((Δ[0] : SSet.{u}) ⟶ X))
    (hsupport : SSet.Subcomplex.range p.1.map ≤
      ⨆ j, SSet.Subcomplex.range (points j)) : a = b := by
  have hlen := point_supported_nondegenerate_length_zero p hnd points hsupport
  have hfl : p.1.code.first = p.1.code.last := by
    apply p.1.code.verticesEquiv.injective
    simp only [NecklaceCode.first, NecklaceCode.last, Equiv.apply_symm_apply]
    apply ULift.ext
    apply Fin.ext
    exact hlen.symm
  exact p.1.first.symm.trans ((congrArg (p.1.map.app (op ⦋0⦌)) hfl).trans p.1.last)

/-- The same obstruction applies to the actual canonical center of a quotient class. -/
theorem center_point_supported_endpoints_eq
    {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (n : ℕ)
    (t : (flagHom X a b).obj (op ⦋n⦌))
    {J : Type v} (points : J → ((Δ[0] : SSet.{u}) ⟶ X))
    (hsupport : SSet.Subcomplex.range (centerDegreeObj X a b n t).1.map ≤
      ⨆ j, SSet.Subcomplex.range (points j)) : a = b :=
  point_supported_nondegenerate_endpoints_eq (centerDegreeObj X a b n t)
    (centerDegreeObj_nondegenerate X a b n t) points hsupport

end

end DaggerOriginalFlagPointSupportedCenters
