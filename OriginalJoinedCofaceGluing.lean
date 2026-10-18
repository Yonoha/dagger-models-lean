import OriginalJoinedPrefixBoundaryPreimage
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Actual gluing of a prescribed joined boundary and one joined coface

The overlap is the image of the smaller joined boundary, proved by the exact
preimage calculation. Mathlib's subcomplex pushout constructs a map on the
actual union from two compatible maps. The compatibility premise is only
their equality on the overlap, not a filler or a map on the full joined horn.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalJoinedPrefixBoundaryPreimage
open DaggerOriginalJoinedCofaces

universe u

namespace DaggerOriginalJoinedCofaceGluing

noncomputable section

/-- An inclusion between equal subcomplexes is an isomorphism. -/
theorem homOfLE_isIso_of_eq {Y : SSet.{u}} {A B : Y.Subcomplex} (h : A = B) :
    IsIso (SSet.Subcomplex.homOfLE h.le) := by
  subst B
  change IsIso (𝟙 (A : SSet.{u}))
  infer_instance

/-- Glue an original joined coface to a prescribed prefix-boundary map. -/
theorem glue_coface {X : SSet.{u}} (k n : ℕ) (i : Fin (n + 2))
    (g : (prefixBoundary k (n + 1) : SSet.{u}) ⟶ X)
    (h : (Δ[k + n + 1] : SSet.{u}) ⟶ X)
    (w : prefixBoundaryMap k (SimplexCategory.δ i) ≫ g = (prefixBoundary k n).ι ≫ h) :
    ∃ Γ : ((prefixBoundary k (n + 1) ⊔
        SSet.stdSimplex.face {suffixIndex k (n + 1) i}ᶜ :
        (Δ[k + (n + 1) + 1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X,
      SSet.Subcomplex.homOfLE le_sup_left ≫ Γ = g ∧
      (SSet.stdSimplex.faceSingletonComplIso (suffixIndex k (n + 1) i)).hom ≫
        SSet.Subcomplex.homOfLE le_sup_right ≫ Γ = h := by
  let A := prefixBoundary.{u} k (n + 1)
  let B := prefixBoundary.{u} k n
  let F := SSet.stdSimplex.face.{u} {suffixIndex k (n + 1) i}ᶜ
  let f := SSet.stdSimplex.δ.{u} (suffixIndex k (n + 1) i)
  let e := SSet.stdSimplex.faceSingletonComplIso.{u} (suffixIndex k (n + 1) i)
  have himage : B.image f = A ⊓ F := prefixBoundary_image_coface k n i
  let t : (B : SSet.{u}) ⟶
      ((A ⊓ F : (Δ[k + (n + 1) + 1] : SSet.{u}).Subcomplex) : SSet.{u}) :=
    B.toImage f ≫ SSet.Subcomplex.homOfLE himage.le
  haveI : IsIso (SSet.Subcomplex.homOfLE himage.le) := homOfLE_isIso_of_eq himage
  haveI : Epi t := by dsimp [t]; infer_instance
  have ht : t ≫ (A ⊓ F).ι = B.ι ≫ f := by
    dsimp [t]
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toImage_ι]
  have hleft : t ≫ SSet.Subcomplex.homOfLE inf_le_left =
      prefixBoundaryMap k (SimplexCategory.δ i) := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, ht]
    have hd := prefixBoundaryMap_comp_inclusion.{u} k (SimplexCategory.δ i)
    rw [joinMap_coface] at hd
    exact hd.symm
  have hright : t ≫ SSet.Subcomplex.homOfLE inf_le_right = B.ι ≫ e.hom := by
    apply (cancel_mono F.ι).mp
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, ht, Category.assoc]
    exact congrArg (fun a ↦ B.ι ≫ a)
      (SSet.stdSimplex.faceSingletonComplIso_hom_ι (suffixIndex k (n + 1) i)).symm
  have hc : SSet.Subcomplex.homOfLE inf_le_left ≫ g =
      SSet.Subcomplex.homOfLE inf_le_right ≫ (e.inv ≫ h) := by
    apply (cancel_epi t).mp
    rw [← Category.assoc, hleft, ← Category.assoc, hright, Category.assoc,
      ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp]
    exact w
  have sq : SSet.Subcomplex.BicartSq (A ⊓ F) A F (A ⊔ F) := ⟨rfl, rfl⟩
  let Γ := sq.isPushout.desc g (e.inv ≫ h) hc
  refine ⟨Γ, sq.isPushout.inl_desc g (e.inv ≫ h) hc, ?_⟩
  rw [sq.isPushout.inr_desc g (e.inv ≫ h) hc, ← Category.assoc,
    e.hom_inv_id, Category.id_comp]

end

end DaggerOriginalJoinedCofaceGluing
