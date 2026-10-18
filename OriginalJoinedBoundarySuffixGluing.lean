import OriginalJoinedSuffixHornGluing
import OriginalJoinedHornFaceData

/-!
# Actual simultaneous gluing of the joined boundary and suffix horn

Every overlap with the prescribed boundary follows from the original relative
horn commuting square. Since the suffix horn is its actual coface union,
these equations prove agreement on the entire boundary/suffix intersection.
The native subcomplex pushout then constructs the original joined horn map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedCofaceGluing
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedHornFaceData
open DaggerOriginalJoinedSuffixFaceMaps
open DaggerOriginalJoinedSuffixHornGluing

universe u

namespace DaggerOriginalJoinedBoundarySuffixGluing

noncomputable section

/-- The prescribed boundary agrees with every original suffix face on its whole overlap. -/
theorem boundary_face_overlap {X : SSet.{u}} (k n : ℕ) (i j : Fin (n + 2)) (hj : j ≠ i)
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[n + 1, i].ι ≫ β) :
    SSet.Subcomplex.homOfLE inf_le_left ≫ SSet.yonedaEquiv β =
      SSet.Subcomplex.homOfLE inf_le_right ≫ suffixFaceMap k n i j hj φ := by
  obtain ⟨Γ, hleft, hright⟩ := glue_horn_face k n i j hj φ β w
  let A := prefixBoundary.{u} k (n + 1)
  let F := SSet.stdSimplex.face.{u} {suffixIndex k (n + 1) j}ᶜ
  let e := SSet.stdSimplex.faceSingletonComplIso.{u} (suffixIndex k (n + 1) j)
  have hface : SSet.Subcomplex.homOfLE le_sup_right ≫ Γ = suffixFaceMap k n i j hj φ := by
    apply (cancel_epi e.hom).mp
    change e.hom ≫ (SSet.Subcomplex.homOfLE le_sup_right ≫ Γ) =
      e.hom ≫ (e.inv ≫ joinedHornCoface k n i j hj φ)
    rw [e.hom_inv_id_assoc]
    exact hright
  rw [← hleft, ← hface, ← Category.assoc, ← Category.assoc]
  rfl

/-- All coface overlap equations imply agreement on the entire actual boundary/suffix overlap. -/
theorem boundary_suffix_overlap {X : SSet.{u}} (k n : ℕ) (i : Fin (n + 2))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[n + 1, i].ι ≫ β) :
    SSet.Subcomplex.homOfLE inf_le_left ≫ SSet.yonedaEquiv β =
      SSet.Subcomplex.homOfLE inf_le_right ≫ suffixHornMap k n i φ := by
  ext q s
  have hs : s.val ∈ (suffixHorn k (n + 1) i).obj q := s.property.2
  simp only [suffixHorn, Subfunctor.iSup_obj, Set.mem_iUnion] at hs
  obtain ⟨j, hj⟩ := hs
  have hface := boundary_face_overlap k n i j.val j.property φ β w
  have hv := congrArg (fun f ↦ f.app q ⟨s.val, ⟨s.property.1, hj⟩⟩) hface
  have hrestriction := suffixHornMap_face k n i φ j
  have hr := congrArg (fun f ↦ f.app q ⟨s.val, hj⟩) hrestriction
  exact hv.trans hr.symm

/-- Construct the actual joined horn map from the original relative horn and boundary data. -/
theorem glue_all_horn {X : SSet.{u}} (k n : ℕ) (i : Fin (n + 2))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[n + 1, i].ι ≫ β) :
    ∃ Γ : ((prefixBoundary k (n + 1) ⊔ suffixHorn k (n + 1) i :
        (Δ[k + (n + 1) + 1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X,
      SSet.Subcomplex.homOfLE le_sup_left ≫ Γ = SSet.yonedaEquiv β ∧
      SSet.Subcomplex.homOfLE le_sup_right ≫ Γ = suffixHornMap k n i φ := by
  let A := prefixBoundary.{u} k (n + 1)
  let S := suffixHorn.{u} k (n + 1) i
  have sq : SSet.Subcomplex.BicartSq (A ⊓ S) A S (A ⊔ S) := ⟨rfl, rfl⟩
  let hc := boundary_suffix_overlap k n i φ β w
  exact ⟨sq.isPushout.desc (SSet.yonedaEquiv β) (suffixHornMap k n i φ) hc,
    sq.isPushout.inl_desc _ _ hc, sq.isPushout.inr_desc _ _ hc⟩

end

end DaggerOriginalJoinedBoundarySuffixGluing
