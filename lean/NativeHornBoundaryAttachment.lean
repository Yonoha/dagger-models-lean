import NativeHornMissingFaceGeometry
import NativeSubcomplexAttachmentPushout

/-! The original sphere boundary is the actual pushout of a horn and its missing face. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial
open DaggerNativeHornMissingFaceGeometry DaggerNativeSubcomplexAttachmentPushout
universe u
namespace DaggerNativeHornBoundaryAttachment
noncomputable section

theorem subcomplex_eqToIso_hom_ι {X : SSet.{u}} (A B : X.Subcomplex) (h : A = B) :
    (eqToIso (congrArg SSet.Subcomplex.toSSet h)).hom ≫ B.ι = A.ι := by
  subst B
  rfl

def missingFaceBoundaryIso (n : ℕ) (i : Fin (n + 2)) :
    ((SSet.horn.{u} (n + 1) i).preimage (SSet.stdSimplex.δ i) : SSet.{u}) ≅
      (SSet.boundary n : SSet.{u}) :=
  eqToIso (congrArg SSet.Subcomplex.toSSet (missing_face_preimage_horn n i))

def boundaryToHorn (n : ℕ) (i : Fin (n + 2)) :
    (SSet.boundary n : SSet.{u}) ⟶ (SSet.horn (n + 1) i : SSet.{u}) :=
  (missingFaceBoundaryIso n i).inv ≫
    (SSet.horn (n + 1) i).fromPreimage (SSet.stdSimplex.δ i)

theorem boundary_horn_missing_face_isPushout (n : ℕ) (i : Fin (n + 2)) :
    IsPushout (boundaryToHorn.{u} n i) (SSet.boundary n).ι
      (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) (SSet.boundary.ι i) := by
  have hb : SSet.Subcomplex.range (SSet.stdSimplex.δ i : (Δ[n] : SSet.{u}) ⟶ _) ≤
      SSet.boundary (n + 1) := by
    rw [SSet.stdSimplex.range_δ]
    exact SSet.face_le_boundary i
  have hc : SSet.horn.{u} (n + 1) i ⊔ SSet.Subcomplex.range (SSet.stdSimplex.δ i) =
      SSet.boundary (n + 1) := by
    rw [SSet.stdSimplex.range_δ]
    exact horn_sup_missing_face (n + 1) i
  have hs := attachment_isPushout (SSet.horn (n + 1) i) (SSet.boundary (n + 1))
    (SSet.stdSimplex.δ i) (SSet.horn_le_boundary i) hb hc
  apply hs.of_iso (missingFaceBoundaryIso n i) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, boundaryToHorn, Iso.hom_inv_id_assoc]
  · simpa only [Iso.refl_hom, Category.comp_id, missingFaceBoundaryIso] using
      (subcomplex_eqToIso_hom_ι _ _ (missing_face_preimage_horn n i)).symm
  · rfl
  · rfl

end
end DaggerNativeHornBoundaryAttachment
