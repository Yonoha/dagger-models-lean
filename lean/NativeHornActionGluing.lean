import NativeHornBoundaryAttachment
import NativeIhomPushoutPullback
import TopCatModelCategory.SSet.FundamentalGroupoidAction

/-! An existing native action simplex extends over the actual whole boundary sphere. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial
open SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativeHornBoundaryAttachment DaggerNativeIhomPushoutPullback
universe u
namespace DaggerNativeHornActionGluing
noncomputable section

variable {n : ℕ} (i : Fin (n + 2)) {X : SSet.{u}} {x y : X _⦋0⦌}
  {p : Edge (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk y)}
  {f : X.PtSimplex n x} {g : X.PtSimplex n y}

theorem glue_condition (h : ActionStruct p f g) :
    (boundaryToHorn n i ▷ Δ[1]) ≫ snd _ _ ≫ p.map =
      ((SSet.boundary n).ι ▷ Δ[1]) ≫ h.map := by
  rw [whiskerRight_snd_assoc, h.whiskerRight_ι_comp_map]

def gluedMap (h : ActionStruct p f g) :
    (SSet.boundary (n + 1) : SSet.{u}) ⊗ Δ[1] ⟶ X :=
  PushoutCocone.IsColimit.desc
    (tensorPushout (boundary_horn_missing_face_isPushout n i) Δ[1]).isColimit
    (snd _ _ ≫ p.map) h.map (glue_condition i h)

theorem gluedMap_horn (h : ActionStruct p f g) :
    (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i) ▷ Δ[1]) ≫ gluedMap i h =
      snd _ _ ≫ p.map :=
  PushoutCocone.IsColimit.inl_desc
    (tensorPushout (boundary_horn_missing_face_isPushout n i) Δ[1]).isColimit _ _ _

theorem gluedMap_face (h : ActionStruct p f g) :
    (SSet.boundary.ι i ▷ Δ[1]) ≫ gluedMap i h = h.map :=
  PushoutCocone.IsColimit.inr_desc
    (tensorPushout (boundary_horn_missing_face_isPushout n i) Δ[1]).isColimit _ _ _

def gluedHomotopy (h : ActionStruct p f g)
    (s t : (SSet.boundary (n + 1) : SSet.{u}) ⟶ X)
    (hsH : SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i) ≫ s = SSet.const x)
    (hsF : SSet.boundary.ι i ≫ s = f.map)
    (htH : SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i) ≫ t = SSet.const y)
    (htF : SSet.boundary.ι i ≫ t = g.map) : SSet.Homotopy s t :=
  SSet.Homotopy.mk (gluedMap i h) (by
    apply (boundary_horn_missing_face_isPushout n i).hom_ext
    · rw [← SSet.ι₀_comp_assoc, gluedMap_horn, SSet.ι₀_snd_assoc, SSet.const_comp,
        p.comm₀', hsH]
    · rw [← SSet.ι₀_comp_assoc, gluedMap_face, h.ι₀_map, hsF]) (by
    apply (boundary_horn_missing_face_isPushout n i).hom_ext
    · rw [← SSet.ι₁_comp_assoc, gluedMap_horn, SSet.ι₁_snd_assoc, SSet.const_comp,
        p.comm₁', htH]
    · rw [← SSet.ι₁_comp_assoc, gluedMap_face, h.ι₁_map, htF])

end
end DaggerNativeHornActionGluing
