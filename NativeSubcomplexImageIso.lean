import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import NativeInnerHornFactorization

/-! Transport a full subcomplex inclusion along the SAME actual ambient isomorphism. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeInnerHornFactorization
universe u
namespace DaggerNativeSubcomplexImageIso
noncomputable section

variable {X Y : SSet.{u}} (e : X ≅ Y) (A : X.Subcomplex)

def imageIso : (A : SSet.{u}) ≅ (A.image e.hom : SSet.{u}) where
  hom := A.toImage e.hom
  inv :=
    { app := fun q s ↦ ⟨e.inv.app q s.val, by
        obtain ⟨t, ht, he⟩ := s.property
        have hv : e.inv.app q s.val = t := by
          rw [← he]
          exact congrFun (NatTrans.congr_app e.hom_inv_id q) t
        exact hv.symm ▸ ht⟩
      naturality := by
        intro q r α
        funext s
        apply Subtype.ext
        exact congrFun (e.inv.naturality α) s.val }
  hom_inv_id := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app e.hom_inv_id q) s.val
  inv_hom_id := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app e.inv_hom_id q) s.val

def inclusionArrowIso : Arrow.mk A.ι ≅ Arrow.mk (A.image e.hom).ι :=
  Arrow.isoMk (imageIso e A) e (SSet.Subcomplex.toImage_ι A e.hom)

theorem image_innerAnodyne (h : innerAnodyne A.ι) : innerAnodyne (A.image e.hom).ι := by
  have : innerAnodyne.{u}.RespectsIso := by unfold innerAnodyne; infer_instance
  exact (innerAnodyne.arrow_mk_iso_iff (inclusionArrowIso e A)).mp h

end
end DaggerNativeSubcomplexImageIso
