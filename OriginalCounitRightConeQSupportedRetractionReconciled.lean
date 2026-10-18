import OriginalCounitRightConeQCommonBaseRetractionFactorReconciled

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalCounitRightConeQSupportedRetraction

noncomputable section

/-- A map with image in a split monomorphism is fixed by the associated
target idempotent. This uses the entire simplicial image, degreewise. -/
theorem supported_map_fixed_of_split {X Y T : SSet.{u}}
    (f : X ⟶ Y) (r : Y ⟶ X) (hfr : f ≫ r = 𝟙 X)
    (p : T ⟶ Y) (hp : SSet.Subcomplex.range p ≤ SSet.Subcomplex.range f) :
    (p ≫ r) ≫ f = p := by
  ext q x
  have hmem : p.app q x ∈ (SSet.Subcomplex.range p).obj q := ⟨x, rfl⟩
  have htarget := hp q hmem
  change ∃ y : X.obj q, f.app q y = p.app q x at htarget
  obtain ⟨y, hy⟩ := htarget
  change f.app q (r.app q (p.app q x)) = p.app q x
  rw [← hy]
  have hid := congrFun (NatTrans.congr_app hfr q) y
  change r.app q (f.app q y) = y at hid
  rw [hid]

end

end DaggerOriginalCounitRightConeQSupportedRetraction
