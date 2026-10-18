import NativeStandardSimplexContraction

/-! Restrict an actual full cylinder homotopy that remains in the original subcomplex. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Simplicial Opposite
universe u
namespace DaggerNativeSubcomplexHomotopyRestriction
noncomputable section

variable {X : SSet.{u}} (S : X.Subcomplex) {F G : X ⟶ X}
  (h : SSet.Homotopy F G)
  (hs : ∀ (d : SimplexCategoryᵒᵖ) (s : S.obj d) (t : (Δ[1] : SSet.{u}).obj d),
    h.h.app d (s.val, t) ∈ S.obj d)

def restrictedCylinder : (S : SSet.{u}) ⊗ Δ[1] ⟶ S where
  app d p := ⟨h.h.app d (p.1.val, p.2), hs d p.1 p.2⟩
  naturality d e α := by
    funext p
    apply Subtype.ext
    exact congrFun (h.h.naturality α) (p.1.val, p.2)

def restrictHomotopy {f g : (S : SSet.{u}) ⟶ S}
    (hf : f ≫ S.ι = S.ι ≫ F) (hg : g ≫ S.ι = S.ι ≫ G) :
    SSet.Homotopy f g :=
  SSet.Homotopy.mk (restrictedCylinder S h hs) (by
    apply NatTrans.ext
    funext d x
    apply Subtype.ext
    exact (congrFun (NatTrans.congr_app h.h₀ d) x.val).trans
      (congrFun (NatTrans.congr_app hf d) x).symm) (by
    apply NatTrans.ext
    funext d x
    apply Subtype.ext
    exact (congrFun (NatTrans.congr_app h.h₁ d) x.val).trans
      (congrFun (NatTrans.congr_app hg d) x).symm)

end
end DaggerNativeSubcomplexHomotopyRestriction
