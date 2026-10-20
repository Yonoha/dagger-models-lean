import TopCatModelCategory.SSet.Contractible
import TopCatModelCategory.TopCat.Homotopy

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerOriginalIntervalChosenHom

noncomputable section

variable {X Y : SSet.{u}}

/-- SOURCE DRAFT: the supplied full iso transports the supplied contraction. -/
def contractibleOfIso (e : X ≅ Y) (c : SSet.Contractible X) : SSet.Contractible Y where
  pt := e.hom.app (op ⦋0⦌) c.pt
  h := ((c.h.precomp e.inv).postcomp e.hom).congr
    (by rw [Category.assoc, SSet.const_comp, SSet.comp_const])
    (by simp)

theorem contractibleOfIso_map (e : X ≅ Y) (c : SSet.Contractible X) :
    (contractibleOfIso e c).h.h = e.inv ▷ (Δ[1] : SSet.{u}) ≫ c.h.h ≫ e.hom := rfl

theorem contractibleOfIso_zero (e : X ≅ Y) (c : SSet.Contractible X) :
    SSet.ι₀ ≫ (contractibleOfIso e c).h.h =
      SSet.const (e.hom.app (op ⦋0⦌) c.pt) := (contractibleOfIso e c).h.h₀

theorem contractibleOfIso_one (e : X ≅ Y) (c : SSet.Contractible X) :
    SSet.ι₁ ≫ (contractibleOfIso e c).h.h = 𝟙 Y := (contractibleOfIso e c).h.h₁

theorem contractibleOfIso_operator (e : X ≅ Y) (c : SSet.Contractible X)
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (x : Y.obj q)
    (t : (Δ[1] : SSet.{u}).obj q) :
    Y.map α ((contractibleOfIso e c).h.h.app q (x, t)) =
      (contractibleOfIso e c).h.h.app r (Y.map α x, (Δ[1] : SSet.{u}).map α t) :=
  (congrFun ((contractibleOfIso e c).h.h.naturality α) (x, t)).symm

end

end DaggerOriginalIntervalChosenHom
