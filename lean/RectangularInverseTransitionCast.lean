import RectangularInverseDataPost

/-! Equality of the transition arrow changes none of the actual inverse or raw cells. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerRectangularInverseWitnessData DaggerInverseTriangleCellFamily
universe u v w
namespace DaggerRectangularInverseTransitionCast
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})
  {a b : Arrow C} {p q : a ⟶ b}

def cast (h : p = q) (e : Data R p) : Data R q := h ▸ e

theorem inv_cast (h : p = q) (e : Data R p) : (cast R h e).inv = e.inv := by
  cases h
  rfl

theorem cell_left (h : p = q) (e : Data R p) (r : Kind) :
    DaggerRawIsoTriangleCells.cell (cast R h e).left r =
      DaggerRawIsoTriangleCells.cell e.left r := by
  cases h
  rfl

theorem cell_right (h : p = q) (e : Data R p) (r : Kind) :
    DaggerRawIsoTriangleCells.cell (cast R h e).right r =
      DaggerRawIsoTriangleCells.cell e.right r := by
  cases h
  rfl

end DaggerRectangularInverseTransitionCast
