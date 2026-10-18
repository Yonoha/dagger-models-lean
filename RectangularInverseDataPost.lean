import RelativeInverseActualStage

/-! Extending a relative inverse along an actual original Arrow morphism. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeHoIsoTriangles DaggerNativeIhomHoObjects DaggerInverseTriangleCellFamily
open DaggerRectangularInverseWitnessData
universe u v w
namespace DaggerRectangularInverseDataPost
noncomputable section
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

variable {a b c : Arrow C} (p : a ⟶ b) (q : b ⟶ c) (e : Data R p)

def post : Data R (p ≫ q) where
  inv := e.inv ≫ R.map q.left
  left := DaggerNativeIsoTriangleCellTransport.cast
    (congrArg homObject (Category.assoc (R.map a.hom) e.inv (R.map q.left)))
    (congrArg homObject (R.map_comp p.left q.left).symm)
    (DaggerRectangularTrianglePrePost.post (R.map q.left)
      (R.map a.hom ≫ e.inv) (R.map p.left) e.left)
  right := DaggerNativeIsoTriangleCellTransport.cast
    (congrArg homObject (by
      show (e.inv ≫ R.map b.hom) ≫ R.map q.right =
        (e.inv ≫ R.map q.left) ≫ R.map c.hom
      rw [Category.assoc, ← DaggerRelativeArrowStageFacs.map_square R q, Category.assoc]))
    (congrArg homObject (R.map_comp p.right q.right).symm)
    (DaggerRectangularTrianglePrePost.post (R.map q.right)
      (e.inv ≫ R.map b.hom) (R.map p.right) e.right)

theorem inv_post : (post R p q e).inv = e.inv ≫ R.map q.left := rfl

theorem cell_left (r : Kind) :
    DaggerRawIsoTriangleCells.cell (post R p q e).left r =
      ((ihom (R.obj a.left)).map (R.map q.left)).app (op ⦋r.degree⦌)
        (DaggerRawIsoTriangleCells.cell e.left r) := by
  dsimp [post]
  rw [DaggerRawIsoTriangleCasts.cell_cast, DaggerRectangularTrianglePrePost.cell_post]

theorem cell_right (r : Kind) :
    DaggerRawIsoTriangleCells.cell (post R p q e).right r =
      ((ihom (R.obj a.right)).map (R.map q.right)).app (op ⦋r.degree⦌)
        (DaggerRawIsoTriangleCells.cell e.right r) := by
  dsimp [post]
  rw [DaggerRawIsoTriangleCasts.cell_cast, DaggerRectangularTrianglePrePost.cell_post]

end
end DaggerRectangularInverseDataPost
