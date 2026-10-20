import RectangularInverseWitnessData
import RawIsoTriangleCells
import Mathlib.CategoryTheory.Functor.OfSequence

/-! Actual countable crossed inverses and all eight strict rectangular cell compatibilities. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerInverseTriangleCellFamily
open DaggerRectangularInverseWitnessData
universe u v w
namespace DaggerRelativeInverseLadderData
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u}) (D : ℕ ⥤ Arrow C)

abbrev step (n : ℕ) : D.obj n ⟶ D.obj (n + 1) := D.map (homOfLE (n.le_add_right 1))

structure Ladder where
  data : ∀ n, Data R (step D n)
  inverse_compatible : ∀ n, R.map (step D n).right ≫ (data (n + 1)).inv =
    (data n).inv ≫ R.map (step D (n + 1)).left
  left_compatible : ∀ n (r : Kind), Square (R.map (step D n).left)
    (R.map (step D (n + 1)).left) (DaggerRawIsoTriangleCells.cell (data n).left r)
    (DaggerRawIsoTriangleCells.cell (data (n + 1)).left r)
  right_compatible : ∀ n (r : Kind), Square (R.map (step D n).right)
    (R.map (step D (n + 1)).right) (DaggerRawIsoTriangleCells.cell (data n).right r)
    (DaggerRawIsoTriangleCells.cell (data (n + 1)).right r)

structure Over (e : Ladder R D) (c : Cocone D)
    (d : SimplexInverseData (R.map c.pt.hom)) : Prop where
  inverse_fac : ∀ n, (e.data n).inv ≫ R.map (c.ι.app (n + 1)).left =
    R.map (c.ι.app n).right ≫ d.inv
  left_fac : ∀ n (r : Kind), Square (R.map (c.ι.app n).left)
    (R.map (c.ι.app (n + 1)).left) (DaggerRawIsoTriangleCells.cell (e.data n).left r)
    (DaggerRawIsoTriangleCells.cell d.left r)
  right_fac : ∀ n (r : Kind), Square (R.map (c.ι.app n).right)
    (R.map (c.ι.app (n + 1)).right) (DaggerRawIsoTriangleCells.cell (e.data n).right r)
    (DaggerRawIsoTriangleCells.cell d.right r)

end DaggerRelativeInverseLadderData
