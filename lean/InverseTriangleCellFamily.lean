import SimplexInverseWitnessCategory

/-! A fixed finite indexing of every chosen edge and cancellation triangle. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeHoIsoTriangles DaggerNativeEndomorphismCellSquares
open DaggerSimplexInverseWitnessCategory
universe u
namespace DaggerInverseTriangleCellFamily

inductive Kind where
  | forward | backward | leftTriangle | rightTriangle
  deriving DecidableEq, Fintype

def Kind.degree (k : Kind) : ℕ :=
  match k with
  | .forward => 1
  | .backward => 1
  | .leftTriangle => 2
  | .rightTriangle => 2

def cell {X : SSet.{u}} {x y : SSet.hoFunctor.obj ((ihom X).obj X)}
    (d : IsoTriangles ((ihom X).obj X) x y) (k : Kind) :
    ((ihom X).obj X).obj (op ⦋k.degree⦌) :=
  match k with
  | .forward => d.forward.edge
  | .backward => d.backward.edge
  | .leftTriangle => d.leftTriangle.simplex
  | .rightTriangle => d.rightTriangle.simplex

theorem square_iff_all_cells {X Y : SSet.{u}} (a : X ⟶ Y)
    {x₀ x₁ : SSet.hoFunctor.obj ((ihom X).obj X)}
    {y₀ y₁ : SSet.hoFunctor.obj ((ihom Y).obj Y)}
    (d : IsoTriangles ((ihom X).obj X) x₀ x₁)
    (e : IsoTriangles ((ihom Y).obj Y) y₀ y₁) :
    TriangleSquare a d e ↔ ∀ k, CellSquare a (cell d k) (cell e k) := by
  constructor
  · intro h k
    cases k
    · exact h.forward
    · exact h.backward
    · exact h.leftTriangle
    · exact h.rightTriangle
  · intro h
    exact ⟨h .forward, h .backward, h .leftTriangle, h .rightTriangle⟩

end DaggerInverseTriangleCellFamily
