import InverseTriangleCellFamily
import NativeIsoTriangleMaps

/-! A uniform finite indexing of the original chosen cells in any simplicial set. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeHoIsoTriangles DaggerInverseTriangleCellFamily
universe u
namespace DaggerRawIsoTriangleCells

def cell {X : SSet.{u}} {x y : SSet.hoFunctor.obj X} (d : IsoTriangles X x y) (k : Kind) :
    X.obj (op ⦋k.degree⦌) :=
  match k with
  | .forward => d.forward.edge
  | .backward => d.backward.edge
  | .leftTriangle => d.leftTriangle.simplex
  | .rightTriangle => d.rightTriangle.simplex

theorem cell_map {X Y : SSet.{u}} (f : X ⟶ Y) {x y : SSet.hoFunctor.obj X}
    (d : IsoTriangles X x y) (k : Kind) :
    cell (DaggerNativeIsoTriangleMaps.map f d) k = f.app (op ⦋k.degree⦌) (cell d k) := by
  cases k <;> rfl

end DaggerRawIsoTriangleCells
