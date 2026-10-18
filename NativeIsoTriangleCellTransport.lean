import NativeIsoTriangleMaps
import InverseTriangleCellFamily

/-! Endpoint equality and actual mapping preserve the entire chosen simplex data. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeHoIsoTriangles DaggerInverseTriangleCellFamily
universe u
namespace DaggerNativeIsoTriangleCellTransport

def cast {X : SSet.{u}} {x y x' y' : SSet.hoFunctor.obj X}
    (hx : x = x') (hy : y = y') (d : IsoTriangles X x y) : IsoTriangles X x' y' :=
  hx ▸ hy ▸ d

theorem cell_cast {X : SSet.{u}} {x y x' y' : SSet.hoFunctor.obj ((ihom X).obj X)}
    (hx : x = x') (hy : y = y') (d : IsoTriangles ((ihom X).obj X) x y) (k : Kind) :
    cell (cast hx hy d) k = cell d k := by
  cases hx
  cases hy
  rfl

theorem cell_map {X Y : SSet.{u}} (f : (ihom X).obj X ⟶ (ihom Y).obj Y)
    {x y : SSet.hoFunctor.obj ((ihom X).obj X)}
    (d : IsoTriangles ((ihom X).obj X) x y) (k : Kind) :
    cell (DaggerNativeIsoTriangleMaps.map f d) k = f.app (op ⦋k.degree⦌) (cell d k) := by
  cases k <;> rfl

end DaggerNativeIsoTriangleCellTransport
