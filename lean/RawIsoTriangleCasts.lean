import RawIsoTriangleCells
import NativeIsoTriangleCellTransport

/-! Changes of endpoint equality preserve every chosen raw cell in rectangular Homs. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeHoIsoTriangles DaggerInverseTriangleCellFamily
universe u
namespace DaggerRawIsoTriangleCasts

theorem cell_cast {X : SSet.{u}} {x y x' y' : SSet.hoFunctor.obj X}
    (hx : x = x') (hy : y = y') (d : IsoTriangles X x y) (k : Kind) :
    DaggerRawIsoTriangleCells.cell (DaggerNativeIsoTriangleCellTransport.cast hx hy d) k =
      DaggerRawIsoTriangleCells.cell d k := by
  cases hx
  cases hy
  rfl

end DaggerRawIsoTriangleCasts
