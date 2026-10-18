import NativeHoIsoTriangles

/-! Functorial transport of the actual chosen edges and cancellation triangles. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeHoIsoTriangles
universe u
namespace DaggerNativeIsoTriangleMaps
noncomputable section

def map {X Y : SSet.{u}} (f : X ⟶ Y) {x y : SSet.hoFunctor.obj X}
    (d : IsoTriangles X x y) : IsoTriangles Y
      ((SSet.hoFunctor.map f).toFunctor.obj x) ((SSet.hoFunctor.map f).toFunctor.obj y) where
  forward := d.forward.map f
  backward := d.backward.map f
  leftTriangle := SSet.Edge.CompStruct.mk (d.leftTriangle.map f).simplex
    (d.leftTriangle.map f).d₂ (d.leftTriangle.map f).d₀
    (by simpa only [SSet.Edge.map_id] using (d.leftTriangle.map f).d₁)
  rightTriangle := SSet.Edge.CompStruct.mk (d.rightTriangle.map f).simplex
    (d.rightTriangle.map f).d₂ (d.rightTriangle.map f).d₀
    (by simpa only [SSet.Edge.map_id] using (d.rightTriangle.map f).d₁)

end
end DaggerNativeIsoTriangleMaps
