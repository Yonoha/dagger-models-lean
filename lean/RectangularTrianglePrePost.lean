import RectangularHomTriangleStageLift

/-! Actual pre/postcomposition transports every chosen rectangular triangle cell. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeHoIsoTriangles DaggerNativeIhomHoObjects
open DaggerNativeWalkingRetractionMappingEquivalence DaggerInverseTriangleCellFamily
open DaggerRawIsoTriangleCells
universe u
namespace DaggerRectangularTrianglePrePost
noncomputable section

def pre {A X Z : SSet.{u}} (a : A ⟶ X) (h k : X ⟶ Z)
    (d : IsoTriangles ((ihom X).obj Z) (homObject h) (homObject k)) :
    IsoTriangles ((ihom A).obj Z) (homObject (a ≫ h)) (homObject (a ≫ k)) :=
  DaggerNativeIsoTriangleCellTransport.cast (pre_obj a h) (pre_obj a k)
    (DaggerNativeIsoTriangleMaps.map ((MonoidalClosed.pre a).app Z) d)

def post {A Z T : SSet.{u}} (a : Z ⟶ T) (h k : A ⟶ Z)
    (d : IsoTriangles ((ihom A).obj Z) (homObject h) (homObject k)) :
    IsoTriangles ((ihom A).obj T) (homObject (h ≫ a)) (homObject (k ≫ a)) :=
  DaggerNativeIsoTriangleCellTransport.cast (post_obj h a) (post_obj k a)
    (DaggerNativeIsoTriangleMaps.map ((ihom A).map a) d)

theorem cell_pre {A X Z : SSet.{u}} (a : A ⟶ X) (h k : X ⟶ Z)
    (d : IsoTriangles ((ihom X).obj Z) (homObject h) (homObject k)) (r : Kind) :
    cell (pre a h k d) r = ((MonoidalClosed.pre a).app Z).app (op ⦋r.degree⦌) (cell d r) := by
  rw [pre, DaggerRawIsoTriangleCasts.cell_cast, DaggerRawIsoTriangleCells.cell_map]

theorem cell_post {A Z T : SSet.{u}} (a : Z ⟶ T) (h k : A ⟶ Z)
    (d : IsoTriangles ((ihom A).obj Z) (homObject h) (homObject k)) (r : Kind) :
    cell (post a h k d) r = ((ihom A).map a).app (op ⦋r.degree⦌) (cell d r) := by
  rw [post, DaggerRawIsoTriangleCasts.cell_cast, DaggerRawIsoTriangleCells.cell_map]

end
end DaggerRectangularTrianglePrePost
