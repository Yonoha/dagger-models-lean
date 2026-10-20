import NativeEndomorphismConjugation
import NativeIsoTriangleCellTransport

/-! Exact transport of all chosen inverse triangles along an actual simplicial isomorphism. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeHoIsoTriangles DaggerNativeIhomHoObjects
open DaggerNativeEndomorphismConjugation DaggerNativeIsoTriangleCellTransport
open DaggerInverseTriangleCellFamily DaggerSimplexInverseWitnessCategory
universe u
namespace DaggerNativeInverseTriangleIsoTransport
noncomputable section

def transport {X Y : SSet.{u}} (e : X ≅ Y) (h k : X ⟶ X)
    (d : IsoTriangles ((ihom X).obj X) (homObject h) (homObject k)) :
    IsoTriangles ((ihom Y).obj Y) (homObject (e.inv ≫ h ≫ e.hom))
      (homObject (e.inv ≫ k ≫ e.hom)) :=
  cast (conjugation_obj e h) (conjugation_obj e k)
    (DaggerNativeIsoTriangleMaps.map (conjugation e) d)

theorem transport_cell {X Y : SSet.{u}} (e : X ≅ Y) (h k : X ⟶ X)
    (d : IsoTriangles ((ihom X).obj X) (homObject h) (homObject k)) (i : Kind) :
    cell (transport e h k d) i = (conjugation e).app (op ⦋i.degree⦌) (cell d i) := by
  rw [transport, cell_cast, cell_map]

theorem transport_square {X Y : SSet.{u}} (e : X ≅ Y) (h k : X ⟶ X)
    (d : IsoTriangles ((ihom X).obj X) (homObject h) (homObject k)) :
    TriangleSquare e.hom d (transport e h k d) := by
  apply (square_iff_all_cells _ _ _).2
  intro i
  rw [transport_cell]
  exact conjugation_square e i.degree (cell d i)

end
end DaggerNativeInverseTriangleIsoTransport
