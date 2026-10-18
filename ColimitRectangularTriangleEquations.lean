import SourceColimitSimplexExt
import RawIsoTriangleCells

/-! Actual faces, vertices and degenerate identity edges are forced by source-colimit descent. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeIhomHoObjects DaggerNativeHoIsoTriangles DaggerInverseTriangleCellFamily
open DaggerRectangularInverseWitnessData DaggerRectangularCellOperators
universe u
namespace DaggerColimitRectangularTriangleEquations
variable {F : ℕ ⥤ SSet.{u}} {c : Cocone F}
  (h k : ∀ n, F.obj n ⟶ F.obj (n + 1))
  (d : ∀ n, IsoTriangles ((ihom (F.obj n)).obj (F.obj (n + 1)))
    (homObject (h n)) (homObject (k n)))
  (S : ∀ r : Kind, ((ihom c.pt).obj c.pt).obj (op ⦋r.degree⦌))
  (hS : ∀ n r, Square (c.ι.app n) (c.ι.app (n + 1))
    (DaggerRawIsoTriangleCells.cell (d n) r) (S r))

include hS

theorem face_eq (hc : IsColimit c) (r s : Kind) (α : ⦋s.degree⦌ ⟶ ⦋r.degree⦌)
    (hFace : ∀ n, ((ihom (F.obj n)).obj (F.obj (n + 1))).map α.op
      (DaggerRawIsoTriangleCells.cell (d n) r) = DaggerRawIsoTriangleCells.cell (d n) s) :
    ((ihom c.pt).obj c.pt).map α.op (S r) = S s := by
  apply DaggerSourceColimitSimplexExt.square_ext hc s.degree
    (fun n ↦ F.obj (n + 1)) (fun n ↦ c.ι.app (n + 1))
    (fun n ↦ DaggerRawIsoTriangleCells.cell (d n) s)
  · intro n
    have hh := restrict_square α (hS n r)
    rw [hFace n] at hh
    exact hh
  · exact fun n ↦ hS n s

theorem endpoint_eq (hc : IsColimit c) (r : Kind) (α : ⦋0⦌ ⟶ ⦋r.degree⦌)
    (f : ∀ n, F.obj n ⟶ F.obj (n + 1)) (H : c.pt ⟶ c.pt)
    (hFace : ∀ n, ((ihom (F.obj n)).obj (F.obj (n + 1))).map α.op
      (DaggerRawIsoTriangleCells.cell (d n) r) = vertex (f n))
    (hH : ∀ n, f n ≫ c.ι.app (n + 1) = c.ι.app n ≫ H) :
    ((ihom c.pt).obj c.pt).map α.op (S r) = vertex H := by
  apply DaggerSourceColimitSimplexExt.square_ext hc 0
    (fun n ↦ F.obj (n + 1)) (fun n ↦ c.ι.app (n + 1)) (fun n ↦ vertex (f n))
  · intro n
    have hh := restrict_square α (hS n r)
    rw [hFace n] at hh
    exact hh
  · intro n
    exact (vertex_square_iff _ _ _ _).2 (hH n)

theorem identity_face_eq (hc : IsColimit c) (r : Kind) (α : ⦋1⦌ ⟶ ⦋r.degree⦌)
    (f : ∀ n, F.obj n ⟶ F.obj (n + 1)) (H : c.pt ⟶ c.pt)
    (hFace : ∀ n, ((ihom (F.obj n)).obj (F.obj (n + 1))).map α.op
      (DaggerRawIsoTriangleCells.cell (d n) r) = (SSet.Edge.id (vertex (f n))).edge)
    (hH : ∀ n, f n ≫ c.ι.app (n + 1) = c.ι.app n ≫ H) :
    ((ihom c.pt).obj c.pt).map α.op (S r) = (SSet.Edge.id (vertex H)).edge := by
  apply DaggerSourceColimitSimplexExt.square_ext hc 1
    (fun n ↦ F.obj (n + 1)) (fun n ↦ c.ι.app (n + 1))
    (fun n ↦ (SSet.Edge.id (vertex (f n))).edge)
  · intro n
    have hh := restrict_square α (hS n r)
    rw [hFace n] at hh
    exact hh
  · intro n
    exact restrict_square (SimplexCategory.σ 0) ((vertex_square_iff _ _ _ _).2 (hH n))

end DaggerColimitRectangularTriangleEquations
