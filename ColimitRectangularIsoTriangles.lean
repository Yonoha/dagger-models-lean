import ColimitRectangularTriangleEquations

/-! The prescribed whole raw cells form actual global cancellation triangles. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeIhomHoObjects DaggerNativeHoIsoTriangles DaggerInverseTriangleCellFamily
open DaggerRectangularInverseWitnessData DaggerRectangularCellOperators
open DaggerColimitRectangularTriangleEquations
universe u
namespace DaggerColimitRectangularIsoTriangles
noncomputable section
variable {F : ℕ ⥤ SSet.{u}} {c : Cocone F}
  (h k : ∀ n, F.obj n ⟶ F.obj (n + 1))
  (d : ∀ n, IsoTriangles ((ihom (F.obj n)).obj (F.obj (n + 1)))
    (homObject (h n)) (homObject (k n)))
  (S : ∀ r : Kind, ((ihom c.pt).obj c.pt).obj (op ⦋r.degree⦌))
  (hS : ∀ n r, Square (c.ι.app n) (c.ι.app (n + 1))
    (DaggerRawIsoTriangleCells.cell (d n) r) (S r))

def colimitTriangles (hc : IsColimit c) (H K : c.pt ⟶ c.pt)
    (hH : ∀ n, h n ≫ c.ι.app (n + 1) = c.ι.app n ≫ H)
    (hK : ∀ n, k n ≫ c.ι.app (n + 1) = c.ι.app n ≫ K) :
    IsoTriangles ((ihom c.pt).obj c.pt) (homObject H) (homObject K) := by
  have f0 : ((ihom c.pt).obj c.pt).δ 1 (S .forward) = vertex H :=
    endpoint_eq h k d S hS hc .forward (SimplexCategory.δ (n := 0) 1) h H
      (fun n ↦ (d n).forward.src_eq) hH
  have f1 : ((ihom c.pt).obj c.pt).δ 0 (S .forward) = vertex K :=
    endpoint_eq h k d S hS hc .forward (SimplexCategory.δ (n := 0) 0) k K
      (fun n ↦ (d n).forward.tgt_eq) hK
  have b0 : ((ihom c.pt).obj c.pt).δ 1 (S .backward) = vertex K :=
    endpoint_eq h k d S hS hc .backward (SimplexCategory.δ (n := 0) 1) k K
      (fun n ↦ (d n).backward.src_eq) hK
  have b1 : ((ihom c.pt).obj c.pt).δ 0 (S .backward) = vertex H :=
    endpoint_eq h k d S hS hc .backward (SimplexCategory.δ (n := 0) 0) h H
      (fun n ↦ (d n).backward.tgt_eq) hH
  let ef := SSet.Edge.mk (S .forward) f0 f1
  let eb := SSet.Edge.mk (S .backward) b0 b1
  refine ⟨ef, eb, ?_, ?_⟩
  · refine SSet.Edge.CompStruct.mk (S .leftTriangle) ?_ ?_ ?_
    · exact face_eq h k d S hS hc .leftTriangle .forward (SimplexCategory.δ (n := 1) 2)
        (fun n ↦ (d n).leftTriangle.d₂)
    · exact face_eq h k d S hS hc .leftTriangle .backward (SimplexCategory.δ (n := 1) 0)
        (fun n ↦ (d n).leftTriangle.d₀)
    · exact identity_face_eq h k d S hS hc .leftTriangle (SimplexCategory.δ (n := 1) 1) h H
        (fun n ↦ (d n).leftTriangle.d₁) hH
  · refine SSet.Edge.CompStruct.mk (S .rightTriangle) ?_ ?_ ?_
    · exact face_eq h k d S hS hc .rightTriangle .backward (SimplexCategory.δ (n := 1) 2)
        (fun n ↦ (d n).rightTriangle.d₂)
    · exact face_eq h k d S hS hc .rightTriangle .forward (SimplexCategory.δ (n := 1) 0)
        (fun n ↦ (d n).rightTriangle.d₀)
    · exact identity_face_eq h k d S hS hc .rightTriangle (SimplexCategory.δ (n := 1) 1) k K
        (fun n ↦ (d n).rightTriangle.d₁) hK

theorem cell_colimitTriangles (hc : IsColimit c) (H K : c.pt ⟶ c.pt)
    (hH : ∀ n, h n ≫ c.ι.app (n + 1) = c.ι.app n ≫ H)
    (hK : ∀ n, k n ≫ c.ι.app (n + 1) = c.ι.app n ≫ K) (r : Kind) :
    DaggerRawIsoTriangleCells.cell (colimitTriangles h k d S hS hc H K hH hK) r = S r := by
  cases r <;> rfl

end
end DaggerColimitRectangularIsoTriangles
