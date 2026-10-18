import ColimitCellFaceEquations
import SimplexInverseWitnessCategory

/-!
# Whole actual inverse triangles descend along the original colimit cocone

All four raw simplices descend. Their faces and the degenerate identity edges
are the exact original faces and identities, with prescribed colimit vertices.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeIhomHoObjects DaggerNativeHoIsoTriangles
open DaggerNativeEndomorphismCellSquares DaggerEndomorphismCellOperators
open DaggerColimitEndomorphismCells DaggerColimitEndomorphismCellOperators
open DaggerColimitCellFaceEquations DaggerSimplexInverseWitnessCategory
universe u
namespace DaggerColimitEndomorphismIsoTriangles
noncomputable section
variable {J : Type u} [SmallCategory J] {F : J ⥤ SSet.{u}} {c : Cocone F}
  (h k : ∀ j, F.obj j ⟶ F.obj j)
  (d : ∀ j, IsoTriangles ((ihom (F.obj j)).obj (F.obj j))
    (homObject (h j)) (homObject (k j)))
  (hd : ∀ {i j} (f : i ⟶ j), TriangleSquare (F.map f) (d i) (d j))

include d hd

theorem sourceCompatible : ∀ {i j} (f : i ⟶ j), h i ≫ F.map f = F.map f ≫ h j := by
  intro i j f
  have h0 : CellSquare (F.map f)
      (((ihom (F.obj i)).obj (F.obj i)).δ 1 (d i).forward.edge)
      (((ihom (F.obj j)).obj (F.obj j)).δ 1 (d j).forward.edge) :=
    restrict_square (SimplexCategory.δ (n := 0) 1).op (hd f).forward
  rw [(d i).forward.src_eq, (d j).forward.src_eq] at h0
  exact (vertex_square_iff _ _ _).1 h0

theorem targetCompatible : ∀ {i j} (f : i ⟶ j), k i ≫ F.map f = F.map f ≫ k j := by
  intro i j f
  have h0 : CellSquare (F.map f)
      (((ihom (F.obj i)).obj (F.obj i)).δ 0 (d i).forward.edge)
      (((ihom (F.obj j)).obj (F.obj j)).δ 0 (d j).forward.edge) :=
    restrict_square (SimplexCategory.δ (n := 0) 0).op (hd f).forward
  rw [(d i).forward.tgt_eq, (d j).forward.tgt_eq] at h0
  exact (vertex_square_iff _ _ _).1 h0

def colimitTriangles (hc : IsColimit c) (H K : c.pt ⟶ c.pt)
    (hH : ∀ j, h j ≫ c.ι.app j = c.ι.app j ≫ H)
    (hK : ∀ j, k j ≫ c.ι.app j = c.ι.app j ≫ K) :
    IsoTriangles ((ihom c.pt).obj c.pt) (homObject H) (homObject K) := by
  let sf := fun j ↦ (d j).forward.edge
  let sb := fun j ↦ (d j).backward.edge
  let sl := fun j ↦ (d j).leftTriangle.simplex
  let sr := fun j ↦ (d j).rightTriangle.simplex
  have hf : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (sf i) (sf j) :=
    fun {_ _} f ↦ (hd f).forward
  have hb : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (sb i) (sb j) :=
    fun {_ _} f ↦ (hd f).backward
  have hl : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (sl i) (sl j) :=
    fun {_ _} f ↦ (hd f).leftTriangle
  have hr : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (sr i) (sr j) :=
    fun {_ _} f ↦ (hd f).rightTriangle
  have hh : ∀ {i j} (f : i ⟶ j), h i ≫ F.map f = F.map f ≫ h j :=
    sourceCompatible h k d hd
  have hk : ∀ {i j} (f : i ⟶ j), k i ≫ F.map f = F.map f ≫ k j :=
    targetCompatible h k d hd
  let f := descSimplex 1 sf hf hc
  let b := descSimplex 1 sb hb hc
  have f0 : ((ihom c.pt).obj c.pt).δ 1 f = vertex H :=
    (descSimplex_map_eq (SimplexCategory.δ (n := 0) 1) sf hf
      (fun j ↦ vertex (h j)) (vertexCompatible h hh) hc
      (fun j ↦ (d j).forward.src_eq)).trans (descSimplex_vertex hc h hh H hH)
  have f1 : ((ihom c.pt).obj c.pt).δ 0 f = vertex K :=
    (descSimplex_map_eq (SimplexCategory.δ (n := 0) 0) sf hf
      (fun j ↦ vertex (k j)) (vertexCompatible k hk) hc
      (fun j ↦ (d j).forward.tgt_eq)).trans (descSimplex_vertex hc k hk K hK)
  have b0 : ((ihom c.pt).obj c.pt).δ 1 b = vertex K :=
    (descSimplex_map_eq (SimplexCategory.δ (n := 0) 1) sb hb
      (fun j ↦ vertex (k j)) (vertexCompatible k hk) hc
      (fun j ↦ (d j).backward.src_eq)).trans (descSimplex_vertex hc k hk K hK)
  have b1 : ((ihom c.pt).obj c.pt).δ 0 b = vertex H :=
    (descSimplex_map_eq (SimplexCategory.δ (n := 0) 0) sb hb
      (fun j ↦ vertex (h j)) (vertexCompatible h hh) hc
      (fun j ↦ (d j).backward.tgt_eq)).trans (descSimplex_vertex hc h hh H hH)
  let ef : SSet.Edge (vertex H) (vertex K) := SSet.Edge.mk f f0 f1
  let eb : SSet.Edge (vertex K) (vertex H) := SSet.Edge.mk b b0 b1
  refine ⟨ef, eb, ?_, ?_⟩
  · refine SSet.Edge.CompStruct.mk (descSimplex 2 sl hl hc) ?_ ?_ ?_
    · exact descSimplex_map_eq (SimplexCategory.δ (n := 1) 2) sl hl sf hf hc
        (fun j ↦ (d j).leftTriangle.d₂)
    · exact descSimplex_map_eq (SimplexCategory.δ (n := 1) 0) sl hl sb hb hc
        (fun j ↦ (d j).leftTriangle.d₀)
    · exact (descSimplex_map_eq (SimplexCategory.δ (n := 1) 1) sl hl
        (idEdgeFamily h) (idEdgeCompatible h hh) hc
        (fun j ↦ (d j).leftTriangle.d₁)).trans (descSimplex_idEdge hc h hh H hH)
  · refine SSet.Edge.CompStruct.mk (descSimplex 2 sr hr hc) ?_ ?_ ?_
    · exact descSimplex_map_eq (SimplexCategory.δ (n := 1) 2) sr hr sb hb hc
        (fun j ↦ (d j).rightTriangle.d₂)
    · exact descSimplex_map_eq (SimplexCategory.δ (n := 1) 0) sr hr sf hf hc
        (fun j ↦ (d j).rightTriangle.d₀)
    · exact (descSimplex_map_eq (SimplexCategory.δ (n := 1) 1) sr hr
        (idEdgeFamily k) (idEdgeCompatible k hk) hc
        (fun j ↦ (d j).rightTriangle.d₁)).trans (descSimplex_idEdge hc k hk K hK)

theorem colimitTriangles_leg_square (hc : IsColimit c) (H K : c.pt ⟶ c.pt)
    (hH : ∀ j, h j ≫ c.ι.app j = c.ι.app j ≫ H)
    (hK : ∀ j, k j ≫ c.ι.app j = c.ι.app j ≫ K) (j : J) :
    TriangleSquare (c.ι.app j) (d j) (colimitTriangles h k d hd hc H K hH hK) :=
  ⟨descSimplex_square 1 (fun i ↦ (d i).forward.edge) (fun {_ _} f ↦ (hd f).forward) hc j,
    descSimplex_square 1 (fun i ↦ (d i).backward.edge) (fun {_ _} f ↦ (hd f).backward) hc j,
    descSimplex_square 2 (fun i ↦ (d i).leftTriangle.simplex)
      (fun {_ _} f ↦ (hd f).leftTriangle) hc j,
    descSimplex_square 2 (fun i ↦ (d i).rightTriangle.simplex)
      (fun {_ _} f ↦ (hd f).rightTriangle) hc j⟩

theorem colimitTriangles_target_square (hc : IsColimit c) (H K : c.pt ⟶ c.pt)
    (hH : ∀ j, h j ≫ c.ι.app j = c.ι.app j ≫ H)
    (hK : ∀ j, k j ≫ c.ι.app j = c.ι.app j ≫ K)
    {Z : SSet.{u}} (a : c.pt ⟶ Z)
    {z₀ z₁ : SSet.hoFunctor.obj ((ihom Z).obj Z)}
    (e : IsoTriangles ((ihom Z).obj Z) z₀ z₁)
    (ha : ∀ j, TriangleSquare (c.ι.app j ≫ a) (d j) e) :
    TriangleSquare a (colimitTriangles h k d hd hc H K hH hK) e :=
  ⟨descSimplex_target_square 1 (fun i ↦ (d i).forward.edge)
      (fun {_ _} f ↦ (hd f).forward) hc a e.forward.edge (fun i ↦ (ha i).forward),
    descSimplex_target_square 1 (fun i ↦ (d i).backward.edge)
      (fun {_ _} f ↦ (hd f).backward) hc a e.backward.edge (fun i ↦ (ha i).backward),
    descSimplex_target_square 2 (fun i ↦ (d i).leftTriangle.simplex)
      (fun {_ _} f ↦ (hd f).leftTriangle) hc a e.leftTriangle.simplex
      (fun i ↦ (ha i).leftTriangle),
    descSimplex_target_square 2 (fun i ↦ (d i).rightTriangle.simplex)
      (fun {_ _} f ↦ (hd f).rightTriangle) hc a e.rightTriangle.simplex
      (fun i ↦ (ha i).rightTriangle)⟩

end
end DaggerColimitEndomorphismIsoTriangles
