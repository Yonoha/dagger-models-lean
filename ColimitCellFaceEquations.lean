import ColimitEndomorphismCellOperators

/-!
# Exact face equations and degenerate identity edges descend

All equations use the actual simplicial operators. The identities are the
original degenerate edges at the prescribed endomorphism vertices.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeEndomorphismCellSquares DaggerColimitEndomorphismCells
open DaggerEndomorphismCellOperators DaggerColimitEndomorphismCellOperators
universe u
namespace DaggerColimitCellFaceEquations
noncomputable section
variable {J : Type u} [SmallCategory J] {F : J ⥤ SSet.{u}} {c : Cocone F}

theorem descSimplex_map_eq {n m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : ∀ j, ((ihom (F.obj j)).obj (F.obj j)).obj (op ⦋n⦌))
    (hs : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (s i) (s j))
    (t : ∀ j, ((ihom (F.obj j)).obj (F.obj j)).obj (op ⦋m⦌))
    (ht : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (t i) (t j))
    (hc : IsColimit c) (h : ∀ j, ((ihom (F.obj j)).obj (F.obj j)).map α.op (s j) = t j) :
    ((ihom c.pt).obj c.pt).map α.op (descSimplex n s hs hc) = descSimplex m t ht hc :=
  (descSimplex_restrict α s hs hc).symm.trans
    (descSimplex_congr m (restrictFamily α s) t (restrictCompatible α s hs) ht hc h)

def idEdgeFamily (h : ∀ j, F.obj j ⟶ F.obj j) :
    ∀ j, ((ihom (F.obj j)).obj (F.obj j)).obj (op ⦋1⦌) :=
  restrictFamily (SimplexCategory.σ 0) (fun j ↦ vertex (h j))

theorem idEdgeCompatible (h : ∀ j, F.obj j ⟶ F.obj j)
    (hh : ∀ {i j} (f : i ⟶ j), h i ≫ F.map f = F.map f ≫ h j) :
    ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (idEdgeFamily h i) (idEdgeFamily h j) :=
  restrictCompatible (SimplexCategory.σ 0) (fun j ↦ vertex (h j)) (vertexCompatible h hh)

theorem descSimplex_idEdge (hc : IsColimit c) (h : ∀ j, F.obj j ⟶ F.obj j)
    (hh : ∀ {i j} (f : i ⟶ j), h i ≫ F.map f = F.map f ≫ h j)
    (H : c.pt ⟶ c.pt) (hH : ∀ j, h j ≫ c.ι.app j = c.ι.app j ≫ H) :
    descSimplex 1 (idEdgeFamily h) (idEdgeCompatible h hh) hc =
      SSet.Edge.edge (SSet.Edge.id (vertex H)) := by
  have hr : descSimplex 1 (idEdgeFamily h) (idEdgeCompatible h hh) hc =
      ((ihom c.pt).obj c.pt).map (SimplexCategory.σ 0).op
        (descSimplex 0 (fun j ↦ vertex (h j)) (vertexCompatible h hh) hc) :=
    descSimplex_restrict (SimplexCategory.σ 0) (fun j ↦ vertex (h j))
      (vertexCompatible h hh) hc
  rw [descSimplex_vertex hc h hh H hH] at hr
  exact hr

end
end DaggerColimitCellFaceEquations
