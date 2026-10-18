import ColimitEndomorphismCells
import EndomorphismCellOperators

/-!
# All faces, degeneracies, and prescribed endomorphism vertices descend exactly

Unique strict descent identifies the face or degeneracy of a colimit cell
with the descent of its actual componentwise faces or degeneracies.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeEndomorphismCellSquares DaggerColimitEndomorphismCells
open DaggerEndomorphismCellOperators
universe u
namespace DaggerColimitEndomorphismCellOperators
noncomputable section
variable {J : Type u} [SmallCategory J] {F : J ⥤ SSet.{u}} {c : Cocone F}

theorem descSimplex_congr (n : ℕ)
    (s t : ∀ j, ((ihom (F.obj j)).obj (F.obj j)).obj (op ⦋n⦌))
    (hs : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (s i) (s j))
    (ht : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (t i) (t j))
    (hc : IsColimit c) (h : ∀ j, s j = t j) :
    descSimplex n s hs hc = descSimplex n t ht hc := by
  have hst : s = t := funext h
  subst t
  rfl

def restrictFamily {n m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : ∀ j, ((ihom (F.obj j)).obj (F.obj j)).obj (op ⦋n⦌)) :
    ∀ j, ((ihom (F.obj j)).obj (F.obj j)).obj (op ⦋m⦌) :=
  fun j ↦ ((ihom (F.obj j)).obj (F.obj j)).map α.op (s j)

theorem restrictCompatible {n m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : ∀ j, ((ihom (F.obj j)).obj (F.obj j)).obj (op ⦋n⦌))
    (hs : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (s i) (s j)) :
    ∀ {i j} (f : i ⟶ j),
      CellSquare (F.map f) (restrictFamily α s i) (restrictFamily α s j) :=
  fun {_ _} f ↦ restrict_square α.op (hs f)

theorem descSimplex_restrict {n m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : ∀ j, ((ihom (F.obj j)).obj (F.obj j)).obj (op ⦋n⦌))
    (hs : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (s i) (s j)) (hc : IsColimit c) :
    descSimplex m (restrictFamily α s) (restrictCompatible α s hs) hc =
      ((ihom c.pt).obj c.pt).map α.op (descSimplex n s hs hc) := by
  apply descSimplex_unique
  intro j
  exact restrict_square α.op (descSimplex_square n s hs hc j)

theorem vertexCompatible (h : ∀ j, F.obj j ⟶ F.obj j)
    (hh : ∀ {i j} (f : i ⟶ j), h i ≫ F.map f = F.map f ≫ h j) :
    ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (vertex (h i)) (vertex (h j)) :=
  fun {_ _} f ↦ (vertex_square_iff _ _ _).2 (hh f)

theorem descSimplex_vertex (hc : IsColimit c) (h : ∀ j, F.obj j ⟶ F.obj j)
    (hh : ∀ {i j} (f : i ⟶ j), h i ≫ F.map f = F.map f ≫ h j)
    (H : c.pt ⟶ c.pt) (hH : ∀ j, h j ≫ c.ι.app j = c.ι.app j ≫ H) :
    descSimplex 0 (fun j ↦ vertex (h j)) (vertexCompatible h hh) hc = vertex H := by
  apply descSimplex_unique
  intro j
  exact (vertex_square_iff _ _ _).2 (hH j)

end
end DaggerColimitEndomorphismCellOperators
