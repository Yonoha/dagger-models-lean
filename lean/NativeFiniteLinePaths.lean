import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! The original finite ordinal is the free category on its successive-vertex arrows. -/
set_option autoImplicit false
open CategoryTheory Simplicial
universe u
namespace DaggerNativeFiniteLinePaths
noncomputable section

structure Vertex (n : ℕ) : Type u where
  index : Fin (n + 1)

instance vertexQuiver (n : ℕ) : Quiver.{u + 1} (Vertex.{u} n) where
  Hom x y := ULift.{u} (PLift (x.index.val + 1 = y.index.val))

instance homSubsingleton {n : ℕ} (x y : Vertex.{u} n) : Subsingleton (x ⟶ y) := by
  change Subsingleton (ULift (PLift _))
  infer_instance

variable {n : ℕ}

theorem vertex_ext {x y : Vertex.{u} n} (h : x.index = y.index) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem path_distance {x y : Vertex.{u} n} (p : Quiver.Path x y) :
    x.index.val + p.length = y.index.val := by
  induction p with
  | nil => rfl
  | @cons z y p e ih =>
      have he : z.index.val + 1 = y.index.val := e.down.down
      rw [Quiver.Path.length_cons]
      omega

theorem path_unique {x y : Vertex.{u} n} (p q : Quiver.Path x y) : p = q := by
  induction p with
  | nil =>
      cases q with
      | nil => rfl
      | @cons z x q e =>
          have hd := path_distance q
          have he : z.index.val + 1 = x.index.val := e.down.down
          exact False.elim (by omega)
  | @cons z y p e ih =>
      cases q with
      | nil =>
          have hd := path_distance p
          have he := e.down.down
          exact False.elim (by omega)
      | @cons z' y q e' =>
          have hz : z = z' := by
            apply vertex_ext
            apply Fin.ext
            have he : z.index.val + 1 = y.index.val := e.down.down
            have he' : z'.index.val + 1 = y.index.val := e'.down.down
            omega
          subst z'
          have hp := ih q
          subst q
          have he : e = e' := Subsingleton.elim _ _
          subst e'
          rfl

instance pathSubsingleton (x y : Vertex.{u} n) : Subsingleton (Quiver.Path x y) :=
  ⟨path_unique⟩

def pathOfLE (x y : Vertex.{u} n) (hxy : x.index ≤ y.index) : Quiver.Path x y := by
  classical
  by_cases h : x = y
  · subst y
    exact .nil
  · have hlt : x.index.val < y.index.val := by
      have hn : x.index.val ≠ y.index.val := fun he ↦ h (vertex_ext (Fin.ext he))
      change x.index.val ≤ y.index.val at hxy
      omega
    let z : Vertex.{u} n := ⟨⟨y.index.val - 1, by have hy := y.index.isLt; omega⟩⟩
    have hxz : x.index ≤ z.index := by change x.index.val ≤ y.index.val - 1; omega
    let e : z ⟶ y := ⟨⟨by change y.index.val - 1 + 1 = y.index.val; omega⟩⟩
    exact (pathOfLE x z hxz).cons e
termination_by y.index.val
decreasing_by
  omega

def toOrdinal (n : ℕ) : Paths (Vertex.{u} n) ⥤ ULift.{u} (Fin (n + 1)) where
  obj x := ⟨x.index⟩
  map {x y} p := homOfLE (by
    change x.index.val ≤ y.index.val
    have h := path_distance p
    omega)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def fromOrdinal (n : ℕ) : ULift.{u} (Fin (n + 1)) ⥤ Paths (Vertex.{u} n) where
  obj x := ⟨x.down⟩
  map {x y} f := by
    have h : x ≤ y := leOfHom f
    exact pathOfLE _ _ h
  map_id _ := path_unique _ _
  map_comp _ _ := path_unique _ _

theorem from_to (n : ℕ) : fromOrdinal.{u} n ⋙ toOrdinal n = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro x y f
  exact Subsingleton.elim _ _

theorem to_from (n : ℕ) : toOrdinal.{u} n ⋙ fromOrdinal n = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro x y f
  exact path_unique _ _

end
end DaggerNativeFiniteLinePaths
