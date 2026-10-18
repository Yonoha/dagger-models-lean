import Mathlib.Combinatorics.Quiver.Covering

/-! Root heights and unique signed parents specify all actual cells of a tree collapse. -/
set_option autoImplicit false
universe u
namespace DaggerNativeRootedQuiverPairingData
noncomputable section

variable (W : Type u) [Quiver.{u + 1} W]

structure Data where
  root : W
  height : W → ℕ
  height_zero_iff (x : W) : height x = 0 ↔ x = root
  edge_height {x y : W} (e : x ⟶ y) : height y = height x + 1 ∨ height y + 1 = height x
  unique_parent (x : W) (hx : x ≠ root) :
    ∃! s : Quiver.Star (show Quiver.Symmetrify W from x), height s.1 + 1 = height x

namespace Data

variable {W} (D : Data W)

def Cell := {x : W // x ≠ D.root}

def parent (x : D.Cell) : Quiver.Star (show Quiver.Symmetrify W from x.val) :=
  (D.unique_parent x.val x.property).choose

theorem parent_height (x : D.Cell) : D.height (D.parent x).1 + 1 = D.height x.val :=
  (D.unique_parent x.val x.property).choose_spec.1

theorem parent_eq (x : D.Cell)
    (s : Quiver.Star (show Quiver.Symmetrify W from x.val))
    (hs : D.height s.1 + 1 = D.height x.val) : D.parent x = s :=
  ((D.unique_parent x.val x.property).choose_spec.2 s hs).symm

theorem parent_ne (x : D.Cell) : (D.parent x).1 ≠ x.val := by
  intro he
  have hh := D.parent_height x
  rw [he] at hh
  omega

theorem root_height : D.height D.root = 0 := (D.height_zero_iff D.root).mpr rfl

theorem edge_source_not_root {x y : W} (_e : x ⟶ y)
    (hh : D.height y + 1 = D.height x) : x ≠ D.root := by
  intro he
  rw [he, D.root_height] at hh
  omega

theorem edge_target_not_root {x y : W} (_e : x ⟶ y)
    (hh : D.height y = D.height x + 1) : y ≠ D.root := by
  intro he
  rw [he, D.root_height] at hh
  omega

end Data
end
end DaggerNativeRootedQuiverPairingData
