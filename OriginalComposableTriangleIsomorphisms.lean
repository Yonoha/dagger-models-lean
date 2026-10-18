import OriginalOrdinaryCoreHornEdgeTransport

/-!
# Recover the missing arrow of an outer triangle by native iso cancellation

The long edge is the literal composite in a composable-arrow diagram. If it and
either short edge are isomorphisms, Mathlib's factorization cancellation proves
that both short edges are isomorphisms, hence every arrow is an isomorphism.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalComposableArrowsAdjacentIsomorphisms

universe v u

namespace DaggerOriginalComposableTriangleIsomorphisms

/-- A diagonal and either side determine invertibility of every arrow of a nerve triangle. -/
theorem all_arrows_iso_of_triangle_diagonal {C : Type u} [Category.{v} C]
    (s : ComposableArrows C 2)
    (hdiag : IsIso (s.map (homOfLE (show (0 : Fin 3) ≤ 2 by decide))))
    (hside : IsIso (s.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide))) ∨
      IsIso (s.map (homOfLE (show (1 : Fin 3) ≤ 2 by decide)))) :
    ∀ {a b : Fin 3} (f : a ⟶ b), IsIso (s.map f) := by
  have hcomp : s.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide)) ≫
      s.map (homOfLE (show (1 : Fin 3) ≤ 2 by decide)) =
        s.map (homOfLE (show (0 : Fin 3) ≤ 2 by decide)) := by
    rw [← s.map_comp]
    congr 1
  have h01 : IsIso (s.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide))) := by
    rcases hside with h | h
    · exact h
    · exact IsIso.of_isIso_fac_right hcomp
  have h12 : IsIso (s.map (homOfLE (show (1 : Fin 3) ≤ 2 by decide))) :=
    IsIso.of_isIso_fac_left hcomp
  apply all_arrows_iso_of_adjacent
  intro k
  fin_cases k
  · exact h01
  · exact h12

end DaggerOriginalComposableTriangleIsomorphisms
