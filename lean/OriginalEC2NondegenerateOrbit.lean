import OriginalEC2NondegenerateSimplices

/-!
# The actual nondegenerate codiscrete-nerve simplices form at most one orbit

Two alternating `C2` vertex sequences with the same first vertex coincide.
The actual regular action moves one first vertex to another, so it acts
transitively on nondegenerate simplices in each dimension when they exist.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2NondegenerateSimplices

universe u

namespace DaggerOriginalEC2NondegenerateOrbit

noncomputable section

private theorem c2_cases (g : C2.{u}) : g = 1 ∨ g = generator := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz (Multiplicative.toAdd g.down) with h | h
  · left
    apply ULift.down_injective
    exact h
  · right
    apply ULift.down_injective
    exact h

private theorem c2_ne_unique (x y z : C2.{u})
    (hxy : x ≠ y) (hxz : x ≠ z) : y = z := by
  rcases c2_cases x with rfl | rfl
  · rcases c2_cases y with rfl | rfl
    · exact (hxy rfl).elim
    · rcases c2_cases z with rfl | rfl
      · exact (hxz rfl).elim
      · rfl
  · rcases c2_cases y with rfl | rfl
    · rcases c2_cases z with rfl | rfl
      · rfl
      · exact (hxz rfl).elim
    · exact (hxy rfl).elim

private theorem alternating_unique (n : ℕ)
    (a b : Fin (n + 1) → C2.{u})
    (hzero : a 0 = b 0)
    (ha : ∀ i : Fin n, a i.castSucc ≠ a i.succ)
    (hb : ∀ i : Fin n, b i.castSucc ≠ b i.succ) : a = b := by
  funext j
  induction j using Fin.induction with
  | zero => exact hzero
  | succ j ih =>
      have hb' : a j.castSucc ≠ b j.succ := by
        simpa only [ih] using hb j
      exact c2_ne_unique _ _ _ (ha j) hb'

/-- In every degree, the actual action multiplies every original vertex label. -/
theorem action_obj (g : C2.{u}) (n : ℕ)
    (s : ComposableArrows (Codiscrete C2.{u}) n) (j : Fin (n + 1)) :
    (((simplicialAction.{u}.ρ g).asHom).app (op ⦋n⦌) s).obj j =
      Codiscrete.mk (g * (s.obj j).as) := by
  change ((nerveMap (Codiscrete.functorOfFun
    (fun z : C2.{u} ↦ g * z))).app (op ⦋n⦌) s).obj j = _
  rfl

/-- Nondegenerate actual nerve simplices with the same first object coincide. -/
theorem nondegenerate_eq_of_first (n : ℕ)
    (s t : ComposableArrows (Codiscrete C2.{u}) n)
    (hs : s ∈ (simplicialEC2.{u}).nonDegenerate n)
    (ht : t ∈ (simplicialEC2.{u}).nonDegenerate n)
    (hfirst : s.obj 0 = t.obj 0) : s = t := by
  have hseq : (fun j : Fin (n + 1) ↦ (s.obj j).as) =
      (fun j : Fin (n + 1) ↦ (t.obj j).as) := by
    apply alternating_unique n
    · exact congrArg Codiscrete.as hfirst
    · exact (nondegenerate_iff_adjacent_labels n s).1 hs
    · exact (nondegenerate_iff_adjacent_labels n t).1 ht
  apply ComposableArrows.ext
  · intro j hj
    exact @Subsingleton.elim Unit inferInstance _ _
  · intro j
    apply Codiscrete.ext
    exact congrFun hseq j

/-- Any two actual nondegenerate simplices of one degree lie in one `C2` orbit. -/
theorem nondegenerate_orbit_transitive (n : ℕ)
    (s t : ComposableArrows (Codiscrete C2.{u}) n)
    (hs : s ∈ (simplicialEC2.{u}).nonDegenerate n)
    (ht : t ∈ (simplicialEC2.{u}).nonDegenerate n) :
    ∃ g : C2.{u},
      ((simplicialAction.{u}.ρ g).asHom).app (op ⦋n⦌) s = t := by
  let g : C2.{u} := (t.obj 0).as * ((s.obj 0).as)⁻¹
  let s' : ComposableArrows (Codiscrete C2.{u}) n :=
    ((simplicialAction.{u}.ρ g).asHom).app (op ⦋n⦌) s
  have hs' : s' ∈ (simplicialEC2.{u}).nonDegenerate n := by
    apply (nondegenerate_iff_adjacent_labels n s').2
    intro i heq
    have hmul : g * (s.obj i.castSucc).as =
        g * (s.obj i.succ).as := by
      simpa only [s', action_obj] using heq
    exact ((nondegenerate_iff_adjacent_labels n s).1 hs i)
      (mul_left_cancel hmul)
  have hfirst : s'.obj 0 = t.obj 0 := by
    change Codiscrete.mk (g * (s.obj 0).as) = t.obj 0
    apply Codiscrete.ext
    dsimp [g]
    simp
  exact ⟨g, nondegenerate_eq_of_first n s' t hs' ht hfirst⟩

end

end DaggerOriginalEC2NondegenerateOrbit
