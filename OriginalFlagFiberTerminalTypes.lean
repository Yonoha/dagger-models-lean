import OriginalFlagFiberTerminal

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification

noncomputable section

/-- The actual terminal center uses the supplied quotient class, in every universe. -/
example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (flagHom X a b).obj (op ⦋n⦌)),
    IsTerminal (fiberCenter X a b n t) := by
  intro X a b n t
  exact fiberCenterIsTerminal X a b n t

/-- The original class is retained, rather than an isomorphic or chosen other class. -/
example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (flagHom X a b).obj (op ⦋n⦌)),
    classOf X a b n (fiberCenter X a b n t).obj.obj = t := by
  intro X a b n t
  exact fiberCenter_class X a b n t

/-- Other objects of the SAME fiber have no additional nondegeneracy hypothesis. -/
example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (flagHom X a b).obj (op ⦋n⦌)) (p : FlankedFiber X a b n t),
    Nonempty (p ⟶ fiberCenter X a b n t) ∧
      ∀ f g : p ⟶ fiberCenter X a b n t, f = g := by
  intro X a b n t p
  exact ⟨flankedFiber_hom_nonempty X a b n t p (fiberCenter X a b n t)
      (fiberCenter_nondegenerate X a b n t),
    fun f g ↦ flankedFiber_hom_unique X a b n t p (fiberCenter X a b n t)
      (fiberCenter_nondegenerate X a b n t) f g⟩

end
