import OriginalFlagFlankFibers

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
variable (t : (flagHom X a b).obj (op ⦋n⦌))

/-- Literal property equality with the existing component; every original representative remains. -/
theorem fiberPredicate_eq_component :
    fiberPredicate X a b n t =
      ((componentEquiv X a b n).symm t).objectProperty := by
  funext p
  apply propext
  constructor
  · intro hp
    change ConnectedComponents.mk p = (componentEquiv X a b n).symm t
    apply (componentEquiv X a b n).injective
    rw [componentEquiv_mk, Equiv.apply_symm_apply]
    exact hp
  · intro hp
    change classOf X a b n p = t
    have h := congrArg (componentEquiv X a b n) hp
    simpa only [componentEquiv_mk, Equiv.apply_symm_apply] using h

instance fiber_isConnected : IsConnected (Fiber X a b n t) := by
  change IsConnected ((fiberPredicate X a b n t).FullSubcategory)
  rw [fiberPredicate_eq_component]
  infer_instance

theorem fiber_zigzag (p q : Fiber X a b n t) : Zigzag p q :=
  isPreconnected_zigzag p q

instance flankedFiber_nonempty : Nonempty (FlankedFiber X a b n t) := by
  obtain ⟨p⟩ := fiber_nonempty X a b n t
  exact ⟨(flankToFlankedFiber X a b n t).obj p⟩

/-- Only the actual flank functor and the two original recoding isos transport the finite path. -/
theorem flankedFiber_zigzag (p q : FlankedFiber X a b n t) : Zigzag p q := by
  have h : Zigzag ((forgetFlankedFiber X a b n t).obj p)
      ((forgetFlankedFiber X a b n t).obj q) :=
    fiber_zigzag X a b n t _ _
  have h' := zigzag_obj_of_zigzag (flankToFlankedFiber X a b n t) h
  exact (Zigzag.of_hom (recodingFiberIso X a b n t p).inv).trans
    (h'.trans (Zigzag.of_hom (recodingFiberIso X a b n t q).hom))

instance flankedFiber_isConnected : IsConnected (FlankedFiber X a b n t) :=
  zigzag_isConnected (flankedFiber_zigzag X a b n t)

end

end DaggerOriginalFlagFlankification
