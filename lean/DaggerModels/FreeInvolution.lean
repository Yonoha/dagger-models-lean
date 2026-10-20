import Mathlib.Data.Quot
import Mathlib.Logic.Equiv.Defs

/-!
# Choosing representatives for a free involution

The quotient by `x = y ∨ x = τ y` indexes the two-element orbits. Choice
selects one representative in each orbit. Its representative and its image
under the involution give a bijection with the orbit quotient times `Bool`.
No ordering or additional hypothesis on the type is used.
-/

universe u

namespace DaggerModels.FreeInvolution

variable {N : Type u} (τ : N ≃ N) (hτ : Function.Involutive τ)

/-- The orbit equivalence relation of an involution, including the trivial orbits. -/
def orbitSetoid : Setoid N where
  r x y := x = y ∨ x = τ y
  iseqv :=
    { refl x := Or.inl rfl
      symm := by
        intro x y h
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr ((hτ y).symm.trans (congrArg τ h.symm))
      trans := by
        intro x y z hxy hyz
        rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
        · exact Or.inl (hxy.trans hyz)
        · exact Or.inr (hxy.trans hyz)
        · exact Or.inr (hxy.trans (congrArg τ hyz))
        · exact Or.inl (hxy.trans ((congrArg τ hyz).trans (hτ z))) }

/-- The type of involution orbits, in the same universe as the original type. -/
def Orbit := Quotient (orbitSetoid τ hτ)

/-- The quotient map to the orbit of an element. -/
def orbit (x : N) : Orbit τ hτ := Quotient.mk (orbitSetoid τ hτ) x

@[simp] theorem orbit_involution (x : N) : orbit τ hτ (τ x) = orbit τ hτ x :=
  Quotient.sound (Or.inr rfl)

/-- One chosen representative in each involution orbit. -/
noncomputable def representative (r : Orbit τ hτ) : N := r.out

@[simp] theorem orbit_representative (r : Orbit τ hτ) :
    orbit τ hτ (representative τ hτ r) = r := Quotient.out_eq r

/-- Every element is the chosen representative of its orbit or its conjugate. -/
theorem representative_cover (x : N) :
    x = representative τ hτ (orbit τ hτ x) ∨
      x = τ (representative τ hτ (orbit τ hτ x)) :=
  Quotient.exact (orbit_representative τ hτ (orbit τ hτ x)).symm

/-- Chosen representatives from the same orbit have the same orbit index. -/
theorem representative_separated {r s : Orbit τ hτ}
    (h : representative τ hτ r = representative τ hτ s ∨
      representative τ hτ r = τ (representative τ hτ s)) : r = s := by
  calc
    r = orbit τ hτ (representative τ hτ r) := (orbit_representative τ hτ r).symm
    _ = orbit τ hτ (representative τ hτ s) := Quotient.sound h
    _ = s := orbit_representative τ hτ s

/-- A representative is not the conjugate of any chosen representative when the action is free. -/
theorem representative_ne_involution (hfree : ∀ x, τ x ≠ x) (r s : Orbit τ hτ) :
    representative τ hτ r ≠ τ (representative τ hτ s) := by
  intro h
  obtain rfl := representative_separated τ hτ (Or.inr h)
  exact hfree (representative τ hτ r) h.symm

/-- The two copies of each orbit: `false` is the representative and `true` its conjugate. -/
noncomputable def assemble (p : Orbit τ hτ × Bool) : N :=
  if p.2 then τ (representative τ hτ p.1) else representative τ hτ p.1

@[simp] theorem assemble_false (r : Orbit τ hτ) :
    assemble τ hτ (r, false) = representative τ hτ r := rfl

@[simp] theorem assemble_true (r : Orbit τ hτ) :
    assemble τ hτ (r, true) = τ (representative τ hτ r) := rfl

@[simp] theorem orbit_assemble (p : Orbit τ hτ × Bool) :
    orbit τ hτ (assemble τ hτ p) = p.1 := by
  rcases p with ⟨r, b⟩
  cases b <;> simp

/-- Conjugation switches the two Bool-labelled elements of an orbit. -/
theorem assemble_flip (p : Orbit τ hτ × Bool) :
    assemble τ hτ (p.1, !p.2) = τ (assemble τ hτ p) := by
  rcases p with ⟨r, b⟩
  cases b
  · rfl
  · exact (hτ (representative τ hτ r)).symm

theorem assemble_bijective (hfree : ∀ x, τ x ≠ x) :
    Function.Bijective (assemble τ hτ) := by
  constructor
  · rintro ⟨r, b⟩ ⟨s, c⟩ h
    have hrs : r = s := (orbit_assemble τ hτ (r, b)).symm.trans
      ((congrArg (orbit τ hτ) h).trans (orbit_assemble τ hτ (s, c)))
    subst s
    cases b <;> cases c
    · rfl
    · exact False.elim (hfree (representative τ hτ r) h.symm)
    · exact False.elim (hfree (representative τ hτ r) h)
    · rfl
  · intro x
    rcases representative_cover τ hτ x with h | h
    · exact ⟨(orbit τ hτ x, false), h.symm⟩
    · exact ⟨(orbit τ hτ x, true), h.symm⟩

/-- A free involution is a Bool flip over its actual orbit quotient. -/
noncomputable def equiv (hfree : ∀ x, τ x ≠ x) : N ≃ Orbit τ hτ × Bool :=
  (Equiv.ofBijective (assemble τ hτ) (assemble_bijective τ hτ hfree)).symm

@[simp] theorem equiv_symm_apply (hfree : ∀ x, τ x ≠ x) (p : Orbit τ hτ × Bool) :
    (equiv τ hτ hfree).symm p = assemble τ hτ p := rfl

/-- The equivalence identifies the given involution with the Bool flip. -/
theorem equiv_involution (hfree : ∀ x, τ x ≠ x) (x : N) :
    equiv τ hτ hfree (τ x) =
      ((equiv τ hτ hfree x).1, !(equiv τ hτ hfree x).2) := by
  apply (equiv τ hτ hfree).symm.injective
  rw [Equiv.symm_apply_apply, equiv_symm_apply, assemble_flip]
  exact congrArg τ ((equiv τ hτ hfree).symm_apply_apply x).symm

include hτ in
/-- The explicit construction gives an equivariant two-element-orbit decomposition. -/
theorem exists_equivariant_equiv (hfree : ∀ x, τ x ≠ x) :
    ∃ (R : Type u) (e : N ≃ R × Bool), ∀ x, e (τ x) = ((e x).1, !(e x).2) :=
  ⟨Orbit τ hτ, equiv τ hτ hfree, equiv_involution τ hτ hfree⟩

end DaggerModels.FreeInvolution
