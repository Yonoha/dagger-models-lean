import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import Mathlib.GroupTheory.FreeGroup.Basic

/-! Native symmetric-quiver paths retain their full endpoint-aware edge data as signed words. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeSignedPathWords

variable (V : Type u) [Quiver.{u + 1} V]

def Edge := Σ a : V, Σ b : V, a ⟶ b

def signedEdgeEquiv :
    (Σ a : Quiver.Symmetrify V, Σ b : Quiver.Symmetrify V, a ⟶ b) ≃ Edge V × Bool where
  toFun
    | ⟨a, b, Sum.inl e⟩ => (⟨a, b, e⟩, true)
    | ⟨a, b, Sum.inr e⟩ => (⟨b, a, e⟩, false)
  invFun
    | (⟨a, b, e⟩, true) => ⟨a, b, Sum.inl e⟩
    | (⟨a, b, e⟩, false) => ⟨b, a, Sum.inr e⟩
  left_inv := by rintro ⟨a, b, e | e⟩ <;> rfl
  right_inv := by rintro ⟨⟨a, b, e⟩, b'⟩; cases b' <;> rfl

variable {V}

def letter {a b : Quiver.Symmetrify V} (e : a ⟶ b) : Edge V × Bool :=
  signedEdgeEquiv V ⟨a, b, e⟩

theorem letter_reverse {a b : Quiver.Symmetrify V} (e : a ⟶ b) :
    letter (Quiver.reverse e) = ((letter e).1, !(letter e).2) := by
  cases e <;> rfl

def word {a : Quiver.Symmetrify V} :
    ∀ {b : Quiver.Symmetrify V}, Quiver.Path a b → List (Edge V × Bool)
  | _, .nil => []
  | _, .cons p e => letter e :: word p

theorem word_length {a b : Quiver.Symmetrify V} (p : Quiver.Path a b) :
    (word p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => exact congrArg Nat.succ ih

theorem word_comp {a b c : Quiver.Symmetrify V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) : word (p.comp q) = word q ++ word p := by
  induction q with
  | nil => rfl
  | cons q e ih => simpa only [word, List.cons_append] using congrArg (List.cons (letter e)) ih

theorem letter_same_target {a a' b : Quiver.Symmetrify V} (e : a ⟶ b) (f : a' ⟶ b)
    (h : letter e = letter f) : a = a' ∧ HEq e f := by
  have hs := (signedEdgeEquiv V).injective h
  obtain ⟨ha, he⟩ := Sigma.mk.inj_iff.mp hs
  subst a'
  have ht : (⟨b, e⟩ : Σ c : Quiver.Symmetrify V, a ⟶ c) = ⟨b, f⟩ := eq_of_heq he
  exact ⟨rfl, (Sigma.mk.inj_iff.mp ht).2⟩

theorem word_injective {a b : Quiver.Symmetrify V} :
    Function.Injective (word : Quiver.Path a b → List (Edge V × Bool)) := by
  intro p
  induction p with
  | nil =>
    intro q hq
    cases q with
    | nil => rfl
    | cons q e => simp [word] at hq
  | @cons b c p e ih =>
    intro q hq
    cases q with
    | nil => simp [word] at hq
    | @cons b' _ q f =>
      obtain ⟨hl, hw⟩ := List.cons.inj hq
      obtain ⟨hb, he⟩ := letter_same_target e f hl
      subst b'
      have hef : e = f := eq_of_heq he
      subst f
      exact congrArg (fun r ↦ Quiver.Path.cons r e) (ih hw)

end DaggerNativeSignedPathWords
