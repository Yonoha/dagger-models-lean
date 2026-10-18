import Mathlib.CategoryTheory.Action.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases

/-! The actual two-element group action associated to an ordinary involution.
The underlying object, arrow and nonidentity action remain the given data.
-/

open CategoryTheory

universe v u

namespace DaggerFixedGraph

abbrev C2 := Multiplicative (ZMod 2)

def flip : C2 := Multiplicative.ofAdd (1 : ZMod 2)

@[simp] theorem flip_ne_one : flip ≠ (1 : C2) := by decide

@[simp] theorem flip_mul_flip : flip * flip = (1 : C2) := by decide

theorem c2_cases (g : C2) : g = 1 ∨ g = flip := by
  change Fin 2 at g
  fin_cases g <;> decide

variable {C : Type u} [Category.{v} C]

def involutionAction (X : C) (σ : X ⟶ X) (hσ : σ ≫ σ = 𝟙 X) : Action C C2 where
  V := X
  ρ :=
    { toFun := fun g ↦ if g = 1 then 𝟙 X else σ
      map_one' := by simp
      map_mul' := fun g h ↦ by
        rcases c2_cases g with rfl | rfl <;> rcases c2_cases h with rfl | rfl
        all_goals simp [flip_mul_flip, hσ, End.mul_def] }

@[simp] theorem involutionAction_one (X : C) (σ : X ⟶ X) (hσ) :
    (involutionAction X σ hσ).ρ 1 = 𝟙 X := by simp [involutionAction]

@[simp] theorem involutionAction_flip (X : C) (σ : X ⟶ X) (hσ) :
    (involutionAction X σ hσ).ρ flip = σ := by simp [involutionAction]

theorem action_flip_involutive (A : Action C C2) :
    A.ρ flip ≫ A.ρ flip = 𝟙 A.V := by
  have h := A.ρ.map_mul flip flip
  simpa only [flip_mul_flip, map_one, End.mul_def] using h.symm

def involutionActionMap {X Y : C} (σ : X ⟶ X) (τ : Y ⟶ Y)
    (hσ : σ ≫ σ = 𝟙 X) (hτ : τ ≫ τ = 𝟙 Y) (f : X ⟶ Y)
    (hf : σ ≫ f = f ≫ τ) : involutionAction X σ hσ ⟶ involutionAction Y τ hτ where
  hom := f
  comm g := by
    rcases c2_cases g with rfl | rfl
    · change 𝟙 X ≫ f = f ≫ 𝟙 Y
      exact (Category.id_comp f).trans (Category.comp_id f).symm
    · change σ ≫ f = f ≫ τ
      exact hf

def actionReconstructionIso (A : Action C C2) :
    involutionAction A.V (A.ρ flip) (action_flip_involutive A) ≅ A :=
  Action.mkIso (Iso.refl _) (fun g ↦ by
    rcases c2_cases g with rfl | rfl
    · change 𝟙 A.V ≫ 𝟙 A.V = 𝟙 A.V ≫ A.ρ 1
      rw [A.ρ.map_one]
      rfl
    · change A.ρ flip ≫ 𝟙 A.V = 𝟙 A.V ≫ A.ρ flip
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end DaggerFixedGraph
