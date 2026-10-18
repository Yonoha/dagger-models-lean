import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card

/-!
SOURCE-ONLY CONSTRUCTOR DRAFT. The three GenRel first leaves are currently unavailable.
The full sorted admissibility, prescribed-collapse iff, and transport proofs remain pending.
This draft does not claim those missing statements from its helper's admissibility premise.
-/

open CategoryTheory Simplicial
universe u
namespace DaggerBisimplicialDiagonal

/-- The original finite subset, retained as its increasing list of natural values. -/
def positions {n : ℕ} (I : Finset (Fin n)) : List ℕ :=
  (I.image Fin.val).sort (· ≤ ·)

theorem positions_length {n : ℕ} (I : Finset (Fin n)) :
    (positions I).length = I.card := by
  rw [positions, Finset.length_sort, Finset.card_image_of_injective _ Fin.val_injective]

theorem positions_dimension {n : ℕ} (I : Finset (Fin n)) :
    n - I.card + (positions I).length = n := by
  rw [positions_length]
  exact Nat.sub_add_cancel (by simpa only [Fintype.card_fin] using I.card_le_univ)

/-- Exactly the already existing mapped standardσ, with the original dimensions. -/
def rho {n : ℕ} (I : Finset (Fin n)) : ⦋n⦌ ⟶ ⦋n - I.card⦌ :=
  SimplexCategoryGenRel.toSimplexCategory.map
    (SimplexCategoryGenRel.standardσ (positions I) (positions_dimension I))

theorem rho_eq_mapped_standardσ {n : ℕ} (I : Finset (Fin n)) :
    rho I = SimplexCategoryGenRel.toSimplexCategory.map
      (SimplexCategoryGenRel.standardσ (positions I) (positions_dimension I)) := rfl

/-- This is only an internal source helper; proving its hypothesis is a new finite duty. -/
theorem rho_eval_of_admissible {n : ℕ} (I : Finset (Fin n))
    (hL : SimplexCategoryGenRel.IsAdmissible (n - I.card) (positions I))
    (j : ℕ) (hj : j < n + 1) :
    (rho I).toOrderHom ⟨j, hj⟩ = SimplexCategoryGenRel.simplicialEvalσ (positions I) j := by
  exact SimplexCategoryGenRel.simplicialEvalσ_of_isAdmissible
    (positions I) n (n - I.card) hL (positions_dimension I) j hj

end DaggerBisimplicialDiagonal
