import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
import TopCatModelCategory.SSet.Degenerate

-- #32201
universe u

open CategoryTheory Opposite Simplicial

namespace SSet

section

variable (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] (n : ℕ)

lemma nondegenerate_eq_bot_of_hasDimensionLT (hn : d ≤ n) : X.nonDegenerate n = ⊥ := by
  simp [nonDegenerate, X.degenerate_eq_top_of_hasDimensionLT d n hn]

lemma dim_lt_of_nondegenerate {n : ℕ} (x : X.nonDegenerate n) (d : ℕ)
    [X.HasDimensionLT d] : n < d := by
  by_contra!
  obtain ⟨x, hx⟩ := x
  simp [X.nondegenerate_eq_bot_of_hasDimensionLT d n this] at hx

lemma dim_le_of_nondegenerate {n : ℕ} (x : X.nonDegenerate n) (d : ℕ)
    [X.HasDimensionLE d] : n ≤ d :=
  Nat.le_of_lt_succ (X.dim_lt_of_nondegenerate x (d + 1))

end

namespace Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

end Subcomplex

lemma hasDimensionLT_iff_subcomplex_top (X : SSet.{u}) (d : ℕ) :
    X.HasDimensionLT d ↔ HasDimensionLT (⊤ : X.Subcomplex) d := by
  constructor
  · intro
    infer_instance
  · intro h
    simp only [hasDimensionLT_iff, Subcomplex.degenerate_eq_top_iff] at h
    simpa [hasDimensionLT_iff] using h

end SSet
