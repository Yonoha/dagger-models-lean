import OriginalSimplexCoslice

/-!
# The actual joined horn is a single native inner horn

Separate the vertices of [k+n+1] into the native left and right ordinal blocks.
The union of the faces omitting a left-block vertex and the faces omitting a
right-block vertex other than i is exactly the original horn with index k+1+i.
If i<n this index is inner. These are actual subcomplexes of the original
standard simplex, in arbitrary universe and all dimensions.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers

universe u

namespace DaggerOriginalJoinedHornGeometry

/-- The original vertex in the native left ordinal block. -/
def prefixIndex (k n : ℕ) (j : Fin (k + 1)) : Fin (k + n + 2) :=
  ⟨j.val, by have h := j.isLt; omega⟩

/-- The original vertex in the native right ordinal block. -/
def suffixIndex (k n : ℕ) (j : Fin (n + 1)) : Fin (k + n + 2) :=
  ⟨k + 1 + j.val, by have h := j.isLt; omega⟩

/-- The left-block vertex is precisely the native ordinal-sum inclusion. -/
theorem prefixIndex_eq_native (k n : ℕ) (j : Fin (k + 1)) :
    prefixIndex k n j = (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n⦌).toOrderHom j := by
  apply Fin.ext
  rw [AugmentedSimplexCategory.inl'_eval]
  rfl

/-- The right-block vertex is precisely the native ordinal-sum inclusion. -/
theorem suffixIndex_eq_native (k n : ℕ) (j : Fin (n + 1)) :
    suffixIndex k n j = (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋n⦌).toOrderHom j := by
  apply Fin.ext
  rw [AugmentedSimplexCategory.inr'_eval]
  rfl

/-- Left and right native block vertices are distinct. -/
theorem prefixIndex_ne_suffixIndex (k n : ℕ) (j : Fin (k + 1)) (i : Fin (n + 1)) :
    prefixIndex k n j ≠ suffixIndex k n i := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  change j.val = k + 1 + i.val at hv
  omega

/-- The right native block inclusion is injective. -/
theorem suffixIndex_injective (k n : ℕ) : Function.Injective (suffixIndex k n) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change k + 1 + i.val = k + 1 + j.val at hv
  omega

/-- The union of the actual faces omitting a left-block vertex. -/
def prefixBoundary (k n : ℕ) : (Δ[k + n + 1] : SSet.{u}).Subcomplex :=
  ⨆ j : Fin (k + 1), SSet.stdSimplex.face {prefixIndex k n j}ᶜ

/-- The union of the actual right-block faces, except the specified one. -/
def suffixHorn (k n : ℕ) (i : Fin (n + 1)) :
    (Δ[k + n + 1] : SSet.{u}).Subcomplex :=
  ⨆ j : ({i}ᶜ : Set (Fin (n + 1))), SSet.stdSimplex.face {suffixIndex k n j.val}ᶜ

/-- The actual joined boundary-and-horn domain is exactly the original horn. -/
theorem prefixBoundary_sup_suffixHorn (k n : ℕ) (i : Fin (n + 1)) :
    prefixBoundary.{u} k n ⊔ suffixHorn k n i = Λ[k + n + 1, suffixIndex k n i] := by
  apply le_antisymm
  · rw [sup_le_iff]
    constructor
    · rw [prefixBoundary, iSup_le_iff]
      intro j
      exact SSet.face_le_horn _ _ (prefixIndex_ne_suffixIndex k n j i)
    · rw [suffixHorn, iSup_le_iff]
      intro j
      apply SSet.face_le_horn
      intro hj
      have hi : j.val ≠ i := j.property
      exact hi (suffixIndex_injective k n hj)
  · rw [SSet.horn_eq_iSup, iSup_le_iff]
    rintro ⟨j, hj⟩
    change j ≠ suffixIndex k n i at hj
    by_cases hleft : j.val < k + 1
    · let a : Fin (k + 1) := ⟨j.val, hleft⟩
      have ha : prefixIndex k n a = j := Fin.ext rfl
      calc
        SSet.stdSimplex.face {j}ᶜ = SSet.stdSimplex.face {prefixIndex k n a}ᶜ := by rw [ha]
        _ ≤ prefixBoundary k n := le_iSup (fun a ↦
          SSet.stdSimplex.face {prefixIndex k n a}ᶜ) a
        _ ≤ prefixBoundary k n ⊔ suffixHorn k n i := le_sup_left
    · let a : Fin (n + 1) := ⟨j.val - (k + 1), by have h := j.isLt; omega⟩
      have ha : suffixIndex k n a = j := by
        apply Fin.ext
        change k + 1 + (j.val - (k + 1)) = j.val
        omega
      have hai : a ≠ i := by
        intro h
        apply hj
        rw [← ha, h]
      calc
        SSet.stdSimplex.face {j}ᶜ = SSet.stdSimplex.face {suffixIndex k n a}ᶜ := by rw [ha]
        _ ≤ suffixHorn k n i := le_iSup (fun a : ({i}ᶜ : Set (Fin (n + 1))) ↦
          SSet.stdSimplex.face {suffixIndex k n a.val}ᶜ) ⟨a, hai⟩
        _ ≤ prefixBoundary k n ⊔ suffixHorn k n i := le_sup_right

/-- Every nonfinal right-block horn index becomes a literal inner index after the native join. -/
theorem suffixIndex_inner (k n : ℕ) (i : Fin (n + 1)) (hi : i < Fin.last n) :
    0 < suffixIndex k n i ∧ suffixIndex k n i < Fin.last (k + n + 1) := by
  change i.val < n at hi
  change 0 < k + 1 + i.val ∧ k + 1 + i.val < k + n + 1
  omega

/-- Actual maps from the joined boundary-and-horn domain extend by the original inner condition. -/
theorem joined_leftHorn_filling (X : SSet.{u}) (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 1)) (hi : i < Fin.last n) :
    ∀ σ₀ : ((prefixBoundary k n ⊔ suffixHorn k n i :
      (Δ[k + n + 1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X,
      ∃ σ : (Δ[k + n + 1] : SSet.{u}) ⟶ X,
        σ₀ = (prefixBoundary k n ⊔ suffixHorn k n i).ι ≫ σ := by
  rw [prefixBoundary_sup_suffixHorn]
  intro σ₀
  have hinner := suffixIndex_inner k n i hi
  exact hX hinner.1 hinner.2 σ₀

end DaggerOriginalJoinedHornGeometry
