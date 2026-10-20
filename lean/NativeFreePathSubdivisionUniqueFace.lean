import NativeFreePathFirstSubdivision
import NativeUniqueFaceNondegeneracy

/-! The exact subdivision pair has the unique native inner face needed by PairingCore. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeFreePathNerveWeight DaggerNativeFreePathNerveWeightOperators
open DaggerNativePathFirstSplit DaggerNativeFreePathFirstSubdivision
universe u
namespace DaggerNativeFreePathSubdivisionUniqueFace
noncomputable section

variable {V : Type u} [Quiver.{u + 1} V]

theorem first_length_delta_after_one {n : ℕ} (c : ComposableArrows (Paths V) (n + 2))
    (i : Fin (n + 3)) (hi : 1 < i) :
    ((show ComposableArrows (Paths V) (n + 1) from
      (nerve (Paths V)).δ i c).map' 0 1).length = (c.map' 0 1).length := by
  apply segment_length_congr c
  · change i.succAbove (0 : Fin (n + 2)) = 0
    have h : (0 : Fin (n + 2)).castSucc < i := by
      have h' : (0 : Fin (n + 3)) < i := by
        have hi' := hi
        simp only [Fin.lt_def, Fin.val_one, Fin.val_zero] at hi' ⊢
        omega
      simpa using h'
    simpa using Fin.succAbove_of_castSucc_lt i (0 : Fin (n + 2)) h
  · change i.succAbove (1 : Fin (n + 2)) = 1
    have h : (1 : Fin (n + 2)).castSucc < i := by simpa using hi
    simpa using Fin.succAbove_of_castSucc_lt i (1 : Fin (n + 2)) h

theorem delta_split_eq_iff {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) (hc : 1 < (c.map' 0 1).length)
    (i : Fin (n + 3)) : (nerve (Paths V)).δ i (splitSimplex c s) = c ↔ i = 1 := by
  constructor
  · intro h
    by_cases hi₀ : i = 0
    · subst i
      have hw := split_zero_weight_lt c s
      rw [h] at hw
      exact (lt_irrefl _ hw).elim
    by_cases hi₁ : i = 1
    · exact hi₁
    have h₀ : i.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hi₀
    have h₁ : i.val ≠ 1 := by simpa only [Fin.ext_iff, Fin.val_one] using hi₁
    have hi : (1 : Fin (n + 3)) < i := by
      simp only [Fin.lt_def, Fin.val_one]
      omega
    have hl := first_length_delta_after_one (splitSimplex c s) i hi
    rw [h, split_first_length] at hl
    exact (hc.ne' hl).elim
  · rintro rfl
    exact delta_one_split c s

theorem unique_inner_face {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) (hc : 1 < (c.map' 0 1).length) :
    SSet.IsUniquelyCodimOneFace (X := nerve (Paths V)) c (splitSimplex c s) :=
  .mk ⟨1, delta_one_split c s, fun i hi ↦ (delta_split_eq_iff c s hc i).mp hi⟩

theorem split_nonDegenerate {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) (hc : 1 < (c.map' 0 1).length)
    (hnd : c ∈ (nerve (Paths V)).nonDegenerate (n + 1)) :
    splitSimplex c s ∈ (nerve (Paths V)).nonDegenerate (n + 2) :=
  DaggerNativeUniqueFaceNondegeneracy.coface_nonDegenerate (X := nerve (Paths V))
    c _ hnd (unique_inner_face c s hc)

end
end DaggerNativeFreePathSubdivisionUniqueFace
