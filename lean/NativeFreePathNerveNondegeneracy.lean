import NativeNerveTailDegeneracy
import NativeFreePathNerveWeight

/-! Native free-path nerve degeneracy is detected recursively by zero-length arrows. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeNerveFrontDegeneracy DaggerNativeNerveTailDegeneracy
universe u
namespace DaggerNativeFreePathNerveNondegeneracy

variable {V : Type u} [Quiver.{u + 1} V]

theorem precomp_degenerate_iff {n : ℕ} (c : ComposableArrows (Paths V) n)
    {X : Paths V} (f : X ⟶ c.left) :
    c.precomp f ∈ (nerve (Paths V)).degenerate (n + 1) ↔
      f.length = 0 ∨ c ∈ (nerve (Paths V)).degenerate n := by
  constructor
  · intro hc
    rw [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion] at hc
    obtain ⟨i, z, hz⟩ := hc
    cases i using Fin.cases with
    | zero =>
      left
      rw [sigma_zero] at hz
      have hl := congrArg (fun d : ComposableArrows (Paths V) (n + 1) ↦
        (d.map' 0 1).length) hz
      exact hl.symm
    | succ i =>
      right
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
        have hd := congrArg (fun d : ComposableArrows (Paths V) (n + 2) ↦ d.δ₀) hz
        have hs := SSet.δ_comp_σ_of_le_apply (S := nerve (Paths V))
          (i := (0 : Fin (n + 2))) (j := i) (Fin.zero_le _) z
        simp only [Fin.castSucc_zero, nerve.δ₀_eq] at hs
        simp only [ComposableArrows.precomp_δ₀] at hd
        rw [hs] at hd
        rw [← hd]
        exact SSet.σ_mem_degenerate _ _ _
  · rintro (hf | hc)
    · cases f with
      | nil =>
        change c.precomp (𝟙 c.left) ∈ (nerve (Paths V)).degenerate (n + 1)
        rw [← sigma_zero]
        exact SSet.σ_mem_degenerate _ _ _
      | cons p e => simp at hf
    · exact precomp_degenerate_of_tail c f hc

theorem precomp_nonDegenerate_iff {n : ℕ} (c : ComposableArrows (Paths V) n)
    {X : Paths V} (f : X ⟶ c.left) :
    c.precomp f ∈ (nerve (Paths V)).nonDegenerate (n + 1) ↔
      0 < f.length ∧ c ∈ (nerve (Paths V)).nonDegenerate n := by
  change (¬ c.precomp f ∈ (nerve (Paths V)).degenerate (n + 1)) ↔
    0 < f.length ∧ ¬ c ∈ (nerve (Paths V)).degenerate n
  rw [precomp_degenerate_iff, not_or, Nat.pos_iff_ne_zero]

end DaggerNativeFreePathNerveNondegeneracy
