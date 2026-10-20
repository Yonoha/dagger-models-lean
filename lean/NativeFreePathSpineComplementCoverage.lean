import NativeFreePathSubdivisionInverse
import NativeFreePathSubdivisionUniqueFace

/-! Every native nondegenerate simplex outside the weighted spine belongs to a subdivision pair. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeFreePathNerveWeight DaggerNativePathFirstSplit
open DaggerNativeFreePathFirstSubdivision DaggerNativeFreePathInnerFaceNondegeneracy
open DaggerNativeFreePathSubdivisionInverse
universe u
namespace DaggerNativeFreePathSpineComplementCoverage
noncomputable section

variable {V : Type u} [Quiver.{u + 1} V]

theorem weight_zero_dim (c : ComposableArrows (Paths V) 0) : weight c = 0 := by
  change (c.map (𝟙 (0 : Fin 1))).length = 0
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem outside_spine_partition {n : ℕ} (c : ComposableArrows (Paths V) n)
    (hc : c ∈ (nerve (Paths V)).nonDegenerate n) (hw : 1 < weight c) :
    (∃ (m : ℕ) (d : ComposableArrows (Paths V) (m + 1)),
      d ∈ (nerve (Paths V)).nonDegenerate (m + 1) ∧
        1 < (d.map' 0 1).length ∧ HEq c d) ∨
    (∃ (m : ℕ) (d : ComposableArrows (Paths V) (m + 2)),
      d ∈ (nerve (Paths V)).nonDegenerate (m + 2) ∧
        (d.map' 0 1).length = 1 ∧ HEq c d) := by
  cases n with
  | zero => rw [weight_zero_dim] at hw; omega
  | succ n =>
    have hp := ((nonDegenerate_iff_front c).mp hc).1
    by_cases hf : (c.map' 0 1).length = 1
    · cases n with
      | zero =>
        change 1 < (c.map' 0 1).length at hw
        omega
      | succ m => exact Or.inr ⟨m, c, hc, hf, HEq.rfl⟩
    · exact Or.inl ⟨n, c, hc, by omega, HEq.rfl⟩

theorem outside_spine_covered {n : ℕ} (c : ComposableArrows (Paths V) n)
    (hc : c ∈ (nerve (Paths V)).nonDegenerate n) (hw : 1 < weight c) :
    ∃ (m : ℕ) (d : ComposableArrows (Paths V) (m + 1))
      (s : FirstSplit (V := V) (d.map' 0 1)),
      d ∈ (nerve (Paths V)).nonDegenerate (m + 1) ∧
        1 < (d.map' 0 1).length ∧ (HEq c d ∨ HEq c (splitSimplex d s)) := by
  rcases outside_spine_partition c hc hw with ⟨m, d, hd, hf, he⟩ | ⟨m, d, hd, hf, he⟩
  · exact ⟨m, d, firstSplit _ (by omega), hd, hf, Or.inl he⟩
  · let b : ComposableArrows (Paths V) (m + 1) := (nerve (Paths V)).δ 1 d
    have hb : b ∈ (nerve (Paths V)).nonDegenerate (m + 1) :=
      delta_one_nonDegenerate d hd
    have hl : 1 < (b.map' 0 1).length := first_length_delta_one_gt_one d hd hf
    let s := firstSplit (V := V) (b.map' 0 1) (by omega)
    refine ⟨m, b, s, hb, hl, Or.inr ?_⟩
    have hs : splitSimplex b s = d := split_delta_one d hf s
    rw [hs]
    exact he

end
end DaggerNativeFreePathSpineComplementCoverage
