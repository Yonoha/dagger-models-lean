import NativeFreePathPairingCells

/-! The actual native cells cover the entire native complement, including dimension data. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeFreePathNerveWeight DaggerNativeFreePathSpineComplementCoverage
open DaggerNativeFreePathInnerFaceNondegeneracy DaggerNativeFreePathSubdivisionInverse
open DaggerNativeFreePathPairingCells
universe u
namespace DaggerNativeFreePathPairingCoverage
noncomputable section

variable {V : Type u} [Quiver.{u + 1} V]

theorem cover (x : (generatorSpine V).N) :
    ∃ s : CellIndex V, x.toS = SSet.S.mk (upper s) ∨ x.toS = SSet.S.mk (lower s) := by
  obtain ⟨n, c, hc, hn, rfl⟩ := x.mk_surjective
  have hw : 1 < weight c := by
    change ¬ weight c ≤ 1 at hn
    omega
  cases n with
  | zero => rw [weight_zero_dim] at hw; omega
  | succ n =>
    change ComposableArrows (Paths V) (n + 1) at c
    have hp := ((nonDegenerate_iff_front c).mp hc).1
    by_cases hf : (c.map' 0 1).length = 1
    · cases n with
      | zero =>
        change 1 < (c.map' 0 1).length at hw
        omega
      | succ m =>
        let b : ComposableArrows (Paths V) (m + 1) := (nerve (Paths V)).δ 1 c
        have hb := delta_one_nonDegenerate c hc
        have hl : 1 < (b.map' 0 1).length := first_length_delta_one_gt_one c hc hf
        let s : CellIndex V := ⟨m, ⟨b, hb, hl⟩⟩
        have hu : upper s = c := split_delta_one c hf (split s)
        exact ⟨s, Or.inl (congrArg (SSet.S.mk (X := nerve (Paths V))) hu.symm)⟩
    · let s : CellIndex V := ⟨n, ⟨c, hc, by omega⟩⟩
      exact ⟨s, Or.inr rfl⟩

end
end DaggerNativeFreePathPairingCoverage
