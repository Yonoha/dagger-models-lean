import NativeFreePathPairingCoverage

/-! A proper inner native PairingCore on the entire free-path spine complement. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeFreePathNerveWeight DaggerNativeFreePathPairingCells
open DaggerNativeFreePathPairingCoverage DaggerNativeFreePathSubdivisionUniqueFace
universe u
namespace DaggerNativeFreePathPairingCore
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

def pairingCore : (generatorSpine V).PairingCore where
  ι := CellIndex V
  d s := s.1 + 1
  type₁ s := upper s
  index s := 1
  nonDegenerate₁ := upper_nonDegenerate
  nonDegenerate₂ s := by
    change (nerve (Paths V)).δ (1 : Fin (s.1 + 3)) (upper s) ∈ _
    rw [delta_one_upper]
    exact lower_nonDegenerate s
  notMem₁ := upper_notMem
  notMem₂ s := by
    change (nerve (Paths V)).δ (1 : Fin (s.1 + 3)) (upper s) ∉ _
    rw [delta_one_upper]
    exact lower_notMem s
  injective_type₁ := upper_injective
  injective_type₂ h := by
    rw [delta_one_upper, delta_one_upper] at h
    exact lower_injective h
  type₁_neq_type₂ s t := by
    rw [delta_one_upper]
    exact upper_ne_lower s t
  surjective' x := by
    obtain ⟨s, hs | hs⟩ := cover x
    · exact ⟨s, Or.inl hs⟩
    · refine ⟨s, Or.inr ?_⟩
      rw [delta_one_upper]
      exact hs

instance pairingCoreProper : (pairingCore V).IsProper where
  isUniquelyCodimOneFace s := by
    change SSet.IsUniquelyCodimOneFace (X := nerve (Paths V))
      ((nerve (Paths V)).δ (1 : Fin (s.1 + 3)) (upper s)) (upper s)
    rw [delta_one_upper]
    exact unique_inner_face _ _ s.2.property.2

theorem pairingCoreInner : (pairingCore V).IsInner := by
  intro s
  change (1 : Fin (s.1 + 3)) ≠ 0 ∧ (1 : Fin (s.1 + 3)) ≠ Fin.last (s.1 + 2)
  constructor
  · intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_one, Fin.val_zero] at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_one, Fin.val_last] at hv
    omega

end
end DaggerNativeFreePathPairingCore
