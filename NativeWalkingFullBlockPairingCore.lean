import NativeWalkingRelativeCellEquivalence
import NativeWalkingRelativeCellCoverage

/-! A proper inner PairingCore on the whole original relative cell class, in all degrees. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordBlocks DaggerNativeWalkingWordFaces
open DaggerNativeWalkingBlockInnerIndices
open DaggerNativeWalkingRelativeCells DaggerNativeWalkingRelativeCellBranches
open DaggerNativeWalkingRelativeCellEquivalence DaggerNativeWalkingRelativeCellCoverage
universe u
namespace DaggerNativeWalkingFullBlockPairingCore
noncomputable section

def indexEquivalence (n : ℕ) : LowerIndex.{u} n ≃ UpperIndex.{u} n :=
  Equiv.sigmaCongrRight (fun d ↦ cellEquivalence n d)

def cellIndex {n d : ℕ} (s : UpperCell.{u} n d) : Fin (d + 3) :=
  if level s.val < Fin.last (n + 1) then
    lastActive (coordinates s.val.val) (true_exists s.val)
  else firstActive (coordinates s.val.val) (true_exists s.val)

theorem cellIndex_inner {n d : ℕ} (s : UpperCell.{u} n d) :
    cellIndex s ≠ 0 ∧ cellIndex s ≠ Fin.last (d + 2) := by
  by_cases ha : level s.val < Fin.last (n + 1)
  · have ht : lastTag s.val = false := by simpa only [endTag, if_pos ha] using s.property
    simpa only [cellIndex, if_pos ha] using
      terminal_deletion (coordinates s.val.val) (true_exists s.val)
        (projection_surjective s.val) ha ht
  · have ht : firstTag s.val = false := by simpa only [endTag, if_neg ha] using s.property
    simpa only [cellIndex, if_neg ha] using
      initial_deletion (coordinates s.val.val) (true_exists s.val)
        (projection_surjective s.val) (initial_level_pos s.val ha) ht

theorem lower_val_index {n d : ℕ} (s : UpperCell.{u} n d) :
    (lower s).val.val = (ambient.{u} n).δ (cellIndex s) s.val.val := by
  by_cases ha : level s.val < Fin.last (n + 1)
  · have ht : lastTag s.val = false := by simpa only [endTag, if_pos ha] using s.property
    rw [lower_val_terminal s ha ht]
    simp only [cellIndex, if_pos ha]
    rfl
  · have ht : firstTag s.val = false := by simpa only [endTag, if_neg ha] using s.property
    rw [lower_val_initial s ha ht]
    simp only [cellIndex, if_neg ha]
    rfl

def pairingCore (n : ℕ) : (relative.{u} n).PairingCore where
  ι := UpperIndex.{u} n
  d s := s.1 + 1
  type₁ s := s.2.val.val
  index s := cellIndex s.2
  nonDegenerate₁ s := s.2.val.property.1
  nonDegenerate₂ s := by
    rw [← lower_val_index s.2]
    exact (lower s.2).val.property.1
  notMem₁ s := s.2.val.property.2
  notMem₂ s := by
    rw [← lower_val_index s.2]
    exact (lower s.2).val.property.2
  injective_type₁ {s t} he := by
    apply upperToN_injective
    exact (SSet.Subcomplex.N.eq_iff_sMk_eq _ _).mpr he
  injective_type₂ {s t} he := by
    apply (indexEquivalence n).symm.injective
    apply lowerToN_injective
    apply (SSet.Subcomplex.N.eq_iff_sMk_eq _ _).mpr
    change SSet.S.mk (lower s.2).val.val = SSet.S.mk (lower t.2).val.val
    rw [lower_val_index, lower_val_index]
    exact he
  type₁_neq_type₂ s t he := by
    apply disjoint_classes s.2 (lower t.2)
    apply (SSet.Subcomplex.N.eq_iff_sMk_eq _ _).mpr
    change SSet.S.mk s.2.val.val = SSet.S.mk (lower t.2).val.val
    rw [lower_val_index]
    exact he
  surjective' x := by
    obtain hu | hl := whole_cell_partition x
    · obtain ⟨d, y, hy⟩ := hu
      refine ⟨⟨d, y⟩, Or.inl ?_⟩
      exact congrArg (fun z : (relative.{u} n).N ↦ z.toS) hy.symm
    · obtain ⟨d, y, hy⟩ := hl
      let s := upper y
      refine ⟨⟨d, s⟩, Or.inr ?_⟩
      have hh : (ambient.{u} n).δ (cellIndex s) s.val.val = y.val.val := by
        rw [← lower_val_index, lower_upper]
      change x.toS = SSet.S.mk ((ambient.{u} n).δ (cellIndex s) s.val.val)
      calc
        _ = SSet.S.mk y.val.val := congrArg (fun z : (relative.{u} n).N ↦ z.toS) hy.symm
        _ = _ := congrArg SSet.S.mk hh.symm

instance pairingCoreProper (n : ℕ) : (pairingCore.{u} n).IsProper where
  isUniquelyCodimOneFace s := uniquelyCodimOneFace s.2.val.val s.2.val.property.1 (cellIndex s.2)

theorem pairingCoreInner (n : ℕ) : (pairingCore.{u} n).IsInner :=
  fun s ↦ cellIndex_inner s.2

end
end DaggerNativeWalkingFullBlockPairingCore
