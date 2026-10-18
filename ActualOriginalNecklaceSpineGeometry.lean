import NativeStandardSpineGeometry
import ChosenNecklaceBeadCoordinates

/-! The SAME original necklace contains the native spine; distinct beads overlap in it. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeStandardSpineInner DaggerChosenRigidificationNecklace
universe u
namespace DaggerActualOriginalNecklaceSpineGeometry
noncomputable section

variable (T : NecklaceCode)

instance bead_finite : Finite T.Bead :=
  Finite.of_injective (fun b : T.Bead ↦ b.left)
    (fun b c h ↦ b.left_injective c h)

theorem spine_le_complex : spine.{u} T.len ≤ T.complex := by
  intro q c hc
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      apply (T.mem_complex_iff c).mpr
      have hs := (mem_spine_iff c).mp hc
      let r := SSet.stdSimplex.asOrderHom c (Fin.last d)
      have hmax (j : Fin (d + 1)) : SSet.stdSimplex.asOrderHom c j ≤ r :=
        (SSet.stdSimplex.asOrderHom c).monotone (Fin.le_last j)
      by_cases hr : r = 0
      · left
        intro j
        exact le_antisymm (hr ▸ hmax j) (Fin.zero_le _)
      · obtain ⟨b, hl, hb⟩ := T.exists_bead_at r (Fin.pos_iff_ne_zero.mpr hr)
        right
        refine ⟨b, fun j ↦ Finset.mem_Icc.mpr ⟨?_, (hmax j).trans hb⟩⟩
        have hmin := (SSet.stdSimplex.asOrderHom c).monotone (Fin.zero_le j)
        change b.left.val < r.val at hl
        change r.val ≤ (SSet.stdSimplex.asOrderHom c 0).val + 1 at hs
        change (SSet.stdSimplex.asOrderHom c 0).val ≤
          (SSet.stdSimplex.asOrderHom c j).val at hmin
        change b.left.val ≤ (SSet.stdSimplex.asOrderHom c j).val
        omega

theorem bead_overlap_le_spine (b c : T.Bead) (hne : b ≠ c) :
    NecklaceCode.Bead.face.{u} b ⊓ c.face ≤ spine T.len := by
  intro q x hx
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      obtain ⟨hb, hc⟩ := hx
      rw [NecklaceCode.Bead.face, SSet.stdSimplex.mem_face_iff] at hb hc
      change ∀ j, SSet.stdSimplex.asOrderHom x j ∈ b.interval at hb
      change ∀ j, SSet.stdSimplex.asOrderHom x j ∈ c.interval at hc
      have hbmax := (Finset.mem_Icc.mp (hb (Fin.last d))).2
      have hbmin := (Finset.mem_Icc.mp (hb 0)).1
      have hcmax := (Finset.mem_Icc.mp (hc (Fin.last d))).2
      have hcmin := (Finset.mem_Icc.mp (hc 0)).1
      rw [mem_spine_iff]
      rcases lt_trichotomy b.left c.left with h | h | h
      · have ht := b.right_le_left c h
        have he := hbmax.trans (ht.trans hcmin)
        exact Nat.le_trans he (Nat.le_succ _)
      · exact False.elim (hne (b.left_injective c h))
      · have ht := c.right_le_left b h
        have he := hcmax.trans (ht.trans hbmin)
        exact Nat.le_trans he (Nat.le_succ _)

end
end DaggerActualOriginalNecklaceSpineGeometry
