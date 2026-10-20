import ChosenNecklaceCode
import Mathlib.Data.Finset.Max

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode)

/-- Every noninitial vertex lies in an actual positive consecutive-joint bead. -/
theorem exists_bead_at (v : Fin (T.len + 1)) (hv : 0 < v) :
    ∃ b : T.Bead, b.left < v ∧ v ≤ b.right := by
  classical
  let L := T.joints.filter (· < v)
  have hL : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨T.first_mem, hv⟩⟩
  let l := L.max' hL
  have hl : l ∈ T.joints ∧ l < v := Finset.mem_filter.mp (L.max'_mem hL)
  let U := T.joints.filter (l < ·)
  have hU : U.Nonempty := by
    refine ⟨Fin.last T.len, Finset.mem_filter.mpr ⟨T.last_mem, ?_⟩⟩
    exact hl.2.trans_le (Fin.le_last v)
  let r := U.min' hU
  have hr : r ∈ T.joints ∧ l < r := Finset.mem_filter.mp (U.min'_mem hU)
  have hvr : v ≤ r := by
    by_contra h
    have hrv : r < v := lt_of_not_ge h
    have hm : r ≤ l := L.le_max' r (Finset.mem_filter.mpr ⟨hr.1, hrv⟩)
    exact (not_lt_of_ge hm) hr.2
  refine ⟨⟨l, r, hl.1, hr.1, hr.2, ?_⟩, hl.2, hvr⟩
  intro w hw hlw hwr
  have hrw : r ≤ w := U.min'_le w (Finset.mem_filter.mpr ⟨hw, hlw⟩)
  exact (not_lt_of_ge hrw) hwr

theorem exists_bead_interval (v : Fin (T.len + 1)) (hv : v ≠ 0) :
    ∃ b : T.Bead, v ∈ b.interval := by
  obtain ⟨b, hl, hr⟩ := T.exists_bead_at v (by
    have hn : 0 ≤ v := Fin.zero_le v
    exact lt_of_le_of_ne hn (Ne.symm hv))
  exact ⟨b, Finset.mem_Icc.mpr ⟨hl.le, hr⟩⟩

/-- A simplex belongs to the necklace exactly when its image is in one bead or the point. -/
theorem mem_complex_iff {n : ℕ} (x : (Δ[T.len] : SSet.{u}).obj (op ⦋n⦌)) :
    x ∈ T.complex.obj (op ⦋n⦌) ↔
      (∀ i, x i = 0) ∨ ∃ b : T.Bead, ∀ i, x i ∈ b.interval := by
  classical
  simp only [complex, Subfunctor.max_obj, Set.mem_union,
    Subfunctor.iSup_obj, Set.mem_iUnion, Bead.face, SSet.stdSimplex.mem_face_iff,
    Finset.mem_singleton]

theorem vertex_mem_complex (v : Fin (T.len + 1))
    (x : (Δ[T.len] : SSet.{u}).obj (op ⦋0⦌)) (hx : ∀ i, x i = v) :
    x ∈ T.complex.obj (op ⦋0⦌) := by
  apply (T.mem_complex_iff x).mpr
  by_cases hv : v = 0
  · exact Or.inl (fun i ↦ (hx i).trans hv)
  · obtain ⟨b, hb⟩ := T.exists_bead_interval v hv
    exact Or.inr ⟨b, fun i ↦ (hx i).symm ▸ hb⟩

end

end DaggerChosenRigidificationNecklace.NecklaceCode
