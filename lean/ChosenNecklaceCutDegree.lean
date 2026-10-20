import ChosenNecklaceIntervalFactor
import ChosenNecklaceWedgePushout

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode) (j : Fin (T.len + 1)) {n : ℕ}

abbrev cutLeft : NecklaceCode := intervalCode T 0 j (Fin.zero_le j)

abbrev cutRight : NecklaceCode := intervalCode T j (Fin.last T.len) (Fin.le_last j)

def cutLeftι : toSSet.{u} (cutLeft T j) ⟶ toSSet.{u} T :=
  intervalι T 0 j (Fin.zero_le j)

def cutRightι : toSSet.{u} (cutRight T j) ⟶ toSSet.{u} T :=
  intervalι T j (Fin.last T.len) (Fin.le_last j)

theorem cut_comm :
    pointAt (cutLeft T j) (ULift.up (Fin.last (cutLeft T j).len)) ≫ cutLeftι.{u} T j =
      pointAt (cutRight T j) (ULift.up 0) ≫ cutRightι T j := by
  ext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  apply necklace_simplex_ext T
  intro v
  change T.inclusion.app _ ((intervalι T 0 j (Fin.zero_le j)).app _
      ((pointAt (cutLeft T j) (ULift.up (Fin.last _))).app _ x)) v =
    T.inclusion.app _ ((intervalι T j (Fin.last T.len) (Fin.le_last j)).app _
      ((pointAt (cutRight T j) (ULift.up 0)).app _ x)) v
  rw [intervalι_apply, intervalι_apply, pointAt_inclusion_apply,
    pointAt_inclusion_apply]
  change intervalEmbedding T 0 j (Fin.zero_le j) (Fin.last (j.val - 0)) =
    intervalEmbedding T j (Fin.last T.len) (Fin.le_last j) 0
  exact (intervalEmbedding_last T 0 j (Fin.zero_le j)).trans
    (intervalEmbedding_first T j (Fin.last T.len) (Fin.le_last j)).symm

theorem cut_cross (x : (toSSet.{u} (cutLeft T j)).obj (op ⦋n⦌))
    (y : (toSSet.{u} (cutRight T j)).obj (op ⦋n⦌))
    (h : (cutLeftι T j).app _ x = (cutRightι T j).app _ y) :
    x = (pointAt (cutLeft T j) (ULift.up (Fin.last _))).app _ (zeroSimplex n) ∧
      y = (pointAt (cutRight T j) (ULift.up 0)).app _ (zeroSimplex n) := by
  have hv (v : Fin (n + 1)) := congrArg (fun z ↦ T.inclusion.app (op ⦋n⦌) z v) h
  have he (v : Fin (n + 1)) :
      intervalEmbedding T 0 j (Fin.zero_le j) ((cutLeft T j).inclusion.app _ x v) =
        intervalEmbedding T j (Fin.last T.len) (Fin.le_last j)
          ((cutRight T j).inclusion.app _ y v) := by
    simpa only [cutLeftι, cutRightι, intervalι_apply] using hv v
  constructor
  · apply constant_simplex_eq
    intro v
    apply Fin.ext
    have hh := congrArg Fin.val (he v)
    have hb := ((cutLeft T j).inclusion.app _ x v).isLt
    change ((cutLeft T j).inclusion.app _ x v).val < j.val - 0 + 1 at hb
    change ((cutLeft T j).inclusion.app _ x v).val = j.val - 0
    change 0 + ((cutLeft T j).inclusion.app _ x v).val =
      j.val + ((cutRight T j).inclusion.app _ y v).val at hh
    omega
  · apply constant_simplex_eq
    intro v
    apply Fin.ext
    have hh := congrArg Fin.val (he v)
    have hb := ((cutLeft T j).inclusion.app _ x v).isLt
    change ((cutLeft T j).inclusion.app _ x v).val < j.val - 0 + 1 at hb
    change ((cutRight T j).inclusion.app _ y v).val = 0
    change 0 + ((cutLeft T j).inclusion.app _ x v).val =
      j.val + ((cutRight T j).inclusion.app _ y v).val at hh
    omega

/-- At a joint, no actual positive bead straddles the cut. -/
theorem bead_cut (hj : j ∈ T.joints) (d : T.Bead) : d.right ≤ j ∨ j ≤ d.left := by
  by_cases h : d.right ≤ j
  · exact Or.inl h
  · right
    by_contra hl
    exact d.no_joint j hj (lt_of_not_ge hl) (lt_of_not_ge h)

theorem cut_degree_cover (hj : j ∈ T.joints) (x : (toSSet.{u} T).obj (op ⦋n⦌)) :
    (∃ y, (cutLeftι T j).app _ y = x) ∨ (∃ y, (cutRightι T j).app _ y = x) := by
  have hm := (T.complexIso.hom.app _ x).property
  rcases (T.mem_complex_iff _).mp hm with h | ⟨d, h⟩
  · left
    have hx : ∀ v, 0 ≤ T.inclusion.app _ x v ∧ T.inclusion.app _ x v ≤ j := by
      intro v
      exact ⟨Fin.zero_le _, (h v) ▸ Fin.zero_le j⟩
    exact ⟨intervalLiftSimplex T 0 j (Fin.zero_le j) x hx,
      intervalι_lift T 0 j (Fin.zero_le j) x hx⟩
  · rcases bead_cut T j hj d with hl | hr
    · left
      have hx : ∀ v, 0 ≤ T.inclusion.app _ x v ∧ T.inclusion.app _ x v ≤ j := by
        intro v
        exact ⟨Fin.zero_le _, (Finset.mem_Icc.mp (h v)).2.trans hl⟩
      exact ⟨intervalLiftSimplex T 0 j (Fin.zero_le j) x hx,
        intervalι_lift T 0 j (Fin.zero_le j) x hx⟩
    · right
      have hx : ∀ v, j ≤ T.inclusion.app _ x v ∧
          T.inclusion.app _ x v ≤ Fin.last T.len := by
        intro v
        exact ⟨hr.trans (Finset.mem_Icc.mp (h v)).1, Fin.le_last _⟩
      exact ⟨intervalLiftSimplex T j (Fin.last T.len) (Fin.le_last j) x hx,
        intervalι_lift T j (Fin.last T.len) (Fin.le_last j) x hx⟩

end

end DaggerChosenRigidificationNecklace.NecklaceCode
