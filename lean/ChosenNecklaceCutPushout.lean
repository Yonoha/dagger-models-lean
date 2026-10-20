import ChosenNecklaceCutDegree

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode) (j : Fin (T.len + 1))

def cutDegreePullback (n : ℕ) :
    IsPullback
      ((pointAt.{u} (cutLeft T j) (ULift.up (Fin.last _))).app (op ⦋n⦌))
      ((pointAt (cutRight T j) (ULift.up 0)).app (op ⦋n⦌))
      ((cutLeftι T j).app (op ⦋n⦌)) ((cutRightι T j).app (op ⦋n⦌)) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (cut_comm.{u} T j) _, ?_, ?_⟩
  · intro x y _h
    exact (zeroSimplex_unique x).trans (zeroSimplex_unique y).symm
  · intro x y h
    obtain ⟨hx, hy⟩ := cut_cross T j x y h
    exact ⟨zeroSimplex n, hx.symm, hy.symm⟩

def cutDegreePushout (hj : j ∈ T.joints) (n : ℕ) :
    IsPushout
      ((pointAt.{u} (cutLeft T j) (ULift.up (Fin.last _))).app (op ⦋n⦌))
      ((pointAt (cutRight T j) (ULift.up 0)).app (op ⦋n⦌))
      ((cutLeftι T j).app (op ⦋n⦌)) ((cutRightι T j).app (op ⦋n⦌)) := by
  letI : Mono ((cutLeftι.{u} T j).app (op ⦋n⦌)) :=
    (mono_iff_injective _).mpr (intervalι_injective T 0 j (Fin.zero_le j))
  apply Types.isPushout_of_isPullback_of_mono' (cutDegreePullback T j n)
  · ext x
    simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    exact cut_degree_cover T j hj x
  · intro x y _hx _hy h
    exact intervalι_injective T j (Fin.last T.len) (Fin.le_last j) h

/-- Actual cut along an original joint, including either degenerate point side and full UP. -/
def cutIsPushout (hj : j ∈ T.joints) :
    IsPushout (pointAt (cutLeft T j) (ULift.up (Fin.last _)))
      (pointAt (cutRight T j) (ULift.up 0)) (cutLeftι.{u} T j) (cutRightι T j) where
  w := cut_comm T j
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun q ↦ by
    obtain ⟨q⟩ := q
    induction q using SimplexCategory.rec with | _ n
    exact (PushoutCocone.isColimitMapCoconeEquiv _ _).2
      (cutDegreePushout T j hj n).isColimit)⟩

end

end DaggerChosenRigidificationNecklace.NecklaceCode
