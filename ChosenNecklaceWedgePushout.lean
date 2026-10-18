import ChosenNecklaceWedgeDegree
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T U : NecklaceCode) {n : ℕ}

theorem wedgeLeft_injective :
    Function.Injective ((wedgeιLeft.{u} T U).app (op ⦋n⦌)) := by
  intro x y h
  apply necklace_simplex_ext T
  intro i
  have hh := congrArg
    (fun z ↦ (wedge T U).inclusion.app (op ⦋n⦌) z i) h
  dsimp only at hh
  rw [wedgeιLeft_apply, wedgeιLeft_apply] at hh
  exact (wedgeLeft T U).injective hh

theorem wedgeRight_injective :
    Function.Injective ((wedgeιRight.{u} T U).app (op ⦋n⦌)) := by
  intro x y h
  apply necklace_simplex_ext U
  intro i
  have hh := congrArg
    (fun z ↦ (wedge T U).inclusion.app (op ⦋n⦌) z i) h
  dsimp only at hh
  rw [wedgeιRight_apply, wedgeιRight_apply] at hh
  exact (wedgeRight T U).injective hh

theorem wedge_cross (x : (toSSet.{u} T).obj (op ⦋n⦌))
    (y : (toSSet.{u} U).obj (op ⦋n⦌))
    (h : (wedgeιLeft T U).app _ x = (wedgeιRight T U).app _ y) :
    x = (pointAt T (ULift.up (Fin.last T.len))).app _ (zeroSimplex n) ∧
      y = (pointAt U (ULift.up 0)).app _ (zeroSimplex n) := by
  have hv (i : Fin (n + 1)) := congrArg
    (fun z ↦ (wedge T U).inclusion.app (op ⦋n⦌) z i) h
  have he (i : Fin (n + 1)) :
      (T.inclusion.app _ x i).val = T.len + (U.inclusion.app _ y i).val := by
    have hi := hv i
    dsimp only at hi
    rw [wedgeιLeft_apply, wedgeιRight_apply] at hi
    exact congrArg Fin.val hi
  constructor
  · apply constant_simplex_eq
    intro i
    apply Fin.ext
    have hi := he i
    have hb := (T.inclusion.app _ x i).isLt
    change (T.inclusion.app _ x i).val = T.len
    omega
  · apply constant_simplex_eq
    intro i
    apply Fin.ext
    have hi := he i
    have hb := (T.inclusion.app _ x i).isLt
    change (U.inclusion.app _ y i).val = 0
    omega

def wedgeDegreePullback (n : ℕ) :
    IsPullback ((pointAt.{u} T (ULift.up (Fin.last T.len))).app (op ⦋n⦌))
      ((pointAt U (ULift.up 0)).app (op ⦋n⦌))
      ((wedgeιLeft T U).app (op ⦋n⦌)) ((wedgeιRight T U).app (op ⦋n⦌)) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (wedge_comm.{u} T U) _, ?_, ?_⟩
  · intro x y _h
    exact (zeroSimplex_unique x).trans (zeroSimplex_unique y).symm
  · intro x y h
    obtain ⟨hx, hy⟩ := wedge_cross T U x y h
    exact ⟨zeroSimplex n, hx.symm, hy.symm⟩

def wedgeDegreePushout (n : ℕ) :
    IsPushout ((pointAt.{u} T (ULift.up (Fin.last T.len))).app (op ⦋n⦌))
      ((pointAt U (ULift.up 0)).app (op ⦋n⦌))
      ((wedgeιLeft T U).app (op ⦋n⦌)) ((wedgeιRight T U).app (op ⦋n⦌)) := by
  letI : Mono ((wedgeιLeft.{u} T U).app (op ⦋n⦌)) :=
    (mono_iff_injective _).mpr (wedgeLeft_injective T U)
  apply Types.isPushout_of_isPullback_of_mono' (wedgeDegreePullback T U n)
  · ext x
    simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    exact wedge_degree_cover T U x
  · intro x y _hx _hy h
    exact wedgeRight_injective T U h

/-- Both actual inclusions and the full arbitrary-target simplicial pushout UP. -/
def wedgeIsPushout :
    IsPushout (pointAt T (ULift.up (Fin.last T.len))) (pointAt U (ULift.up 0))
      (wedgeιLeft.{u} T U) (wedgeιRight T U) where
  w := wedge_comm T U
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun q ↦ by
    obtain ⟨q⟩ := q
    induction q using SimplexCategory.rec with | _ n
    exact (PushoutCocone.isColimitMapCoconeEquiv _ _).2
      (wedgeDegreePushout T U n).isColimit)⟩

def wedgeDesc {X : SSet.{u}} (f : toSSet.{u} T ⟶ X) (g : toSSet.{u} U ⟶ X)
    (h : pointAt T (ULift.up (Fin.last T.len)) ≫ f = pointAt U (ULift.up 0) ≫ g) :
    toSSet.{u} (wedge T U) ⟶ X :=
  (wedgeIsPushout T U).desc f g h

theorem wedgeDesc_left {X : SSet.{u}} (f : toSSet.{u} T ⟶ X)
    (g : toSSet.{u} U ⟶ X)
    (h : pointAt T (ULift.up (Fin.last T.len)) ≫ f = pointAt U (ULift.up 0) ≫ g) :
    wedgeιLeft T U ≫ wedgeDesc T U f g h = f :=
  (wedgeIsPushout T U).inl_desc f g h

theorem wedgeDesc_right {X : SSet.{u}} (f : toSSet.{u} T ⟶ X)
    (g : toSSet.{u} U ⟶ X)
    (h : pointAt T (ULift.up (Fin.last T.len)) ≫ f = pointAt U (ULift.up 0) ≫ g) :
    wedgeιRight T U ≫ wedgeDesc T U f g h = g :=
  (wedgeIsPushout T U).inr_desc f g h

theorem wedgeDesc_uniq {X : SSet.{u}} (f : toSSet.{u} T ⟶ X)
    (g : toSSet.{u} U ⟶ X)
    (h : pointAt T (ULift.up (Fin.last T.len)) ≫ f = pointAt U (ULift.up 0) ≫ g)
    (k : toSSet.{u} (wedge T U) ⟶ X) (hl : wedgeιLeft T U ≫ k = f)
    (hr : wedgeιRight T U ≫ k = g) : k = wedgeDesc T U f g h :=
  (wedgeIsPushout T U).hom_ext (hl.trans (wedgeDesc_left T U f g h).symm)
    (hr.trans (wedgeDesc_right T U f g h).symm)

end

end DaggerChosenRigidificationNecklace.NecklaceCode
