import OriginalFlagFlankedBeadOperators
import ChosenNecklaceCoverage

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

private theorem bead_right_le_of_left_lt {T : NecklaceCode} (c e : T.Bead)
    (h : c.left < e.left) : c.right ≤ e.left := by
  by_contra hn
  exact c.no_joint e.left e.left_mem h (lt_of_not_ge hn)

private theorem bead_eq_of_same_left {T : NecklaceCode} (c e : T.Bead)
    (h : c.left = e.left) : c = e := by
  have hr : c.right = e.right := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hc | he
    · exact e.no_joint c.right c.right_mem (h ▸ c.lt) hc
    · exact c.no_joint e.right e.right_mem (h.symm ▸ e.lt) he
  exact bead_eq_of_endpoints T h hr

variable {T U : NecklaceCode} {n : ℕ}
variable (F : Flag.{u} T n) (G : Flag.{u} U n)
variable (f : NecklaceCode.Hom.{u} T U) (hfg : NecklaceCode.Flag.map f F = G)
variable (hF : Flanked F) (hG : Flanked G)

include hfg hF hG in
/-- A target bead has exactly one surviving source bead in the ORIGINAL joint order. -/
theorem flanked_surviving_source_unique (d : U.Bead) :
    ∃! c : T.Bead,
      orderMap f.map c.left = d.left ∧ orderMap f.map c.right = d.right := by
  classical
  let r := orderMap f.map
  let S := T.joints.filter (fun v ↦ r v = d.left)
  have hS : S.Nonempty := by
    obtain ⟨v, hv, he⟩ := flanked_arrow_joint_preimage F G f hfg hF hG d.left d.left_mem
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, he⟩⟩
  let l := S.max' hS
  have hl : l ∈ T.joints ∧ r l = d.left := Finset.mem_filter.mp (S.max'_mem hS)
  obtain ⟨w, hw, he⟩ := flanked_arrow_joint_preimage F G f hfg hF hG d.right d.right_mem
  have hlw : l < w := by
    by_contra hn
    have hh := r.monotone (le_of_not_gt hn)
    rw [hl.2, he] at hh
    exact (not_le_of_gt d.lt) hh
  have hlen : l.val + 1 < T.len + 1 := by
    have hh := w.isLt
    change l.val < w.val at hlw
    omega
  let v : Fin (T.len + 1) := ⟨l.val + 1, hlen⟩
  have hlv : l < v := by change l.val < l.val + 1; omega
  obtain ⟨c, hcv, hvc⟩ := T.exists_bead_at v (by
    change 0 < l.val + 1
    omega)
  have hcl : c.left ≤ l := by
    change c.left.val ≤ l.val
    change c.left.val < l.val + 1 at hcv
    omega
  have hlc : l < c.right := hlv.trans_le hvc
  have hcle : c.left = l := by
    by_contra hn
    exact c.no_joint l hl.1 (lt_of_le_of_ne hcl hn) hlc
  have hcw : c.right ≤ w := by
    by_contra hn
    apply c.no_joint w hw
    · simpa only [hcle] using hlw
    · exact lt_of_not_ge hn
  have hrl : d.left ≤ r c.right := by
    rw [← hl.2]
    exact r.monotone hlc.le
  have hrr : r c.right ≤ d.right := by
    rw [← he]
    exact r.monotone hcw
  have hrlt : d.left < r c.right := by
    apply lt_of_le_of_ne hrl
    intro hn
    have hm : c.right ≤ l := S.le_max' c.right
      (Finset.mem_filter.mpr ⟨c.right_mem, hn.symm⟩)
    exact (not_le_of_gt hlc) hm
  have hre : r c.right = d.right := by
    apply le_antisymm hrr
    by_contra hn
    exact d.no_joint (r c.right)
      (flanked_arrow_joint F G f hfg hF hG c.right c.right_mem)
      hrlt (lt_of_not_ge hn)
  refine ⟨c, ⟨by change r c.left = d.left; rw [hcle, hl.2], hre⟩, ?_⟩
  intro e heq
  have hele : e.left = c.left := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hec | hce
    · have hh := r.monotone (bead_right_le_of_left_lt e c hec)
      rw [heq.2, hcle, hl.2] at hh
      exact (not_le_of_gt d.lt) hh
    · have hh := r.monotone (bead_right_le_of_left_lt c e hce)
      rw [hre, heq.1] at hh
      exact (not_le_of_gt d.lt) hh
  exact bead_eq_of_same_left e c hele

/-- This choice is from the proved finite-survivor contract, not from simplex labels in X. -/
def survivingSourceBead (d : U.Bead) : T.Bead :=
  Classical.choose (flanked_surviving_source_unique F G f hfg hF hG d)

theorem survivingSourceBead_left (d : U.Bead) :
    orderMap f.map (survivingSourceBead F G f hfg hF hG d).left = d.left :=
  (Classical.choose_spec (flanked_surviving_source_unique F G f hfg hF hG d)).1.1

theorem survivingSourceBead_right (d : U.Bead) :
    orderMap f.map (survivingSourceBead F G f hfg hF hG d).right = d.right :=
  (Classical.choose_spec (flanked_surviving_source_unique F G f hfg hF hG d)).1.2

theorem survivingSourceBead_positive (d : U.Bead) :
    orderMap f.map (survivingSourceBead F G f hfg hF hG d).left <
      orderMap f.map (survivingSourceBead F G f hfg hF hG d).right := by
  rw [survivingSourceBead_left, survivingSourceBead_right]
  exact d.lt

theorem survivingSourceBead_unique (d : U.Bead) (c : T.Bead)
    (hl : orderMap f.map c.left = d.left) (hr : orderMap f.map c.right = d.right) :
    c = survivingSourceBead F G f hfg hF hG d :=
  (Classical.choose_spec (flanked_surviving_source_unique F G f hfg hF hG d)).2 c ⟨hl, hr⟩

theorem survivingSourceBead_image (d : U.Bead) :
    flankedImageBead F G f hfg hF hG (survivingSourceBead F G f hfg hF hG d)
      (survivingSourceBead_positive F G f hfg hF hG d) = d :=
  bead_eq_of_endpoints U (survivingSourceBead_left F G f hfg hF hG d)
    (survivingSourceBead_right F G f hfg hF hG d)

end

end DaggerOriginalFlagFlankification
