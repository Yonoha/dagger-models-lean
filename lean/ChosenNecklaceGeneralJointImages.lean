import ChosenNecklaceJointImages

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable {T U : NecklaceCode}

/-- All joints inside the actual image interval, without endpoint-preserving assumptions. -/
theorem joint_between_image (f : toSSet.{u} T ⟶ toSSet.{u} U)
    (w : Fin (U.len + 1)) (hw : w ∈ U.joints)
    (h0 : orderMap f 0 ≤ w) (hn : w ≤ orderMap f (Fin.last T.len)) :
    ∃ v ∈ T.joints, orderMap f v = w := by
  classical
  by_cases hlast : w = orderMap f (Fin.last T.len)
  · exact ⟨Fin.last T.len, T.last_mem, hlast.symm⟩
  let L := T.joints.filter (fun v ↦ orderMap f v ≤ w)
  have hL : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨T.first_mem, h0⟩⟩
  let l := L.max' hL
  have hl : l ∈ T.joints ∧ orderMap f l ≤ w := Finset.mem_filter.mp (L.max'_mem hL)
  by_cases he : orderMap f l = w
  · exact ⟨l, hl.1, he⟩
  have hgl : orderMap f l < w := lt_of_le_of_ne hl.2 he
  have hlt : l < Fin.last T.len := by
    apply lt_of_le_of_ne (Fin.le_last l)
    intro heq
    exact hlast (le_antisymm hn (heq ▸ hl.2))
  let R := T.joints.filter (l < ·)
  have hR : R.Nonempty := ⟨Fin.last T.len, Finset.mem_filter.mpr ⟨T.last_mem, hlt⟩⟩
  let r := R.min' hR
  have hr : r ∈ T.joints ∧ l < r := Finset.mem_filter.mp (R.min'_mem hR)
  have hgr : w < orderMap f r := by
    by_contra h
    have hm := L.le_max' r (Finset.mem_filter.mpr ⟨hr.1, le_of_not_gt h⟩)
    exact (not_lt_of_ge hm) hr.2
  let b : T.Bead := ⟨l, r, hl.1, hr.1, hr.2, fun v hv hlv hvr ↦
    (not_lt_of_ge (R.min'_le v (Finset.mem_filter.mpr ⟨hv, hlv⟩))) hvr⟩
  rcases bead_endpoint_image f b with ⟨h1, h2⟩ | ⟨c, hc0, hc1⟩
  · have hne := hgl.trans hgr
    change orderMap f l < orderMap f r at hne
    exact False.elim ((not_lt_of_ge (h2.trans h1.symm).le) hne)
  · obtain ⟨hcL, _⟩ := Finset.mem_Icc.mp hc0
    obtain ⟨_, hcR⟩ := Finset.mem_Icc.mp hc1
    exact False.elim (c.no_joint w hw (hcL.trans_lt hgl) (hgr.trans_le hcR))

end

end DaggerChosenRigidificationNecklace.NecklaceCode
