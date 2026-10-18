import ChosenNecklaceCategory

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable {T U : NecklaceCode}

theorem bead_image_vertex (f : toSSet.{u} T ⟶ toSSet.{u} U) (b : T.Bead)
    (v : Fin (b.length + 1)) :
    SSet.stdSimplex.obj₀Equiv (U.inclusion.app _
      (f.app _ (T.beadSimplex b |>.app _ (SSet.stdSimplex.obj₀Equiv.symm v)))) =
        orderMap f (b.embedding v) := by
  change _ = (mapVertices f (ULift.up (b.embedding v))).down
  rw [← b.beadSimplex_vertex v]
  dsimp [mapVertices]
  rw [T.verticesEquiv.symm_apply_apply]
  rfl

/-- The two original bead endpoints land in one actual target bead, or both at its point. -/
theorem bead_endpoint_image (f : toSSet.{u} T ⟶ toSSet.{u} U) (b : T.Bead) :
    (orderMap f b.left = 0 ∧ orderMap f b.right = 0) ∨
      ∃ c : U.Bead, orderMap f b.left ∈ c.interval ∧ orderMap f b.right ∈ c.interval := by
  let x := SSet.yonedaEquiv (T.beadSimplex b ≫ f)
  let y := U.inclusion.app _ x
  have hx : y ∈ U.complex.obj (op ⦋b.length⦌) :=
    (U.complexIso.hom.app _ x).property
  have hv (v : Fin (b.length + 1)) : y v = orderMap f (b.embedding v) := by
    trans SSet.stdSimplex.obj₀Equiv ((T.beadSimplex b ≫ f ≫ U.inclusion).app _
      (SSet.stdSimplex.obj₀Equiv.symm v))
    · exact stdSimplex_vertex_naturality (T.beadSimplex b ≫ f ≫ U.inclusion)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋b.length⦌)) v
    · exact bead_image_vertex f b v
  have hl : y 0 = orderMap f b.left := by rw [hv, b.embedding_zero]
  have hr : y (Fin.last b.length) = orderMap f b.right := by
    rw [hv, b.embedding_last]
  rcases (U.mem_complex_iff y).mp hx with h | ⟨c, h⟩
  · exact Or.inl ⟨hl.symm.trans (h 0), hr.symm.trans (h (Fin.last b.length))⟩
  · exact Or.inr ⟨c, hl ▸ h 0, hr ▸ h (Fin.last b.length)⟩

/-- Target joints are images of actual source joints, without any injectivity premise. -/
theorem joints_subset_image (f : Hom.{u} T U) : U.joints ⊆ T.joints.image (orderMap f.map) := by
  classical
  intro w hw
  by_cases hlast : w = Fin.last U.len
  · exact Finset.mem_image.mpr ⟨Fin.last T.len, T.last_mem, by
      rw [orderMap_last, hlast]⟩
  let L := T.joints.filter (fun v ↦ orderMap f.map v ≤ w)
  have hL : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨T.first_mem, by
    rw [orderMap_first]
    exact Fin.zero_le w⟩⟩
  let l := L.max' hL
  have hl : l ∈ T.joints ∧ orderMap f.map l ≤ w := Finset.mem_filter.mp (L.max'_mem hL)
  by_cases he : orderMap f.map l = w
  · exact Finset.mem_image.mpr ⟨l, hl.1, he⟩
  have hgl : orderMap f.map l < w := lt_of_le_of_ne hl.2 he
  have hlt : l < Fin.last T.len := by
    apply lt_of_le_of_ne (Fin.le_last l)
    intro hn
    have heq : orderMap f.map l = Fin.last U.len := hn ▸ orderMap_last f
    exact hlast (le_antisymm (Fin.le_last w) (heq ▸ hl.2))
  let R := T.joints.filter (l < ·)
  have hR : R.Nonempty := ⟨Fin.last T.len, Finset.mem_filter.mpr ⟨T.last_mem, hlt⟩⟩
  let r := R.min' hR
  have hr : r ∈ T.joints ∧ l < r := Finset.mem_filter.mp (R.min'_mem hR)
  have hgr : w < orderMap f.map r := by
    by_contra hn
    have hm := L.le_max' r (Finset.mem_filter.mpr ⟨hr.1, le_of_not_gt hn⟩)
    exact (not_lt_of_ge hm) hr.2
  let b : T.Bead := ⟨l, r, hl.1, hr.1, hr.2, fun v hv hlv hvr ↦
    (not_lt_of_ge (R.min'_le v (Finset.mem_filter.mpr ⟨hv, hlv⟩))) hvr⟩
  rcases bead_endpoint_image f.map b with ⟨h0, h1⟩ | ⟨c, hc0, hc1⟩
  · have hne := hgl.trans hgr
    change orderMap f.map l < orderMap f.map r at hne
    exact False.elim ((not_lt_of_ge (h1.trans h0.symm).le) hne)
  · obtain ⟨hcL, _⟩ := Finset.mem_Icc.mp hc0
    obtain ⟨_, hcR⟩ := Finset.mem_Icc.mp hc1
    exact False.elim (c.no_joint w hw (hcL.trans_lt hgl) (hgr.trans_le hcR))

end

end DaggerChosenRigidificationNecklace.NecklaceCode
