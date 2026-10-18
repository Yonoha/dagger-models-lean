import OriginalFlagFiniteCode

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

/-- Consecutive selected joints stay inside one original bead; no injectivity into X occurs. -/
theorem interval_in_original_bead (T : NecklaceCode) (l r : Fin (T.len + 1))
    (hlr : l < r) (hgap : ∀ v ∈ T.joints, l < v → v < r → False) :
    ∃ c : T.Bead, ∀ v ∈ Finset.Icc l r, v ∈ c.interval := by
  obtain ⟨c, hcr, hrc⟩ := T.exists_bead_at r ((Fin.zero_le l).trans_lt hlr)
  have hcl : c.left ≤ l := by
    by_contra h
    exact hgap c.left c.left_mem (lt_of_not_ge h) hcr
  refine ⟨c, ?_⟩
  intro v hv
  obtain ⟨hlv, hvr⟩ := Finset.mem_Icc.mp hv
  exact Finset.mem_Icc.mpr ⟨hcl.trans hlv, hvr.trans hrc⟩

variable {T : NecklaceCode} {n : ℕ} (F : Flag.{u} T n)

theorem flankEmbedding_no_original_joint (b : (flankCode F).Bead)
    (v : Fin (T.len + 1)) (hv : v ∈ T.joints)
    (hl : flankEmbedding F b.left < v) (hr : v < flankEmbedding F b.right) : False := by
  have hj : v ∈ selectedJoints F := originalJoints_subset F hv
  have hV : v ∈ selectedVertices F := selectedJoints_subset F hj
  let k := ((selectedVertices F).orderIsoOfFin (flank_card F)).symm ⟨v, hV⟩
  have hk : flankEmbedding F k = v := congrArg Subtype.val
    (((selectedVertices F).orderIsoOfFin (flank_card F)).apply_symm_apply ⟨v, hV⟩)
  have hkJ : k ∈ (flankCode F).joints := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hk.symm ▸ hj⟩
  exact b.no_joint k hkJ
    ((flankEmbedding F).lt_iff_lt.mp (hk.symm ▸ hl))
    ((flankEmbedding F).lt_iff_lt.mp (hk.symm ▸ hr))

/-- The accepted orderLift hypothesis is proved for the actual finite recoding. -/
theorem flankEmbedding_beadCondition :
    BeadImageCondition (T := flankCode F) (U := T) (flankEmbedding F).toOrderHom := by
  intro b
  obtain ⟨c, hc⟩ := interval_in_original_bead T
    (flankEmbedding F b.left) (flankEmbedding F b.right)
    ((flankEmbedding F).strictMono b.lt) (flankEmbedding_no_original_joint F b)
  left
  refine ⟨c, ?_⟩
  intro v hv
  obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
  exact hc _ (Finset.mem_Icc.mpr
    ⟨(flankEmbedding F).monotone hl, (flankEmbedding F).monotone hr⟩)

def flankInclusion : NecklaceCode.Hom.{u} (flankCode F) T where
  map := orderLift (T := flankCode F) (U := T)
    (flankEmbedding F).toOrderHom (flankEmbedding_beadCondition F)
  first := by
    apply T.verticesEquiv.injective
    have h := orderLift_vertices (T := flankCode F) (U := T) (flankEmbedding F).toOrderHom
      (flankEmbedding_beadCondition F) (ULift.up 0 : Vertices.{u} (flankCode F))
    change _ = ULift.up (flankEmbedding F 0) at h
    rw [flankEmbedding_first] at h
    simpa only [mapVertices, first, flankEmbedding_first, Equiv.apply_symm_apply] using h
  last := by
    apply T.verticesEquiv.injective
    have h := orderLift_vertices (T := flankCode F) (U := T) (flankEmbedding F).toOrderHom
      (flankEmbedding_beadCondition F)
      (ULift.up (Fin.last (flankLen F)) : Vertices.{u} (flankCode F))
    change _ = ULift.up (flankEmbedding F (Fin.last (flankLen F))) at h
    rw [flankEmbedding_last] at h
    simpa only [mapVertices, last, flankEmbedding_last, Equiv.apply_symm_apply] using h

theorem flankInclusion_vertex (v : Vertices.{u} (flankCode F)) :
    mapVertices (flankInclusion F).map v = flankVertex F v :=
  orderLift_vertices (T := flankCode F) (U := T) (flankEmbedding F).toOrderHom
    (flankEmbedding_beadCondition F) v

theorem flankInclusion_ambient :
    (flankInclusion F).map ≫ T.inclusion = ambientOrderMap (flankEmbedding F).toOrderHom :=
  orderLift_inclusion (T := flankCode F) (U := T) (flankEmbedding F).toOrderHom
    (flankEmbedding_beadCondition F)

theorem flankInclusion_flag : NecklaceCode.Flag.map (flankInclusion F) (flankFlag F) = F := by
  apply NecklaceCode.Flag.ext
  intro i
  change mapVertices (flankInclusion F).map '' (flankFlag F).chain i = F.chain i
  have hmap : mapVertices (flankInclusion F).map = flankVertex F :=
    funext (flankInclusion_vertex F)
  rw [hmap]
  exact flankVertex_image F i

end

end DaggerOriginalFlagFlankification
