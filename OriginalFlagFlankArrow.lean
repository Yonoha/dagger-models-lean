import OriginalFlagArrowData

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {T U : NecklaceCode} {n : ℕ}
variable (F : Flag.{u} T n) (G : Flag.{u} U n)
variable (f : NecklaceCode.Hom.{u} T U) (hfg : NecklaceCode.Flag.map f F = G)

theorem flankVertex_injective : Function.Injective (flankVertex F) := by
  intro v w h
  apply ULift.ext
  exact (flankEmbedding F).injective (congrArg ULift.down h)

/-- Every new target joint has an actual preimage in the original first flag set. -/
theorem restrictedOrder_joint_preimage (v : Fin (flankLen G + 1))
    (hv : v ∈ (flankCode G).joints) :
    ∃ k ∈ (flankCode F).joints, restrictedOrder F G f hfg k = v := by
  have hv0 : ULift.up (flankEmbedding G v) ∈ G.chain 0 :=
    (mem_selectedJoints G _).mp (Finset.mem_filter.mp hv).2
  rw [← flagged_arrow_image F G f hfg 0] at hv0
  obtain ⟨w, hw, he⟩ := hv0
  have hwJ : w.down ∈ selectedJoints F := by
    apply (mem_selectedJoints F _).mpr
    simpa using hw
  have hwV := selectedJoints_subset F hwJ
  let k := ((selectedVertices F).orderIsoOfFin (flank_card F)).symm ⟨w.down, hwV⟩
  have hek : flankEmbedding F k = w.down := congrArg Subtype.val
    (((selectedVertices F).orderIsoOfFin (flank_card F)).apply_symm_apply ⟨w.down, hwV⟩)
  refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hek.symm ▸ hwJ⟩, ?_⟩
  apply (flankEmbedding G).injective
  rw [restrictedOrder_square, hek]
  change (mapVertices f.map (ULift.up w.down)).down = flankEmbedding G v
  simpa using congrArg ULift.down he

theorem restrictedOrder_no_joint (b : (flankCode F).Bead)
    (v : Fin (flankLen G + 1)) (hv : v ∈ (flankCode G).joints)
    (hl : restrictedOrder F G f hfg b.left < v)
    (hr : v < restrictedOrder F G f hfg b.right) : False := by
  obtain ⟨k, hk, he⟩ := restrictedOrder_joint_preimage F G f hfg v hv
  have hleft : b.left < k := by
    by_contra h
    have hh := (restrictedOrder F G f hfg).monotone (le_of_not_gt h)
    rw [he] at hh
    exact (not_le_of_gt hl) hh
  have hright : k < b.right := by
    by_contra h
    have hh := (restrictedOrder F G f hfg).monotone (le_of_not_gt h)
    rw [he] at hh
    exact (not_le_of_gt hr) hh
  exact b.no_joint k hk hleft hright

/-- No positive-image bead crosses a target joint; constant beads remain allowed. -/
theorem restrictedOrder_beadCondition :
    BeadImageCondition (T := flankCode F) (U := flankCode G)
      (restrictedOrder F G f hfg) := by
  intro b
  let r := restrictedOrder F G f hfg
  have hlr : r b.left ≤ r b.right := r.monotone b.lt.le
  by_cases he : r b.left = r b.right
  · right
    refine ⟨r b.left, ?_⟩
    intro v hv
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
    exact le_antisymm ((r.monotone hr).trans he.symm.le) (r.monotone hl)
  · obtain ⟨c, hc⟩ := interval_in_original_bead (flankCode G)
      (r b.left) (r b.right) (lt_of_le_of_ne hlr he)
      (restrictedOrder_no_joint F G f hfg b)
    left
    refine ⟨c, ?_⟩
    intro v hv
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
    exact hc _ (Finset.mem_Icc.mpr ⟨r.monotone hl, r.monotone hr⟩)

def flankArrow : NecklaceCode.Hom.{u} (flankCode F) (flankCode G) where
  map := orderLift (T := flankCode F) (U := flankCode G)
    (restrictedOrder F G f hfg) (restrictedOrder_beadCondition F G f hfg)
  first := by
    apply (flankCode G).verticesEquiv.injective
    have h := orderLift_vertices (T := flankCode F) (U := flankCode G)
      (restrictedOrder F G f hfg) (restrictedOrder_beadCondition F G f hfg)
      (ULift.up 0 : Vertices.{u} (flankCode F))
    change _ = ULift.up (restrictedOrder F G f hfg 0) at h
    rw [restrictedOrder_first] at h
    simpa only [mapVertices, first, Equiv.apply_symm_apply] using h
  last := by
    apply (flankCode G).verticesEquiv.injective
    have h := orderLift_vertices (T := flankCode F) (U := flankCode G)
      (restrictedOrder F G f hfg) (restrictedOrder_beadCondition F G f hfg)
      (ULift.up (Fin.last (flankLen F)) : Vertices.{u} (flankCode F))
    change _ = ULift.up (restrictedOrder F G f hfg (Fin.last (flankLen F))) at h
    rw [restrictedOrder_last] at h
    simpa only [mapVertices, last, Equiv.apply_symm_apply] using h

theorem flankArrow_vertices (v : Vertices.{u} (flankCode F)) :
    mapVertices (flankArrow F G f hfg).map v =
      ULift.up (restrictedOrder F G f hfg v.down) :=
  orderLift_vertices (T := flankCode F) (U := flankCode G)
    (restrictedOrder F G f hfg) (restrictedOrder_beadCondition F G f hfg) v

theorem flankArrow_vertex_square (v : Vertices.{u} (flankCode F)) :
    flankVertex G (mapVertices (flankArrow F G f hfg).map v) =
      mapVertices f.map (flankVertex F v) := by
  rw [flankArrow_vertices]
  apply ULift.ext
  exact restrictedOrder_square F G f hfg v.down

/-- This is an equality of the actual whole simplicial maps, at every degree. -/
theorem flankArrow_square :
    (flankArrow F G f hfg).map ≫ (flankInclusion G).map =
      (flankInclusion F).map ≫ f.map := by
  apply hom_ext_vertices
  funext v
  rw [mapVertices_comp, mapVertices_comp]
  change mapVertices (flankInclusion G).map
      (mapVertices (flankArrow F G f hfg).map v) =
    mapVertices f.map (mapVertices (flankInclusion F).map v)
  rw [flankInclusion_vertex, flankInclusion_vertex]
  exact flankArrow_vertex_square F G f hfg v

theorem flankArrow_flag :
    NecklaceCode.Flag.map (flankArrow F G f hfg) (flankFlag F) = flankFlag G := by
  apply NecklaceCode.Flag.ext
  intro i
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change flankVertex G (mapVertices (flankArrow F G f hfg).map w) ∈ G.chain i
    rw [flankArrow_vertex_square, ← flagged_arrow_image F G f hfg i]
    exact ⟨flankVertex F w, hw, rfl⟩
  · intro hv
    change flankVertex G v ∈ G.chain i at hv
    rw [← flagged_arrow_image F G f hfg i] at hv
    obtain ⟨w, hw, he⟩ := hv
    rw [← flankVertex_image F i] at hw
    obtain ⟨k, hk, hek⟩ := hw
    refine ⟨k, hk, ?_⟩
    apply flankVertex_injective G
    rw [flankArrow_vertex_square, hek]
    exact he

end

end DaggerOriginalFlagFlankification
