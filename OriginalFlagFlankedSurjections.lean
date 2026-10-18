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
variable (hF : Flanked F) (hG : Flanked G)

include hfg hF hG in
theorem flanked_arrow_vertex_surjective :
    Function.Surjective (mapVertices f.map) := by
  rcases hF with ⟨_hFfirst, _hFlast⟩
  intro v
  have hv : v ∈ G.chain (Fin.last n) := by rw [hG.2]; exact Set.mem_univ _
  rw [← flagged_arrow_image F G f hfg (Fin.last n)] at hv
  obtain ⟨w, _hw, he⟩ := hv
  exact ⟨w, he⟩

include hfg hF hG in
theorem flanked_arrow_order_surjective : Function.Surjective (orderMap f.map) := by
  intro v
  obtain ⟨w, hw⟩ := flanked_arrow_vertex_surjective F G f hfg hF hG (ULift.up v)
  refine ⟨w.down, ?_⟩
  exact congrArg ULift.down hw

include hfg hF hG in
theorem flanked_arrow_joint (v : Fin (T.len + 1)) (hv : v ∈ T.joints) :
    orderMap f.map v ∈ U.joints := by
  have hs : (ULift.up v : Vertices.{u} T) ∈ F.chain 0 := by
    rw [hF.1]
    exact hv
  have hi : mapVertices f.map (ULift.up v) ∈ mapVertices f.map '' F.chain 0 :=
    ⟨ULift.up v, hs, rfl⟩
  rw [flagged_arrow_image F G f hfg 0, hG.1] at hi
  exact hi

include hfg hF hG in
theorem flanked_arrow_joint_preimage (v : Fin (U.len + 1)) (hv : v ∈ U.joints) :
    ∃ w ∈ T.joints, orderMap f.map w = v := by
  have hg : (ULift.up v : Vertices.{u} U) ∈ G.chain 0 := by
    rw [hG.1]
    exact hv
  rw [← flagged_arrow_image F G f hfg 0] at hg
  obtain ⟨w, hw, he⟩ := hg
  rw [hF.1] at hw
  exact ⟨w.down, hw, congrArg ULift.down he⟩

include hfg hF hG in
theorem flanked_arrow_joint_image :
    orderMap f.map '' {v | v ∈ T.joints} = {v | v ∈ U.joints} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact flanked_arrow_joint F G f hfg hF hG w hw
  · intro hv
    obtain ⟨w, hw, he⟩ := flanked_arrow_joint_preimage F G f hfg hF hG v hv
    exact ⟨w, hw, he⟩

include hfg hF hG in
theorem flanked_arrow_no_inner_joint (c : T.Bead) (v : Fin (U.len + 1))
    (hv : v ∈ U.joints) (hl : orderMap f.map c.left < v)
    (hr : v < orderMap f.map c.right) : False := by
  obtain ⟨w, hw, he⟩ := flanked_arrow_joint_preimage F G f hfg hF hG v hv
  have hleft : c.left < w := by
    by_contra hn
    have hh := (orderMap f.map).monotone (le_of_not_gt hn)
    rw [he] at hh
    exact (not_le_of_gt hl) hh
  have hright : w < c.right := by
    by_contra hn
    have hh := (orderMap f.map).monotone (le_of_not_gt hn)
    rw [he] at hh
    exact (not_le_of_gt hr) hh
  exact c.no_joint w hw hleft hright

/-- The target bead has precisely the SAME images of the original source bead endpoints. -/
def flankedImageBead (c : T.Bead)
    (hc : orderMap f.map c.left < orderMap f.map c.right) : U.Bead where
  left := orderMap f.map c.left
  right := orderMap f.map c.right
  left_mem := flanked_arrow_joint F G f hfg hF hG c.left c.left_mem
  right_mem := flanked_arrow_joint F G f hfg hF hG c.right c.right_mem
  lt := hc
  no_joint := flanked_arrow_no_inner_joint F G f hfg hF hG c

theorem flankedImageBead_left (c : T.Bead)
    (hc : orderMap f.map c.left < orderMap f.map c.right) :
    (flankedImageBead F G f hfg hF hG c hc).left = orderMap f.map c.left := rfl

theorem flankedImageBead_right (c : T.Bead)
    (hc : orderMap f.map c.left < orderMap f.map c.right) :
    (flankedImageBead F G f hfg hF hG c hc).right = orderMap f.map c.right := rfl

include hfg hF hG in
/-- A collapsed original bead is constant at an actual target JOINT, including loops. -/
theorem flanked_arrow_collapsed_bead (c : T.Bead)
    (hc : orderMap f.map c.left = orderMap f.map c.right) :
    orderMap f.map c.left ∈ U.joints ∧
      ∀ v ∈ c.interval, orderMap f.map v = orderMap f.map c.left := by
  refine ⟨flanked_arrow_joint F G f hfg hF hG c.left c.left_mem, ?_⟩
  intro v hv
  obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
  exact le_antisymm (((orderMap f.map).monotone hr).trans hc.symm.le)
    ((orderMap f.map).monotone hl)

end

end DaggerOriginalFlagFlankification
