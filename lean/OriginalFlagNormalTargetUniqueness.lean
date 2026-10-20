import OriginalFlagBeadOperatorTargets

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}
variable {P Q : NecklacesOver X a b}
variable (F : Flag.{u} P.code n) (G : Flag.{u} Q.code n)
variable (f g : P ⟶ Q)
variable (hfg : NecklaceCode.Flag.map f.hom F = G)
variable (hgg : NecklaceCode.Flag.map g.hom F = G)
variable (hF : Flanked F) (hG : Flanked G)
variable (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length)

include hfg hgg hF hG hQ in
/-- Ordered offsets, rather than equality of labels in X, fix every ORIGINAL joint image. -/
theorem flanked_normal_joint_images_equal (i : Fin (beadCount P.code + 1)) :
    orderMap f.hom.map (jointEmbedding P.code i) =
      orderMap g.hom.map (jointEmbedding P.code i) := by
  have hh : ∀ (k : ℕ) (hk : k ≤ beadCount P.code),
      orderMap f.hom.map (jointEmbedding P.code ⟨k, by omega⟩) =
        orderMap g.hom.map (jointEmbedding P.code ⟨k, by omega⟩) := by
    intro k
    induction k with
    | zero =>
        intro hk
        rw [show (⟨0, by omega⟩ : Fin (beadCount P.code + 1)) = 0 from Fin.ext rfl]
        rw [jointEmbedding_first, orderMap_first, orderMap_first]
    | succ k ih =>
        intro hk
        let j : Fin (beadCount P.code) := ⟨k, by omega⟩
        let c := jointBead P.code j
        have hl := ih (by omega)
        change orderMap f.hom.map c.left = orderMap g.hom.map c.left at hl
        have hfd := flanked_bead_image_dim F G f hfg hF hG hQ c
        have hgd := flanked_bead_image_dim F G g hgg hF hG hQ c
        have hfl := (orderMap f.hom.map).monotone c.lt.le
        have hgl := (orderMap g.hom.map).monotone c.lt.le
        have hln := congrArg Fin.val hl
        have hr : orderMap f.hom.map c.right = orderMap g.hom.map c.right := by
          apply Fin.ext
          change (orderMap f.hom.map c.left).val ≤ _ at hfl
          change (orderMap g.hom.map c.left).val ≤ _ at hgl
          omega
        exact hr
  exact hh i.val (by have hi := i.isLt; omega)

include hfg hgg hF hG hQ in
theorem flanked_normal_bead_endpoints_equal (c : P.code.Bead) :
    orderMap f.hom.map c.left = orderMap g.hom.map c.left ∧
      orderMap f.hom.map c.right = orderMap g.hom.map c.right := by
  constructor
  · have h := flanked_normal_joint_images_equal F G f g hfg hgg hF hG hQ
      (jointIndex P.code c.left c.left_mem)
    simpa only [jointEmbedding_jointIndex] using h
  · have h := flanked_normal_joint_images_equal F G f g hfg hgg hF hG hQ
      (jointIndex P.code c.right c.right_mem)
    simpa only [jointEmbedding_jointIndex] using h

include hfg hgg hF hG hQ in
/-- All three EZ data stay on the SAME original source bead and SAME ordered target bead. -/
theorem flanked_normal_bead_vertices_equal (c : P.code.Bead)
    (v : Fin (P.code.len + 1)) (hv : v ∈ c.interval) :
    orderMap f.hom.map v = orderMap g.hom.map v := by
  obtain ⟨hl, hr⟩ := flanked_normal_bead_endpoints_equal F G f g hfg hgg hF hG hQ c
  by_cases hc : orderMap f.hom.map c.left = orderMap f.hom.map c.right
  · have hcg : orderMap g.hom.map c.left = orderMap g.hom.map c.right :=
      hl.symm.trans (hc.trans hr)
    calc
      orderMap f.hom.map v = orderMap f.hom.map c.left :=
        (flanked_arrow_collapsed_bead F G f.hom hfg hF hG c hc).2 v hv
      _ = orderMap g.hom.map c.left := hl
      _ = orderMap g.hom.map v :=
        ((flanked_arrow_collapsed_bead F G g.hom hgg hF hG c hcg).2 v hv).symm
  · have hcf : orderMap f.hom.map c.left < orderMap f.hom.map c.right :=
      lt_of_le_of_ne ((orderMap f.hom.map).monotone c.lt.le) hc
    have hcg : orderMap g.hom.map c.left < orderMap g.hom.map c.right := by
      rw [← hl, ← hr]
      exact hcf
    let d := flankedImageBead F G f.hom hfg hF hG c hcf
    have hdg : flankedImageBead F G g.hom hgg hF hG c hcg = d :=
      bead_eq_of_endpoints Q.code hl.symm hr.symm
    let sf := flankedBeadOperatorTo F G f hfg hF hG c hcf d rfl
    let sg := flankedBeadOperatorTo F G g hgg hF hG c hcg d hdg
    letI : Epi sf := flankedBeadOperatorTo_epi F G f hfg hF hG c hcf d rfl
    have hfs : beadElement P c = X.map sf.op (beadElement Q d) :=
      flankedBeadOperatorTo_element F G f hfg hF hG c hcf d rfl
    have hgs : beadElement P c = X.map sg.op (beadElement Q d) :=
      flankedBeadOperatorTo_element F G g hgg hF hG c hcg d hdg
    have hoperators : sf = sg := X.unique_nonDegenerate_map (beadElement P c)
      sf ⟨beadElement Q d, hQ d⟩ hfs sg ⟨beadElement Q d, hQ d⟩ hgs
    let k := (c.interval.orderIsoOfFin c.card_interval).symm ⟨v, hv⟩
    have hk : c.embedding k = v := congrArg Subtype.val
      ((c.interval.orderIsoOfFin c.card_interval).apply_symm_apply _)
    rw [← hk]
    calc
      orderMap f.hom.map (c.embedding k) = d.embedding (sf.toOrderHom k) :=
        (flankedBeadOperatorTo_embedding F G f hfg hF hG c hcf d rfl k).symm
      _ = d.embedding (sg.toOrderHom k) :=
        congrArg d.embedding (SimplexCategory.congr_toOrderHom_apply hoperators k)
      _ = orderMap g.hom.map (c.embedding k) :=
        flankedBeadOperatorTo_embedding F G g hgg hF hG c hcg d hdg k

include hfg hgg hF hG hQ in
theorem flanked_normal_order_maps_equal : orderMap f.hom.map = orderMap g.hom.map := by
  ext v
  by_cases hv : v = 0
  · subst v
    rw [orderMap_first, orderMap_first]
  · obtain ⟨c, hc⟩ := P.code.exists_bead_interval v hv
    exact congrArg Fin.val
      (flanked_normal_bead_vertices_equal F G f g hfg hgg hF hG hQ c v hc)

include hfg hgg hF hG hQ in
/-- The whole original over-X functor arrow, not merely equality after Q.map. -/
theorem flanked_normal_over_hom_unique : f = g := by
  apply NecklacesOver.Hom.ext
  apply NecklaceCode.Hom.ext
  apply hom_ext_vertices
  funext v
  apply ULift.ext
  exact congrArg (fun r : Fin (P.code.len + 1) →o Fin (Q.code.len + 1) ↦ r v.down)
    (flanked_normal_order_maps_equal F G f g hfg hgg hF hG hQ)

/-- D2 on the ACTUAL FlankedDegree, including all flags and all proof-bearing arrow fields. -/
theorem flankedDegree_hom_unique (p q : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f g : p ⟶ q) : f = g := by
  apply ObjectProperty.hom_ext
  apply Subtype.ext
  exact flanked_normal_over_hom_unique p.obj.2 q.obj.2 f.hom.val g.hom.val
    f.hom.property g.hom.property p.property q.property hq

end

end DaggerOriginalFlagFlankification
