import OriginalFlagBeadImageDimensions
import OriginalFlagBeadNormalizationLaws

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}
variable {P Q R : NecklacesOver X a b}
variable (F : Flag.{u} P.code n) (G : Flag.{u} Q.code n) (H : Flag.{u} R.code n)
variable (f : P ⟶ Q) (g : P ⟶ R)
variable (hf : NecklaceCode.Flag.map f.hom F = G)
variable (hg : NecklaceCode.Flag.map g.hom F = H)
variable (hF : Flanked F) (hG : Flanked G) (hH : Flanked H)

/-- Normalize the SAME actual target bead after the SAME source-bead operator. -/
def flankedCompositeBeadData (c : P.code.Bead)
    (hc : orderMap g.hom.map c.left < orderMap g.hom.map c.right) :
    NondegenerateBeadData P c := by
  let d := flankedImageBead F H g.hom hg hF hH c hc
  let e := normalizeBead R d
  let s := flankedBeadOperator F H g.hom hg hF hH c hc
  letI : Epi s := flankedBeadOperator_epi F H g.hom hg hF hH c hc
  letI : Epi e.operator := e.epi
  refine ⟨e.dim, s ≫ e.operator, inferInstance, e.simplex, ?_⟩
  calc
    beadElement P c = X.map s.op (beadElement R d) :=
      flanked_positive_bead_element F H g hg hF hH c hc
    _ = X.map s.op (X.map e.operator.op e.simplex.val) :=
      congrArg (X.map s.op) e.fac
    _ = X.map (s ≫ e.operator).op e.simplex.val :=
      congrFun (X.map_comp e.operator.op s.op).symm e.simplex.val

private theorem normalization_operator_kernel (c : P.code.Bead)
    (d e : NondegenerateBeadData P c) (v w : Fin (c.length + 1))
    (he : e.operator.toOrderHom v = e.operator.toOrderHom w) :
    d.operator.toOrderHom v = d.operator.toOrderHom w := by
  have h := beadNormalization_unique P c d e
  cases h
  exact he

include hf hg hF hG hH in
/-- A bead collapsed by g is also collapsed by f into the SAME normal target. -/
theorem flanked_collapsed_normal_bead
    (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length)
    (c : P.code.Bead)
    (hc : orderMap g.hom.map c.left = orderMap g.hom.map c.right) :
    orderMap f.hom.map c.left = orderMap f.hom.map c.right := by
  have hd := beadNormalization_dim_unique P c (normalizeBead P c)
    (flankedCollapsedBeadData F H g hg hF hH c hc)
  change (normalizeBead P c).dim = 0 at hd
  have he := flanked_bead_image_dim F G f hf hF hG hQ c
  have hl := (orderMap f.hom.map).monotone c.lt.le
  apply Fin.ext
  change (orderMap f.hom.map c.left).val ≤ _ at hl
  rw [hd] at he
  omega

include hf hg hF hG hH in
/-- Same-source EZ proves the kernel implication on EVERY coordinate of an original bead. -/
theorem flanked_normal_bead_kernel
    (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length)
    (c : P.code.Bead) (v w : Fin (c.length + 1))
    (hvw : orderMap g.hom.map (c.embedding v) =
      orderMap g.hom.map (c.embedding w)) :
    orderMap f.hom.map (c.embedding v) = orderMap f.hom.map (c.embedding w) := by
  by_cases hgc : orderMap g.hom.map c.left = orderMap g.hom.map c.right
  · have hfc := flanked_collapsed_normal_bead F G H f g hf hg hF hG hH hQ c hgc
    exact (flanked_arrow_collapsed_bead F G f.hom hf hF hG c hfc).2 _
      (Finset.orderEmbOfFin_mem c.interval c.card_interval v) |>.trans
        ((flanked_arrow_collapsed_bead F G f.hom hf hF hG c hfc).2 _
          (Finset.orderEmbOfFin_mem c.interval c.card_interval w)).symm
  by_cases hfc : orderMap f.hom.map c.left = orderMap f.hom.map c.right
  · exact (flanked_arrow_collapsed_bead F G f.hom hf hF hG c hfc).2 _
      (Finset.orderEmbOfFin_mem c.interval c.card_interval v) |>.trans
        ((flanked_arrow_collapsed_bead F G f.hom hf hF hG c hfc).2 _
          (Finset.orderEmbOfFin_mem c.interval c.card_interval w)).symm
  have hgp : orderMap g.hom.map c.left < orderMap g.hom.map c.right :=
    lt_of_le_of_ne ((orderMap g.hom.map).monotone c.lt.le) hgc
  have hfp : orderMap f.hom.map c.left < orderMap f.hom.map c.right :=
    lt_of_le_of_ne ((orderMap f.hom.map).monotone c.lt.le) hfc
  let dg := flankedImageBead F H g.hom hg hF hH c hgp
  let sg := flankedBeadOperator F H g.hom hg hF hH c hgp
  have hsg : sg.toOrderHom v = sg.toOrderHom w := by
    apply dg.embedding.injective
    exact (flankedBeadOrder_embedding F H g.hom hg hF hH c hgp v).trans
      (hvw.trans (flankedBeadOrder_embedding F H g.hom hg hF hH c hgp w).symm)
  let e := flankedCompositeBeadData F H g hg hF hH c hgp
  have he : e.operator.toOrderHom v = e.operator.toOrderHom w := by
    change (normalizeBead R dg).operator.toOrderHom (sg.toOrderHom v) =
      (normalizeBead R dg).operator.toOrderHom (sg.toOrderHom w)
    rw [hsg]
  let d := flankedPositiveBeadData F G f hf hF hG c hfp hQ
  have hd := normalization_operator_kernel c d e v w he
  change (flankedBeadOperator F G f.hom hf hF hG c hfp).toOrderHom v =
    (flankedBeadOperator F G f.hom hf hF hG c hfp).toOrderHom w at hd
  calc
    orderMap f.hom.map (c.embedding v) =
        (flankedImageBead F G f.hom hf hF hG c hfp).embedding
          ((flankedBeadOperator F G f.hom hf hF hG c hfp).toOrderHom v) :=
      (flankedBeadOrder_embedding F G f.hom hf hF hG c hfp v).symm
    _ = _ := congrArg (flankedImageBead F G f.hom hf hF hG c hfp).embedding hd
    _ = orderMap f.hom.map (c.embedding w) :=
      flankedBeadOrder_embedding F G f.hom hf hF hG c hfp w

end

end DaggerOriginalFlagFlankification
