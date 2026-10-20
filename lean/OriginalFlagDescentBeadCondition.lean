import OriginalFlagDescentOrder
import OriginalFlagBeadOperatorTargets

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

include hg hF hH in
/-- Every vertex of d lifts in its unique original survivor, not in a chosen unrelated bead. -/
theorem flankedSurvivor_interval_preimage (d : R.code.Bead)
    (v : Fin (R.code.len + 1)) (hv : v ∈ d.interval) :
    ∃ w ∈ (survivingSourceBead F H g.hom hg hF hH d).interval,
      orderMap g.hom.map w = v := by
  let c := survivingSourceBead F H g.hom hg hF hH d
  have hc := survivingSourceBead_positive F H g.hom hg hF hH d
  have hd := survivingSourceBead_image F H g.hom hg hF hH d
  let s := flankedBeadOperatorTo F H g hg hF hH c hc d hd
  letI : Epi s := flankedBeadOperatorTo_epi F H g hg hF hH c hc d hd
  let k := (d.interval.orderIsoOfFin d.card_interval).symm ⟨v, hv⟩
  have hk : d.embedding k = v := congrArg Subtype.val
    ((d.interval.orderIsoOfFin d.card_interval).apply_symm_apply _)
  obtain ⟨z, hz⟩ := SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi s) k
  refine ⟨c.embedding z, Finset.orderEmbOfFin_mem c.interval c.card_interval z, ?_⟩
  calc
    orderMap g.hom.map (c.embedding z) = d.embedding (s.toOrderHom z) :=
      (flankedBeadOperatorTo_embedding F H g hg hF hH c hc d hd z).symm
    _ = d.embedding k := congrArg d.embedding hz
    _ = v := hk

include hf hg hF hG hH in
/-- Original survivor/operator coverage verifies every whole bead of the descended order. -/
theorem flankedDescentOrder_beadCondition
    (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length) :
    BeadImageCondition (T := R.code) (U := Q.code)
      (flankedDescentOrder F H f g hg hF hH) := by
  intro d
  let c := survivingSourceBead F H g.hom hg hF hH d
  by_cases hc : orderMap f.hom.map c.left = orderMap f.hom.map c.right
  · right
    refine ⟨orderMap f.hom.map c.left, ?_⟩
    intro v hv
    obtain ⟨w, hw, he⟩ := flankedSurvivor_interval_preimage F H g hg hF hH d v hv
    calc
      flankedDescentOrder F H f g hg hF hH v = orderMap f.hom.map w := by
        rw [← he]
        exact flankedDescentOrder_factor F G H f g hf hg hF hG hH hQ w
      _ = orderMap f.hom.map c.left :=
        (flanked_arrow_collapsed_bead F G f.hom hf hF hG c hc).2 w hw
  · have hp : orderMap f.hom.map c.left < orderMap f.hom.map c.right :=
      lt_of_le_of_ne ((orderMap f.hom.map).monotone c.lt.le) hc
    left
    let e := flankedImageBead F G f.hom hf hF hG c hp
    refine ⟨e, ?_⟩
    intro v hv
    obtain ⟨w, hw, he⟩ := flankedSurvivor_interval_preimage F H g hg hF hH d v hv
    have hlw := (Finset.mem_Icc.mp hw).1
    have hwr := (Finset.mem_Icc.mp hw).2
    have hval : flankedDescentOrder F H f g hg hF hH v = orderMap f.hom.map w := by
      rw [← he]
      exact flankedDescentOrder_factor F G H f g hf hg hF hG hH hQ w
    rw [hval]
    exact Finset.mem_Icc.mpr
      ⟨(orderMap f.hom.map).monotone hlw, (orderMap f.hom.map).monotone hwr⟩

end

end DaggerOriginalFlagFlankification
