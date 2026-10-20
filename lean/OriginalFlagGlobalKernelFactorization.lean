import OriginalFlagBeadKernelFactorization
import ChosenNecklaceCoverage

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

include hf hg hF hG hH in
/-- ONE original bead contains the adjacent original vertices, even across a chosen joint. -/
theorem flanked_normal_adjacent_kernel
    (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length)
    (i : Fin P.code.len)
    (hi : orderMap g.hom.map i.castSucc = orderMap g.hom.map i.succ) :
    orderMap f.hom.map i.castSucc = orderMap f.hom.map i.succ := by
  obtain ⟨c, hl, hr⟩ := P.code.exists_bead_at i.succ (by simp)
  have hleft : c.left ≤ i.castSucc := by
    simp only [Fin.lt_def, Fin.val_succ] at hl
    change c.left.val ≤ i.val
    omega
  have hv : i.castSucc ∈ c.interval :=
    Finset.mem_Icc.mpr ⟨hleft, (Fin.castSucc_le_succ i).trans hr⟩
  have hw : i.succ ∈ c.interval := Finset.mem_Icc.mpr ⟨hl.le, hr⟩
  let v := (c.interval.orderIsoOfFin c.card_interval).symm ⟨i.castSucc, hv⟩
  let w := (c.interval.orderIsoOfFin c.card_interval).symm ⟨i.succ, hw⟩
  have hcv : c.embedding v = i.castSucc := congrArg Subtype.val
    ((c.interval.orderIsoOfFin c.card_interval).apply_symm_apply _)
  have hcw : c.embedding w = i.succ := congrArg Subtype.val
    ((c.interval.orderIsoOfFin c.card_interval).apply_symm_apply _)
  have hgw : orderMap g.hom.map (c.embedding v) =
      orderMap g.hom.map (c.embedding w) := by
    rw [hcv, hcw]
    exact hi
  have h := flanked_normal_bead_kernel F G H f g hf hg hF hG hH hQ c v w hgw
  simpa only [hcv, hcw] using h

include hf hg hF hG hH in
/-- The full kernel on SAME original vertices; monotonicity handles every intervening joint. -/
theorem flanked_normal_order_kernel
    (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length)
    (v w : Fin (P.code.len + 1))
    (hvw : orderMap g.hom.map v = orderMap g.hom.map w) :
    orderMap f.hom.map v = orderMap f.hom.map w := by
  have ordered : ∀ (v w : Fin (P.code.len + 1)), v ≤ w →
      orderMap g.hom.map v = orderMap g.hom.map w →
        orderMap f.hom.map v = orderMap f.hom.map w := by
    intro v w hvw hgw
    have all : ∀ k : Fin (P.code.len + 1), v ≤ k → k ≤ w →
        orderMap f.hom.map v = orderMap f.hom.map k := by
      intro k
      induction k using Fin.induction with
      | zero =>
          intro hv hk
          have h : v = 0 := le_antisymm hv (Fin.zero_le v)
          rw [h]
      | succ i ih =>
          intro hvi hiw
          by_cases hvold : v ≤ i.castSucc
          · have hiold : i.castSucc ≤ w := (Fin.castSucc_le_succ i).trans hiw
            have hgadj : orderMap g.hom.map i.castSucc =
                orderMap g.hom.map i.succ := by
              apply le_antisymm ((orderMap g.hom.map).monotone (Fin.castSucc_le_succ i))
              calc
                orderMap g.hom.map i.succ ≤ orderMap g.hom.map w :=
                  (orderMap g.hom.map).monotone hiw
                _ = orderMap g.hom.map v := hgw.symm
                _ ≤ orderMap g.hom.map i.castSucc :=
                  (orderMap g.hom.map).monotone hvold
            exact (ih hvold hiold).trans
              (flanked_normal_adjacent_kernel F G H f g hf hg hF hG hH hQ i hgadj)
          · have h : v = i.succ := by
              apply Fin.ext
              change v.val ≤ i.val + 1 at hvi
              change ¬v.val ≤ i.val at hvold
              change v.val = i.val + 1
              omega
            rw [h]
    exact all w hvw le_rfl
  rcases le_total v w with h | h
  · exact ordered v w h hvw
  · exact (ordered w v h hvw.symm).symm

/-- A point source has exactly its original vertex; no positive-bead existence is requested. -/
theorem point_code_kernel (hP : P.code.len = 0) (v w : Fin (P.code.len + 1)) :
    orderMap f.hom.map v = orderMap f.hom.map w := by
  have h : v = w := by
    apply Fin.ext
    have hv := v.isLt
    have hw := w.isLt
    omega
  rw [h]

end

end DaggerOriginalFlagFlankification
