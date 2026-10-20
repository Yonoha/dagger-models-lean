import OriginalFlagGlobalKernelFactorization
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.EpiMono

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

/-- The original finite vertex map, now regarded only as a simplex operator. -/
def flankedOrderArrow : ⦋P.code.len⦌ ⟶ ⦋R.code.len⦌ :=
  SimplexCategory.mkHom (orderMap g.hom.map)

include hg hF hH in
theorem flankedOrderArrow_epi : Epi (flankedOrderArrow g) :=
  SimplexCategory.epi_iff_surjective.mpr
    (flanked_arrow_order_surjective F H g.hom hg hF hH)

/-- A monotone section only: no necklace or endpoint property is asserted for this section. -/
def flankedOrderSection : Fin (R.code.len + 1) →o Fin (P.code.len + 1) := by
  letI : Epi (flankedOrderArrow g) := flankedOrderArrow_epi F H g hg hF hH
  letI : IsSplitEpi (flankedOrderArrow g) := isSplitEpi_of_epi (flankedOrderArrow g)
  exact (section_ (flankedOrderArrow g)).toOrderHom

theorem flankedOrderSection_right_inverse (v : Fin (R.code.len + 1)) :
    orderMap g.hom.map (flankedOrderSection F H g hg hF hH v) = v := by
  letI : Epi (flankedOrderArrow g) := flankedOrderArrow_epi F H g hg hF hH
  letI : IsSplitEpi (flankedOrderArrow g) := isSplitEpi_of_epi (flankedOrderArrow g)
  have h := SimplexCategory.congr_toOrderHom_apply
    (IsSplitEpi.id (flankedOrderArrow g)) v
  exact h

/-- Descent uses the SAME f and g vertex functions and the original finite simplex section. -/
def flankedDescentOrder : Fin (R.code.len + 1) →o Fin (Q.code.len + 1) :=
  (orderMap f.hom.map).comp (flankedOrderSection F H g hg hF hH)

include hf hg hF hG hH in
theorem flankedDescentOrder_factor
    (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length)
    (v : Fin (P.code.len + 1)) :
    flankedDescentOrder F H f g hg hF hH (orderMap g.hom.map v) =
      orderMap f.hom.map v := by
  exact flanked_normal_order_kernel F G H f g hf hg hF hG hH hQ
    (flankedOrderSection F H g hg hF hH (orderMap g.hom.map v)) v
    (flankedOrderSection_right_inverse F H g hg hF hH _)

include hf hg hF hG hH in
theorem flankedDescentOrder_first
    (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length) :
    flankedDescentOrder F H f g hg hF hH 0 = 0 := by
  have h := flankedDescentOrder_factor F G H f g hf hg hF hG hH hQ 0
  simpa only [orderMap_first] using h

include hf hg hF hG hH in
theorem flankedDescentOrder_last
    (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length) :
    flankedDescentOrder F H f g hg hF hH (Fin.last R.code.len) =
      Fin.last Q.code.len := by
  have h := flankedDescentOrder_factor F G H f g hf hg hF hG hH hQ
    (Fin.last P.code.len)
  simpa only [orderMap_last] using h

end

end DaggerOriginalFlagFlankification
