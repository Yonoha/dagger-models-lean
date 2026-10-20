import OriginalFlagSurvivingBeads
import OriginalFlagNormalizedDegree
import ChosenNecklacePointMaps

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

private theorem bead_length_difference {T : NecklaceCode} (c : T.Bead) :
    c.length = c.right.val - c.left.val := by
  have h := c.lt
  simp only [Bead.length, Bead.interval, Fin.card_Icc]
  change c.left.val < c.right.val at h
  omega

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}
variable {P Q : NecklacesOver X a b}
variable (F : Flag.{u} P.code n) (G : Flag.{u} Q.code n)
variable (f : P ⟶ Q) (hfg : NecklaceCode.Flag.map f.hom F = G)
variable (hF : Flanked F) (hG : Flanked G)

include hfg hF hG in
/-- A collapsed bead has the SAME full map at its actual image joint, in every degree. -/
theorem flanked_collapsed_bead_triangle (c : P.code.Bead)
    (hc : orderMap f.hom.map c.left = orderMap f.hom.map c.right) :
    P.code.beadSimplex c ≫ f.hom.map =
      SSet.stdSimplex.map (SimplexCategory.const ⦋c.length⦌ ⦋0⦌ 0) ≫
        pointAt Q.code (ULift.up (orderMap f.hom.map c.left)) := by
  apply (cancel_mono Q.code.inclusion).1
  rw [Category.assoc, map_inclusion, ← Category.assoc]
  apply stdSimplex_hom_ext
  intro x
  apply SSet.stdSimplex.ext
  intro i
  change orderMap f.hom.map
      ((P.code.inclusion.app _ (P.code.beadSimplex c |>.app _ x)) i) =
    Q.code.inclusion.app _
      ((pointAt Q.code (ULift.up (orderMap f.hom.map c.left))).app _
        ((SSet.stdSimplex.map (SimplexCategory.const ⦋c.length⦌ ⦋0⦌ 0)).app _ x)) i
  rw [c.beadSimplex_inclusion_apply, pointAt_inclusion_apply]
  exact (flanked_arrow_collapsed_bead F G f.hom hfg hF hG c hc).2 _
    (Finset.orderEmbOfFin_mem c.interval c.card_interval (x i))

theorem flanked_positive_bead_element (c : P.code.Bead)
    (hc : orderMap f.hom.map c.left < orderMap f.hom.map c.right) :
    beadElement P c =
      X.map (flankedBeadOperator F G f.hom hfg hF hG c hc).op
        (beadElement Q (flankedImageBead F G f.hom hfg hF hG c hc)) := by
  have ht : P.code.beadSimplex c ≫ P.map =
      SSet.stdSimplex.map (flankedBeadOperator F G f.hom hfg hF hG c hc) ≫
        Q.code.beadSimplex (flankedImageBead F G f.hom hfg hF hG c hc) ≫ Q.map := by
    rw [← f.w, ← Category.assoc, flankedBeadOperator_triangle, Category.assoc]
  rw [← SSet.yonedaEquiv.symm_apply_apply
    (Q.code.beadSimplex (flankedImageBead F G f.hom hfg hF hG c hc) ≫ Q.map)] at ht
  calc
    beadElement P c = SSet.yonedaEquiv
        (SSet.stdSimplex.map (flankedBeadOperator F G f.hom hfg hF hG c hc) ≫
          SSet.yonedaEquiv.symm
            (beadElement Q (flankedImageBead F G f.hom hfg hF hG c hc))) :=
      congrArg SSet.yonedaEquiv ht
    _ = _ := by
      rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
      rfl

def flankedPositiveBeadData (c : P.code.Bead)
    (hc : orderMap f.hom.map c.left < orderMap f.hom.map c.right)
    (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length) :
    NondegenerateBeadData P c where
  dim := (flankedImageBead F G f.hom hfg hF hG c hc).length
  operator := flankedBeadOperator F G f.hom hfg hF hG c hc
  epi := flankedBeadOperator_epi F G f.hom hfg hF hG c hc
  simplex := ⟨beadElement Q _, hQ _⟩
  fac := flanked_positive_bead_element F G f hfg hF hG c hc

def flankedCollapsedBeadData (c : P.code.Bead)
    (hc : orderMap f.hom.map c.left = orderMap f.hom.map c.right) :
    NondegenerateBeadData P c where
  dim := 0
  operator := SimplexCategory.const ⦋c.length⦌ ⦋0⦌ 0
  epi := SimplexCategory.epi_iff_surjective.mpr (by
    change Function.Surjective (fun _ : Fin (c.length + 1) ↦ (0 : Fin 1))
    intro v
    exact ⟨0, Subsingleton.elim _ _⟩)
  simplex := ⟨SSet.yonedaEquiv
      (pointAt Q.code (ULift.up (orderMap f.hom.map c.left)) ≫ Q.map), by
    rw [X.nondegenerate_zero]
    exact Set.mem_univ _⟩
  fac := by
    have ht : P.code.beadSimplex c ≫ P.map =
        SSet.stdSimplex.map (SimplexCategory.const ⦋c.length⦌ ⦋0⦌ 0) ≫
          pointAt Q.code (ULift.up (orderMap f.hom.map c.left)) ≫ Q.map := by
      rw [← f.w, ← Category.assoc,
        flanked_collapsed_bead_triangle F G f hfg hF hG c hc, Category.assoc]
    rw [← SSet.yonedaEquiv.symm_apply_apply
      (pointAt Q.code (ULift.up (orderMap f.hom.map c.left)) ≫ Q.map)] at ht
    calc
      beadElement P c = SSet.yonedaEquiv
          (SSet.stdSimplex.map (SimplexCategory.const ⦋c.length⦌ ⦋0⦌ 0) ≫
            SSet.yonedaEquiv.symm (SSet.yonedaEquiv
              (pointAt Q.code (ULift.up (orderMap f.hom.map c.left)) ≫ Q.map))) :=
        congrArg SSet.yonedaEquiv ht
      _ = _ := by
        rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
        rfl

include hfg hF hG in
/-- EZ fixes EACH ordered source bead's image length, even when target labels repeat. -/
theorem flanked_bead_image_dim
    (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length)
    (c : P.code.Bead) :
    (orderMap f.hom.map c.right).val - (orderMap f.hom.map c.left).val =
      (normalizeBead P c).dim := by
  by_cases hc : orderMap f.hom.map c.left = orderMap f.hom.map c.right
  · have he := beadNormalization_dim_unique P c (normalizeBead P c)
      (flankedCollapsedBeadData F G f hfg hF hG c hc)
    change (normalizeBead P c).dim = 0 at he
    rw [hc, he]
    exact Nat.sub_self _
  · have hp : orderMap f.hom.map c.left < orderMap f.hom.map c.right :=
      lt_of_le_of_ne ((orderMap f.hom.map).monotone c.lt.le) hc
    have he := beadNormalization_dim_unique P c (normalizeBead P c)
      (flankedPositiveBeadData F G f hfg hF hG c hp hQ)
    change (normalizeBead P c).dim =
      (flankedImageBead F G f.hom hfg hF hG c hp).length at he
    rw [he, bead_length_difference]
    rfl

end

end DaggerOriginalFlagFlankification
