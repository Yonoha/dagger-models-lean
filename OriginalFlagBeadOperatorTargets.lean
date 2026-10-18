import OriginalFlagBeadImageDimensions

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}
variable {P Q : NecklacesOver X a b}
variable (F : Flag.{u} P.code n) (G : Flag.{u} Q.code n)
variable (f : P ⟶ Q) (hfg : NecklaceCode.Flag.map f.hom F = G)
variable (hF : Flanked F) (hG : Flanked G)
variable (c : P.code.Bead)
variable (hc : orderMap f.hom.map c.left < orderMap f.hom.map c.right)
variable (d : Q.code.Bead) (hd : flankedImageBead F G f.hom hfg hF hG c hc = d)

/-- Only the actual bead equality is used to put the literal operator at the SAME target. -/
def flankedBeadOperatorTo : ⦋c.length⦌ ⟶ ⦋d.length⦌ :=
  flankedBeadOperator F G f.hom hfg hF hG c hc ≫
    eqToHom (congrArg (fun e : Q.code.Bead ↦ ⦋e.length⦌) hd)

instance flankedBeadOperatorTo_epi :
    Epi (flankedBeadOperatorTo F G f hfg hF hG c hc d hd) := by
  dsimp only [flankedBeadOperatorTo]
  infer_instance

theorem flankedBeadOperatorTo_embedding (v : Fin (c.length + 1)) :
    d.embedding ((flankedBeadOperatorTo F G f hfg hF hG c hc d hd).toOrderHom v) =
      orderMap f.hom.map (c.embedding v) := by
  cases hd
  simpa only [flankedBeadOperatorTo, eqToHom_refl, Category.comp_id] using
    flankedBeadOrder_embedding F G f.hom hfg hF hG c hc v

theorem flankedBeadOperatorTo_triangle :
    P.code.beadSimplex c ≫ f.hom.map =
      SSet.stdSimplex.map (flankedBeadOperatorTo F G f hfg hF hG c hc d hd) ≫
        Q.code.beadSimplex d := by
  cases hd
  simpa only [flankedBeadOperatorTo, eqToHom_refl, Category.comp_id] using
    flankedBeadOperator_triangle F G f.hom hfg hF hG c hc

theorem flankedBeadOperatorTo_element :
    beadElement P c =
      X.map (flankedBeadOperatorTo F G f hfg hF hG c hc d hd).op (beadElement Q d) := by
  cases hd
  simpa only [flankedBeadOperatorTo, eqToHom_refl, Category.comp_id] using
    flanked_positive_bead_element F G f hfg hF hG c hc

end

end DaggerOriginalFlagFlankification
