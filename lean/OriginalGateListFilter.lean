import OriginalGateListDeletion

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}}

/-- Forget rejected gates using the original adjacent composition, keeping retained factors. -/
def gateListFilter (keep : X.obj (op ⦋0⦌) → Bool) (a b : X.obj (op ⦋0⦌)) :
    ∀ vs, gateListHom a b vs ⟶ gateListHom a b (vs.filter keep)
  | [] => 𝟙 _
  | v :: vs => if h : keep v then
      (𝟙 (flagHom X a v) ⊗ₘ gateListFilter keep v b vs) ≫
        eqToHom (congrArg (gateListHom a b) (List.filter_cons_of_pos h).symm)
    else
      (gateListDropFirst a v b vs ≫ gateListFilter keep a b vs) ≫
        eqToHom (congrArg (gateListHom a b) (List.filter_cons_of_neg h).symm)

/-- Relabeling equal lists leaves the original iterated composition unchanged. -/
theorem gateListComposition_eqToHom (a b : X.obj (op ⦋0⦌))
    {vs ws : List (X.obj (op ⦋0⦌))} (h : vs = ws) :
    eqToHom (congrArg (gateListHom a b) h) ≫ gateListComposition a b ws =
      gateListComposition a b vs := by
  subst ws
  rfl

/-- Arbitrary simultaneous gate removal preserves the original total composite. -/
theorem gateListFilter_comp (keep : X.obj (op ⦋0⦌) → Bool) (a b : X.obj (op ⦋0⦌))
    (vs : List (X.obj (op ⦋0⦌))) :
    gateListFilter keep a b vs ≫ gateListComposition a b (vs.filter keep) =
      gateListComposition a b vs := by
  induction vs generalizing a with
  | nil => rfl
  | cons v vs ih =>
    by_cases h : keep v
    · simp only [gateListFilter, dif_pos h]
      rw [Category.assoc,
        gateListComposition_eqToHom a b (List.filter_cons_of_pos h).symm]
      apply NatTrans.ext
      funext q x
      exact congrArg (flagCompApp x.1) (congrFun (NatTrans.congr_app (ih v) q) x.2)
    · simp only [gateListFilter, dif_neg h]
      rw [Category.assoc,
        gateListComposition_eqToHom a b (List.filter_cons_of_neg h).symm,
        Category.assoc, ih, gateListDropFirst_comp]

end

end DaggerOriginalProductGadget
