import OriginalGateBisimplicial

set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} (a b : X.obj (op ⦋0⦌)) (A : Set (X.obj (op ⦋0⦌)))
  (R₀ : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)

/-- A literal gate-index chain and an original Hom simplex satisfying its first gate condition. -/
def gateRawBidegree (q k : SimplexCategoryᵒᵖ) : Type u :=
  Σ gamma : ComposableArrows (FlagGateIndex A R₀) k.unop.len,
    ((flagGateDiagram a b A R₀).obj (gamma.obj 0)).obj q

def gateBidegreeToRaw (q k : SimplexCategoryᵒᵖ) :
    ((gateOuterNerve a b A R₀).obj q).obj k → gateRawBidegree a b A R₀ q k :=
  fun gamma ↦ ⟨gamma ⋙ CategoryOfElements.π (flagGateDegreeDiagram a b A R₀ q),
    (gamma.obj 0).2⟩

/-- All inclusions retain the exact same original simplex along the gate chain. -/
def gateRawToBidegree (q k : SimplexCategoryᵒᵖ) :
    gateRawBidegree a b A R₀ q k → ((gateOuterNerve a b A R₀).obj q).obj k := by
  intro p
  exact {
    obj := fun i ↦ ⟨p.1.obj i, ⟨p.2.val,
      (show (p.1.obj i).val ⊆ (p.1.obj 0).val from
        leOfHom (p.1.map (homOfLE (Fin.zero_le i)))).trans p.2.property⟩⟩
    map := fun f ↦ ⟨p.1.map f, rfl⟩
    map_id := by
      intro i
      apply Subtype.ext
      exact p.1.map_id i
    map_comp := by
      intro i j h f g
      apply Subtype.ext
      exact p.1.map_comp f g
  }

theorem gateBidegreeToRaw_rawTo (q k : SimplexCategoryᵒᵖ)
    (p : gateRawBidegree a b A R₀ q k) :
    gateBidegreeToRaw a b A R₀ q k (gateRawToBidegree a b A R₀ q k p) = p := by
  rfl

theorem gateRawToBidegree_toRaw (q k : SimplexCategoryᵒᵖ)
    (gamma : ((gateOuterNerve a b A R₀).obj q).obj k) :
    gateRawToBidegree a b A R₀ q k (gateBidegreeToRaw a b A R₀ q k gamma) = gamma := by
  have hobj : ∀ i, (gateRawToBidegree a b A R₀ q k
      (gateBidegreeToRaw a b A R₀ q k gamma)).obj i = gamma.obj i := by
    intro i
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext
      (congrArg Subtype.val (gamma.map (homOfLE (Fin.zero_le i))).property)))
  apply CategoryTheory.Functor.hext hobj
  intro i j f
  apply (Subtype.heq_iff_coe_heq (by rw [hobj i, hobj j])
    (by rw [hobj i, hobj j])).2
  rfl

/-- Exact bidegree equivalence, including the original gate-index arrows. -/
def gateBidegreeEquiv (q k : SimplexCategoryᵒᵖ) :
    ((gateOuterNerve a b A R₀).obj q).obj k ≃ gateRawBidegree a b A R₀ q k where
  toFun := gateBidegreeToRaw a b A R₀ q k
  invFun := gateRawToBidegree a b A R₀ q k
  left_inv := gateRawToBidegree_toRaw a b A R₀ q k
  right_inv := gateBidegreeToRaw_rawTo a b A R₀ q k

/-- The outer operator acts on the same original simplex inside its initial gate subcomplex. -/
theorem gateBidegreeToRaw_outer {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (k : SimplexCategoryᵒᵖ) (gamma : ((gateOuterNerve a b A R₀).obj q).obj k) :
    gateBidegreeToRaw a b A R₀ r k (((gateOuterNerve a b A R₀).map α).app k gamma) =
      ⟨(gateBidegreeToRaw a b A R₀ q k gamma).1,
        ((flagGateDiagram a b A R₀).obj (gamma.obj 0).1).map α (gamma.obj 0).2⟩ := rfl

/-- The inner operator restricts the actual index chain. -/
theorem gateBidegreeToRaw_inner_chain (q : SimplexCategoryᵒᵖ)
    {k l : SimplexCategoryᵒᵖ} (β : k ⟶ l)
    (gamma : ((gateOuterNerve a b A R₀).obj q).obj k) :
    (gateBidegreeToRaw a b A R₀ q l (((gateOuterNerve a b A R₀).obj q).map β gamma)).1 =
      (nerve (FlagGateIndex A R₀)).map β (gateBidegreeToRaw a b A R₀ q k gamma).1 := rfl

/-- Selecting a new initial gate transports the first simplex by its actual diagram inclusion. -/
theorem gateBidegreeToRaw_inner_simplex (q : SimplexCategoryᵒᵖ)
    {k l : SimplexCategoryᵒᵖ} (β : k ⟶ l)
    (gamma : ((gateOuterNerve a b A R₀).obj q).obj k) :
    (gateBidegreeToRaw a b A R₀ q l (((gateOuterNerve a b A R₀).obj q).map β gamma)).2 =
      (flagGateDegreeDiagram a b A R₀ q).map
        ((gateBidegreeToRaw a b A R₀ q k gamma).1.map
          (homOfLE (Fin.zero_le ((SimplexCategory.toCat.map β.unop).toFunctor.obj
            (0 : Fin (l.unop.len + 1)))))) (gateBidegreeToRaw a b A R₀ q k gamma).2 := by
  exact (gamma.map (homOfLE (Fin.zero_le
    ((SimplexCategory.toCat.map β.unop).toFunctor.obj
      (0 : Fin (l.unop.len + 1)))))).property.symm

end

end DaggerOriginalProductGadget
