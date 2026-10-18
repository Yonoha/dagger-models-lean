import OriginalFlagFlankedSurjections
import OriginalFlagNormalizedBeads
import ChosenNecklaceMapInclusion

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
variable (c : T.Bead) (hc : orderMap f.map c.left < orderMap f.map c.right)

def flankedBeadOrder :
    Fin (c.length + 1) →o Fin ((flankedImageBead F G f hfg hF hG c hc).length + 1) where
  toFun v :=
    let d := flankedImageBead F G f hfg hF hG c hc
    (d.interval.orderIsoOfFin d.card_interval).symm
      ⟨orderMap f.map (c.embedding v), Finset.mem_Icc.mpr
        ⟨(orderMap f.map).monotone
            (Finset.mem_Icc.mp (Finset.orderEmbOfFin_mem c.interval c.card_interval v)).1,
          (orderMap f.map).monotone
            (Finset.mem_Icc.mp (Finset.orderEmbOfFin_mem c.interval c.card_interval v)).2⟩⟩
  monotone' _ _ hvw :=
    ((flankedImageBead F G f hfg hF hG c hc).interval.orderIsoOfFin
      (flankedImageBead F G f hfg hF hG c hc).card_interval).symm.monotone
        ((orderMap f.map).monotone (c.embedding.monotone hvw))

theorem flankedBeadOrder_embedding (v : Fin (c.length + 1)) :
    (flankedImageBead F G f hfg hF hG c hc).embedding
        (flankedBeadOrder F G f hfg hF hG c hc v) =
      orderMap f.map (c.embedding v) := by
  dsimp only [flankedBeadOrder]
  exact congrArg Subtype.val
    (((flankedImageBead F G f hfg hF hG c hc).interval.orderIsoOfFin
      (flankedImageBead F G f hfg hF hG c hc).card_interval).apply_symm_apply _)

theorem flankedBeadOrder_surjective :
    Function.Surjective (flankedBeadOrder F G f hfg hF hG c hc) := by
  intro v
  let d := flankedImageBead F G f hfg hF hG c hc
  by_cases hl : d.embedding v = d.left
  · refine ⟨0, d.embedding.injective ?_⟩
    rw [flankedBeadOrder_embedding, c.embedding_zero, hl]
    rfl
  by_cases hr : d.embedding v = d.right
  · refine ⟨Fin.last c.length, d.embedding.injective ?_⟩
    rw [flankedBeadOrder_embedding, c.embedding_last, hr]
    rfl
  have hmem : d.embedding v ∈ d.interval :=
    Finset.orderEmbOfFin_mem d.interval d.card_interval v
  obtain ⟨hlo, hro⟩ := Finset.mem_Icc.mp hmem
  have hlt : d.left < d.embedding v := lt_of_le_of_ne hlo (fun h => hl h.symm)
  have hrt : d.embedding v < d.right := lt_of_le_of_ne hro hr
  obtain ⟨w, hw⟩ := flanked_arrow_order_surjective F G f hfg hF hG (d.embedding v)
  have hwlo : c.left ≤ w := by
    by_contra hn
    have hh := (orderMap f.map).monotone (le_of_lt (lt_of_not_ge hn))
    rw [hw] at hh
    exact (not_le_of_gt hlt) hh
  have hwro : w ≤ c.right := by
    by_contra hn
    have hh := (orderMap f.map).monotone (le_of_lt (lt_of_not_ge hn))
    rw [hw] at hh
    exact (not_le_of_gt hrt) hh
  let k := (c.interval.orderIsoOfFin c.card_interval).symm
    ⟨w, Finset.mem_Icc.mpr ⟨hwlo, hwro⟩⟩
  have hk : c.embedding k = w := congrArg Subtype.val
    ((c.interval.orderIsoOfFin c.card_interval).apply_symm_apply _)
  refine ⟨k, d.embedding.injective ?_⟩
  rw [flankedBeadOrder_embedding, hk, hw]

/-- Literal simplex operator of this SAME positive bead image, not a chosen abstract epi. -/
def flankedBeadOperator :
    ⦋c.length⦌ ⟶ ⦋(flankedImageBead F G f hfg hF hG c hc).length⦌ :=
  SimplexCategory.Hom.mk (flankedBeadOrder F G f hfg hF hG c hc)

instance flankedBeadOperator_epi : Epi (flankedBeadOperator F G f hfg hF hG c hc) :=
  SimplexCategory.epi_iff_surjective.mpr
    (flankedBeadOrder_surjective F G f hfg hF hG c hc)

/-- Whole triangle: extensionality is used only AFTER the literal target-necklace inclusion. -/
theorem flankedBeadOperator_triangle :
    T.beadSimplex c ≫ f.map =
      SSet.stdSimplex.map (flankedBeadOperator F G f hfg hF hG c hc) ≫
        U.beadSimplex (flankedImageBead F G f hfg hF hG c hc) := by
  apply (cancel_mono U.inclusion).1
  rw [Category.assoc, map_inclusion, ← Category.assoc]
  apply stdSimplex_hom_ext
  intro x
  apply SSet.stdSimplex.ext
  intro i
  change orderMap f.map ((T.inclusion.app _ (T.beadSimplex c |>.app _ x)) i) =
    (U.inclusion.app _
      (U.beadSimplex (flankedImageBead F G f hfg hF hG c hc) |>.app _
        ((SSet.stdSimplex.map
          (flankedBeadOperator F G f hfg hF hG c hc)).app _ x))) i
  rw [c.beadSimplex_inclusion_apply,
    (flankedImageBead F G f hfg hF hG c hc).beadSimplex_inclusion_apply]
  exact (flankedBeadOrder_embedding F G f hfg hF hG c hc (x i)).symm

end

end DaggerOriginalFlagFlankification
