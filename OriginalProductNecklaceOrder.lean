import OriginalProductOrderedEmbedding
import OriginalFlagNormalizedBeadCharts

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- For the existing ordered source necklace, injectivity on original vertices implies Mono. -/
theorem necklace_map_mono_of_vertex_injective {X : SSet.{u}} (T : NecklaceCode)
    (f : T.toSSet ⟶ X) (hf : Function.Injective (f.app (op ⦋0⦌))) : Mono f := by
  constructor
  intro Z g h he
  apply (cancel_mono T.inclusion).1
  apply stdSimplex_hom_ext
  intro z
  exact congrArg (T.inclusion.app (op ⦋0⦌)) (hf
    (congrFun (NatTrans.congr_app he (op ⦋0⦌)) z))

variable {n : ℕ} {factor : Fin n → NecklaceCode}
  {a b : (productSpace.{u} n factor).obj (op ⦋0⦌)}

/-- The monotone vertex function of the actual over-product necklace. -/
def productNecklaceOrder (P : NecklacesOver (productSpace.{u} n factor) a b) :
    Fin (P.code.len + 1) →o ProductVertexOrder.{u} n factor where
  toFun v i := ULift.up (orderMap (P.map ≫ Pi.π (fun i ↦ (factor i).toSSet) i) v)
  monotone' _ _ h i := (orderMap (P.map ≫ Pi.π (fun i ↦ (factor i).toSSet) i)).monotone h

theorem productNecklaceOrder_vertex (P : NecklacesOver (productSpace.{u} n factor) a b)
    (v : Fin (P.code.len + 1)) :
    productNecklaceOrder P v =
      ((productOrderedEmbedding n factor).app (op ⦋0⦌) (vertexImage P v)).obj 0 := rfl

/-- The original Yoneda simplex of a nerve map evaluates at the same specified vertex. -/
theorem orderedNerve_yoneda_vertex {V : Type u} [PartialOrder V] {d : ℕ}
    (f : (Δ[d] : SSet.{u}) ⟶ nerve V) (v : Fin (d + 1)) :
    (SSet.yonedaEquiv f).obj v =
      (f.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm v)).obj 0 := by
  have h := congrFun (f.naturality (SimplexCategory.const ⦋0⦌ ⦋d⦌ v).op)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋d⦌))
  exact (congrArg (fun z ↦ z.obj 0) h).symm

/-- A bead's vertex chart in the ordered embedding is the original global vertex function. -/
theorem productNecklaceOrder_bead (P : NecklacesOver (productSpace.{u} n factor) a b)
    (c : P.code.Bead) (v : Fin (c.length + 1)) :
    productNecklaceOrder P (c.embedding v) =
      ((productOrderedEmbedding n factor).app (op ⦋c.length⦌) (beadElement P c)).obj v := by
  rw [productNecklaceOrder_vertex]
  have h := orderedNerve_yoneda_vertex
    (P.code.beadSimplex c ≫ P.map ≫ productOrderedEmbedding n factor) v
  rw [SSet.yonedaEquiv_comp] at h
  change ((productOrderedEmbedding n factor).app _ (beadElement P c)).obj v = _ at h
  rw [h]
  apply congrArg (fun z ↦ ((productOrderedEmbedding n factor).app (op ⦋0⦌) z).obj 0)
  apply congrArg (P.map.app (op ⦋0⦌))
  exact P.code.verticesEquiv.injective (by
    rw [Equiv.apply_symm_apply, c.beadSimplex_vertex])

/-- Existing Mathlib nondegeneracy makes the actual order map injective on each bead. -/
theorem productNecklaceOrder_bead_injective
    (P : NecklacesOver (productSpace.{u} n factor) a b) (c : P.code.Bead)
    (hc : beadElement P c ∈ (productSpace n factor).nonDegenerate c.length) :
    Function.Injective (fun v ↦ productNecklaceOrder P (c.embedding v)) := by
  intro v w h
  apply (product_nondegenerate_iff_vertex_injective n factor (beadElement P c)).mp hc
  simpa only [productNecklaceOrder_bead] using h

end

end DaggerOriginalProductGadget
