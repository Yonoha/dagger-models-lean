import OriginalProductNecklaceOrder

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {n : ℕ} {factor : Fin n → NecklaceCode}
  {a b : (productSpace.{u} n factor).obj (op ⦋0⦌)}

/-- Beadwise nondegeneracy makes the entire original necklace vertex order strictly monotone. -/
theorem productNecklaceOrder_strictMono (P : NecklacesOver (productSpace.{u} n factor) a b)
    (hP : ∀ c : P.code.Bead, beadElement P c ∈ (productSpace n factor).nonDegenerate c.length) :
    StrictMono (productNecklaceOrder P) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  refine lt_of_le_of_ne ((productNecklaceOrder P).monotone i.castSucc_le_succ) ?_
  intro he
  obtain ⟨c, hl, hr⟩ := P.code.exists_bead_at i.succ (by simp)
  have hleft : c.left ≤ i.castSucc := by
    simp only [Fin.lt_def, Fin.val_succ] at hl
    change c.left.val ≤ i.val
    omega
  have hi : i.castSucc ∈ Set.range c.embedding := by
    simpa only [Bead.embedding, Finset.range_orderEmbOfFin] using
      (show i.castSucc ∈ c.interval from
        Finset.mem_Icc.mpr ⟨hleft, i.castSucc_le_succ.trans hr⟩)
  have hj : i.succ ∈ Set.range c.embedding := by
    simpa only [Bead.embedding, Finset.range_orderEmbOfFin] using
      (show i.succ ∈ c.interval from Finset.mem_Icc.mpr ⟨hl.le, hr⟩)
  obtain ⟨v, hv⟩ := hi
  obtain ⟨w, hw⟩ := hj
  have hvw : v = w := productNecklaceOrder_bead_injective P c (hP c) (by
    change productNecklaceOrder P (c.embedding v) = productNecklaceOrder P (c.embedding w)
    rw [hv, hw]
    exact he)
  have hh := congrArg c.embedding hvw
  rw [hv, hw] at hh
  exact i.castSucc_lt_succ.ne hh

/-- No vertex identification remains in an original product-valued necklace with ND beads. -/
theorem product_necklace_vertices_injective
    (P : NecklacesOver (productSpace.{u} n factor) a b)
    (hP : ∀ c : P.code.Bead, beadElement P c ∈ (productSpace n factor).nonDegenerate c.length) :
    Function.Injective (P.map.app (op ⦋0⦌)) := by
  intro x y h
  apply P.code.verticesEquiv.injective
  apply ULift.ext
  apply (productNecklaceOrder_strictMono P hP).injective
  rw [productNecklaceOrder_vertex, productNecklaceOrder_vertex]
  have hv : vertexImage P (P.code.verticesEquiv x).down =
      vertexImage P (P.code.verticesEquiv y).down := by
    simpa only [vertexImage, ULift.up_down, Equiv.symm_apply_apply] using h
  exact congrArg (fun z ↦ ((productOrderedEmbedding n factor).app (op ⦋0⦌) z).obj 0) hv

/-- Ordered products turn actual beadwise nondegeneracy into Mono of the same necklace map. -/
theorem product_necklace_mono_of_nondegenerate
    (P : NecklacesOver (productSpace.{u} n factor) a b)
    (hP : ∀ c : P.code.Bead, beadElement P c ∈ (productSpace n factor).nonDegenerate c.length) :
    Mono P.map :=
  necklace_map_mono_of_vertex_injective P.code P.map (product_necklace_vertices_injective P hP)

/-- The existing normalization has a monomorphic map into this actual product target. -/
theorem normOver_product_mono (P : NecklacesOver (productSpace.{u} n factor) a b) :
    Mono (normOver P).map :=
  product_necklace_mono_of_nondegenerate (normOver P) (normOver_beads_nondegenerate P)

end

end DaggerOriginalProductGadget
