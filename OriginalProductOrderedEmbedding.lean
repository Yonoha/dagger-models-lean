import OriginalProductGateSupport
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- The actual componentwise vertex order, lifted to the product's original universe. -/
def ProductVertexOrder (n : ℕ) (factor : Fin n → NecklaceCode) :=
  ∀ i, ULift.{u} (Fin ((factor i).len + 1))

instance productVertexOrderPartialOrder (n : ℕ) (factor : Fin n → NecklaceCode) :
    PartialOrder (ProductVertexOrder.{u} n factor) :=
  inferInstanceAs (PartialOrder (∀ i, ULift.{u} (Fin ((factor i).len + 1))))

variable (n : ℕ) (factor : Fin n → NecklaceCode)

/-- Read every vertex of an original product simplex through the existing necklace inclusions. -/
def productOrderedSimplex (q : SimplexCategoryᵒᵖ) (x : (productSpace.{u} n factor).obj q) :
    (nerve (ProductVertexOrder.{u} n factor)).obj q where
  obj j i := ULift.up ((SSet.stdSimplex.objEquiv ((factor i).inclusion.app q
    ((Pi.π (fun i ↦ (factor i).toSSet) i).app q x))).toOrderHom j)
  map f := homOfLE (fun i ↦ (SSet.stdSimplex.objEquiv
    ((factor i).inclusion.app q ((Pi.π (fun i ↦ (factor i).toSSet) i).app q x))).toOrderHom.monotone
      (leOfHom f))

/-- An actual simplicial map to the nerve of the product vertex order. -/
def productOrderedEmbedding : productSpace.{u} n factor ⟶ nerve (ProductVertexOrder.{u} n factor) where
  app := productOrderedSimplex n factor
  naturality q r α := by
    funext x
    refine CategoryTheory.Functor.ext (fun j ↦ ?_)
    funext i
    apply ULift.ext
    have h := congrFun (((Pi.π (fun i ↦ (factor i).toSSet) i) ≫
      (factor i).inclusion).naturality α) x
    exact congrArg (fun y ↦ (SSet.stdSimplex.objEquiv y).toOrderHom j) h

theorem productOrderedEmbedding_injective (q : SimplexCategoryᵒᵖ) :
    Function.Injective ((productOrderedEmbedding.{u} n factor).app q) := by
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d
  intro x y h
  apply SSet.yonedaEquiv.symm.injective
  apply Pi.hom_ext
  intro i
  apply (cancel_mono (factor i).inclusion).1
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp]
  have hx : SSet.yonedaEquiv (SSet.yonedaEquiv.symm x) = x :=
    SSet.yonedaEquiv.apply_symm_apply x
  have hy : SSet.yonedaEquiv (SSet.yonedaEquiv.symm y) = y :=
    SSet.yonedaEquiv.apply_symm_apply y
  apply SSet.stdSimplex.ext
  intro j
  let coord (z : (productSpace.{u} n factor).obj (op ⦋d⦌)) :=
    (factor i).inclusion.app _ ((Pi.π (fun i ↦ (factor i).toSSet) i).app _ z) j
  exact (congrArg coord hx).trans
    ((congrArg (fun z ↦ (z.obj j i).down) h).trans (congrArg coord hy).symm)

instance productOrderedEmbedding_mono : Mono (productOrderedEmbedding.{u} n factor) := by
  have : ∀ q, Mono ((productOrderedEmbedding.{u} n factor).app q) :=
    fun q ↦ (mono_iff_injective _).mpr (productOrderedEmbedding_injective n factor q)
  exact NatTrans.mono_of_mono_app _

/-- The embedding reads the original product vertex coordinates, without changing carriers. -/
theorem productOrderedEmbedding_vertex (x : (productSpace.{u} n factor).obj (op ⦋0⦌))
    (i : Fin n) :
    (((productOrderedEmbedding n factor).app (op ⦋0⦌) x).obj 0 i).down =
      vertex n factor i x := rfl

/-- The pinned Mathlib nondegeneracy theorem applies to every original product simplex. -/
theorem product_nondegenerate_iff_vertex_injective {d : ℕ}
    (x : (productSpace.{u} n factor).obj (op ⦋d⦌)) :
    x ∈ (productSpace n factor).nonDegenerate d ↔
      Function.Injective (((productOrderedEmbedding n factor).app (op ⦋d⦌) x).obj) := by
  rw [← SSet.nonDegenerate_iff_of_mono (productOrderedEmbedding n factor) x]
  exact PartialOrder.mem_nerve_nonDegenerate_iff_injective _

end

end DaggerOriginalProductGadget
