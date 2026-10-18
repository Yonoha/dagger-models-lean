import OriginalFlagGateSubcomplex
import OriginalFlagSupportFlank
import OriginalProductGadgetData
import Mathlib.Order.Preorder.Chain

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

def productInterfaceVertices (K : SSet.{u}) (T : NecklaceCode) (j : Fin (T.len + 1)) :
    Set ((K ⨯ T.toSSet).obj (op ⦋0⦌)) :=
  Set.range ((productJointInclusion K T j).app (op ⦋0⦌))

/-- Every original crossing flag class has a nonempty support in the actual common product. -/
theorem productInterface_support_nonempty (K : SSet.{u}) (T : NecklaceCode)
    {a b : (K ⨯ T.toSSet).obj (op ⦋0⦌)} (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
    (ha : productNecklaceCoordinate K T a ≤ j) (hb : j ≤ productNecklaceCoordinate K T b)
    {q : SimplexCategoryᵒᵖ} (x : (flagHom (K ⨯ T.toSSet) a b).obj q) :
    (flagGateSupport (productInterfaceVertices K T j) x).Nonempty := by
  induction x using Quot.ind with
  | _ p =>
    obtain ⟨k, hk, he, _⟩ := productOver_crossingJoint K T p.1 j hj ha hb
    refine ⟨vertexImage p.1 k, ?_, ?_⟩
    · exact ⟨SSet.yonedaEquiv (productCrossingPoint K T p.1.code p.1.map k),
        productCrossingPoint_vertex K T p.1.code p.1.map k j he⟩
    · exact ⟨ULift.up k, p.2.joints _ hk, rfl⟩

/-- The one-gate subcomplexes cover every simplex of the original crossing Hom. -/
theorem productInterface_gate_member (K : SSet.{u}) (T : NecklaceCode)
    {a b : (K ⨯ T.toSSet).obj (op ⦋0⦌)} (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
    (ha : productNecklaceCoordinate K T a ≤ j) (hb : j ≤ productNecklaceCoordinate K T b)
    {q : SimplexCategoryᵒᵖ} (x : (flagHom (K ⨯ T.toSSet) a b).obj q) :
    ∃ v ∈ productInterfaceVertices K T j, x ∈ (flagGateSubcomplex a b {v}).obj q := by
  obtain ⟨v, hv, hs⟩ := productInterface_support_nonempty K T j hj ha hb x
  exact ⟨v, hv, Set.singleton_subset_iff.mpr hs⟩

/-- The same covering assertion as an equality of actual simplicial subcomplexes. -/
theorem productInterface_gate_cover (K : SSet.{u}) (T : NecklaceCode)
    {a b : (K ⨯ T.toSSet).obj (op ⦋0⦌)} (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
    (ha : productNecklaceCoordinate K T a ≤ j) (hb : j ≤ productNecklaceCoordinate K T b) :
    (⨆ v : productInterfaceVertices K T j, flagGateSubcomplex a b {v.val}) = ⊤ := by
  apply le_antisymm le_top
  intro q x _
  obtain ⟨v, hv, hx⟩ := productInterface_gate_member K T j hj ha hb x
  exact (le_iSup (fun v : productInterfaceVertices K T j ↦
    flagGateSubcomplex a b {v.val}) ⟨v, hv⟩) q hx

/-- The original componentwise vertex relation of a finite product of necklace codes. -/
def productVertexLE (n : ℕ) (factor : Fin n → NecklaceCode)
    (x y : (productSpace.{u} n factor).obj (op ⦋0⦌)) : Prop :=
  ∀ i, vertex n factor i x ≤ vertex n factor i y

/-- Every original flag support in a product gadget is a chain in the actual vertex relation. -/
theorem productVertexSupport_chain (n : ℕ) (factor : Fin n → NecklaceCode)
    {a b : (productSpace.{u} n factor).obj (op ⦋0⦌)} {q : SimplexCategoryᵒᵖ}
    (x : (flagHom (productSpace n factor) a b).obj q) :
    IsChain (productVertexLE n factor) (flagVertexSupport x) := by
  induction x using Quot.ind with
  | _ p =>
    rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩ _
    rcases le_total v.down w.down with h | h
    · left
      intro i
      exact (orderMap (p.1.map ≫ Pi.π (fun i ↦ (factor i).toSSet) i)).monotone h
    · right
      intro i
      exact (orderMap (p.1.map ≫ Pi.π (fun i ↦ (factor i).toSSet) i)).monotone h

end

end DaggerOriginalProductGadget
