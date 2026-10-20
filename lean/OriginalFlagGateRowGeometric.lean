import OriginalProductGateFiber
import NerveHomotopy

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} (a b : X.obj (op ⦋0⦌)) (A : Set (X.obj (op ⦋0⦌)))
  (R₀ : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop) (q : SimplexCategoryᵒᵖ)
  (hc : ∀ x : (flagHom X a b).obj q, IsChain R₀ (flagGateSupport A x))
  (hn : ∀ x : (flagHom X a b).obj q, (flagGateSupport A x).Nonempty)

/-- The row section chooses the whole support and retains the supplied original simplex. -/
def flagGateRowCenters :
    Discrete ((flagHom X a b).obj q) ⥤ (flagGateDegreeDiagram a b A R₀ q).Elements :=
  Discrete.functor (fun x ↦ (flagGateFiberCenter x (hc x) (hn x)).obj)

def flagGateRowCentersAugmentationIso :
    flagGateRowCenters a b A R₀ q hc hn ⋙ flagGateRowAugmentation a b A R₀ q ≅ 𝟭 _ :=
  Discrete.natIso (fun _ ↦ Discrete.eqToIso rfl)

/-- The whole-support inclusion gives a natural arrow to every object of the actual row. -/
def flagGateRowCenterToId :
    flagGateRowAugmentation a b A R₀ q ⋙ flagGateRowCenters a b A R₀ q hc hn ⟶ 𝟭 _ where
  app p := ((flagGateFiberIsInitial p.2.val (hc p.2.val) (hn p.2.val)).to ⟨p, rfl⟩).hom
  naturality _ _ _ := by
    apply Subtype.ext
    exact Subsingleton.elim _ _

include hc hn in
/-- Existing nerve homotopies prove geometric W for the same row augmentation. -/
theorem flagGateRowAugmentation_geometricW :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map
      (nerveMap (flagGateRowAugmentation a b A R₀ q)))) := by
  apply nerveMap_geometricW (flagGateRowAugmentation a b A R₀ q)
    (flagGateRowCenters a b A R₀ q hc hn)
  · exact Relation.EqvGen.rel _ _ ⟨flagGateRowCenterToId a b A R₀ q hc hn⟩
  · exact Relation.EqvGen.rel _ _ ⟨(flagGateRowCentersAugmentationIso a b A R₀ q hc hn).hom⟩

/-- In the actual product-cut setting, support nonemptiness and the chain condition are proved,
so the original row augmentation is weakly equivalent with no additional fiber hypotheses. -/
theorem productGateRowAugmentation_geometricW (n : ℕ) (factor : Fin n → NecklaceCode)
    (T : NecklaceCode) {a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
    (ha : productNecklaceCoordinate (productSpace n factor) T a ≤ j)
    (hb : j ≤ productNecklaceCoordinate (productSpace n factor) T b)
    (q : SimplexCategoryᵒᵖ) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (nerveMap
      (flagGateRowAugmentation a b (productInterfaceVertices (productSpace n factor) T j)
        (productCutVertexLE n factor T) q)))) :=
  flagGateRowAugmentation_geometricW a b _ _ q
    (fun x ↦ IsChain.mono Set.inter_subset_right (productCutVertexSupport_chain n factor T x))
    (productInterface_support_nonempty (productSpace n factor) T j hj ha hb)

end

end DaggerOriginalProductGadget
