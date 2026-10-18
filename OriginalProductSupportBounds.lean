import OriginalGateHomProductIso
import OriginalProductGateFiber

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)

/-- The existing componentwise relation on the literal binary target is antisymmetric. -/
theorem productCutVertexLE_antisymm
    {x y : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    (h : productCutVertexLE n factor T x y) (k : productCutVertexLE n factor T y x) : x = y := by
  apply SSet.yonedaEquiv.symm.injective
  apply prod.hom_ext
  · apply Pi.hom_ext
    intro i
    apply SSet.yonedaEquiv.injective
    simp only [Category.assoc, SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    apply (factor i).verticesEquiv.injective
    exact ULift.ext _ _ (le_antisymm (h.1 i) (k.1 i))
  · apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    apply T.verticesEquiv.injective
    exact ULift.ext _ _ (le_antisymm h.2 k.2)

/-- Every actual support vertex lies between the two original Hom endpoints. -/
theorem productCut_support_bounds
    {a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    {q : SimplexCategoryᵒᵖ} (x : (flagHom (productSpace n factor ⨯ T.toSSet) a b).obj q)
    (w : (productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌)) (hw : w ∈ flagVertexSupport x) :
    productCutVertexLE n factor T a w ∧ productCutVertexLE n factor T w b := by
  induction x using Quot.ind with
  | _ p =>
    obtain ⟨j, _, rfl⟩ := hw
    have hl : productCutVertexLE n factor T (vertexImage p.1 0) (vertexImage p.1 j.down) :=
      ⟨fun i ↦ (orderMap (p.1.map ≫ prod.fst ≫ Pi.π (fun i ↦ (factor i).toSSet) i)).monotone
        (Fin.zero_le _), (orderMap (p.1.map ≫ prod.snd)).monotone (Fin.zero_le _)⟩
    have hr : productCutVertexLE n factor T
        (vertexImage p.1 j.down) (vertexImage p.1 (Fin.last _)) :=
      ⟨fun i ↦ (orderMap (p.1.map ≫ prod.fst ≫ Pi.π (fun i ↦ (factor i).toSSet) i)).monotone
        (Fin.le_last _), (orderMap (p.1.map ≫ prod.snd)).monotone (Fin.le_last _)⟩
    rw [vertexImage_first] at hl
    rw [vertexImage_last] at hr
    exact ⟨hl, hr⟩

variable {X : SSet.{u}} (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)
  (hanti : ∀ {x y}, R x y → R y x → x = y)
  (hbound : ∀ {a b} {q : SimplexCategoryᵒᵖ} (x : (flagHom X a b).obj q) w,
    w ∈ flagVertexSupport x → R a w ∧ R w b)

include hanti hbound in
/-- Gate conditions after the cut vertex are carried exactly by the right Hom factor. -/
theorem gateTail_support_iff {a v b : X.obj (op ⦋0⦌)} {q : SimplexCategoryᵒᵖ}
    (S : Set (X.obj (op ⦋0⦌))) (hS : ∀ w ∈ S, R v w)
    (x : (flagHom X a v).obj q) (y : (flagHom X v b).obj q) :
    S ⊆ flagVertexSupport (flagCompApp x y) ↔ S ⊆ flagVertexSupport y := by
  rw [flagVertexSupport_comp]
  constructor
  · intro h w hw
    rcases h hw with hl | hr
    · have he : w = v := hanti (hbound x w hl).2 (hS w hw)
      exact he ▸ flagVertexSupport_first y
    · exact hr
  · intro h w hw
    exact Or.inr (h hw)

end

end DaggerOriginalProductGadget
