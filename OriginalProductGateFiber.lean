import OriginalFlagGateFiber

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {A : Set (X.obj (op ⦋0⦌))}
  {R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop} {q : SimplexCategoryᵒᵖ}

/-- The center in the actual row fiber carries the entire support and the original simplex. -/
def flagGateFiberCenter (x : (flagHom X a b).obj q) (hx : IsChain R (flagGateSupport A x))
    (hne : (flagGateSupport A x).Nonempty) : FlagGateRowFiber (A := A) (R := R) x :=
  (flagSupportToGateFiber x hx).obj (flagSupportInitialObj x hne)

/-- Every actual row-fiber object receives a unique arrow from the whole support. -/
def flagGateFiberIsInitial (x : (flagHom X a b).obj q) (hx : IsChain R (flagGateSupport A x))
    (hne : (flagGateSupport A x).Nonempty) : IsInitial (flagGateFiberCenter x hx hne) := by
  refine IsInitial.ofUniqueHom (fun p ↦ ?_) (fun _ _ ↦ ?_)
  · apply ObjectProperty.homMk
    refine ⟨homOfLE ((flagGateFiberToSupport x).obj p).property.2, ?_⟩
    apply Subtype.ext
    exact (flagGateRowFiber_value x p).symm
  · apply ObjectProperty.hom_ext
    apply Subtype.ext
    exact Subsingleton.elim _ _

/-- The componentwise relation on the literal binary product used in bead gluing. -/
def productCutVertexLE (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (x y : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)) : Prop :=
  productVertexLE n factor
    ((prod.fst : productSpace n factor ⨯ T.toSSet ⟶ productSpace n factor).app _ x)
    ((prod.fst : productSpace n factor ⨯ T.toSSet ⟶ productSpace n factor).app _ y) ∧
    productNecklaceCoordinate (productSpace n factor) T x ≤
      productNecklaceCoordinate (productSpace n factor) T y

theorem productCutVertexSupport_chain (n : ℕ) (factor : Fin n → NecklaceCode)
    (T : NecklaceCode) {a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    {q : SimplexCategoryᵒᵖ} (x : (flagHom (productSpace n factor ⨯ T.toSSet) a b).obj q) :
    IsChain (productCutVertexLE n factor T) (flagVertexSupport x) := by
  induction x using Quot.ind with
  | _ p =>
    rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩ _
    rcases le_total v.down w.down with h | h
    · left
      exact ⟨fun i ↦ (orderMap (p.1.map ≫ prod.fst ≫
        Pi.π (fun i ↦ (factor i).toSSet) i)).monotone h,
        (orderMap (p.1.map ≫ prod.snd)).monotone h⟩
    · right
      exact ⟨fun i ↦ (orderMap (p.1.map ≫ prod.fst ≫
        Pi.π (fun i ↦ (factor i).toSSet) i)).monotone h,
        (orderMap (p.1.map ≫ prod.snd)).monotone h⟩

/-- For the original crossing Hom, every row fiber has its actual whole-support initial object.
No separate nonemptiness or chain hypothesis on the supplied simplex is required. -/
def productGateFiberIsInitial (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    {a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
    (ha : productNecklaceCoordinate (productSpace n factor) T a ≤ j)
    (hb : j ≤ productNecklaceCoordinate (productSpace n factor) T b)
    {q : SimplexCategoryᵒᵖ} (x : (flagHom (productSpace n factor ⨯ T.toSSet) a b).obj q) :
    IsInitial (flagGateFiberCenter x
      (IsChain.mono Set.inter_subset_right (productCutVertexSupport_chain n factor T x))
      (productInterface_support_nonempty (productSpace n factor) T j hj ha hb x)) :=
  flagGateFiberIsInitial x _ _

end

end DaggerOriginalProductGadget
