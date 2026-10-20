import OriginalGateListIso

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}}

/-- Remove the first gate by the original composition of its two adjacent Hom factors. -/
def gateListDropFirst (a v b : X.obj (op ⦋0⦌)) :
    ∀ vs, gateListHom a b (v :: vs) ⟶ gateListHom a b vs
  | [] => flagComposition X a v b
  | w :: ws => (α_ (flagHom X a v) (flagHom X v w) (gateListHom w b ws)).inv ≫
      (flagComposition X a v w ⊗ₘ 𝟙 (gateListHom w b ws))

/-- Removing the first gate preserves the original total composite. -/
theorem gateListDropFirst_comp (a v b : X.obj (op ⦋0⦌))
    (vs : List (X.obj (op ⦋0⦌))) :
    gateListDropFirst a v b vs ≫ gateListComposition a b vs =
      gateListComposition a b (v :: vs) := by
  cases vs with
  | nil => rfl
  | cons w ws =>
    apply NatTrans.ext
    funext q x
    exact flagCompApp_assoc x.1 x.2.1 ((gateListComposition w b ws).app q x.2.2)

/-- Remove a gate at an arbitrary position by keeping every preceding Hom factor unchanged. -/
def gateListDelete (a b : X.obj (op ⦋0⦌)) :
    ∀ (beforeGates : List (X.obj (op ⦋0⦌))) (v : X.obj (op ⦋0⦌)) (afterGates : List (X.obj (op ⦋0⦌))),
      gateListHom a b (beforeGates ++ v :: afterGates) ⟶ gateListHom a b (beforeGates ++ afterGates)
  | [], v, afterGates => gateListDropFirst a v b afterGates
  | w :: beforeGates, v, afterGates => 𝟙 (flagHom X a w) ⊗ₘ gateListDelete w b beforeGates v afterGates

/-- Arbitrary-position deletion uses the same original total composite. -/
theorem gateListDelete_comp (a b : X.obj (op ⦋0⦌))
    (beforeGates : List (X.obj (op ⦋0⦌))) (v : X.obj (op ⦋0⦌))
    (afterGates : List (X.obj (op ⦋0⦌))) :
    gateListDelete a b beforeGates v afterGates ≫ gateListComposition a b (beforeGates ++ afterGates) =
      gateListComposition a b (beforeGates ++ v :: afterGates) := by
  induction beforeGates generalizing a with
  | nil => exact gateListDropFirst_comp a v b afterGates
  | cons w beforeGates ih =>
    apply NatTrans.ext
    funext q x
    exact congrArg (flagCompApp x.1) (congrFun (NatTrans.congr_app (ih w) q) x.2)

/-- Deletion forgets exactly one required gate, without changing the original ambient Hom. -/
theorem gateListDelete_subset {V : Type u} (beforeGates : List V) (v : V) (afterGates : List V) :
    gateListSet (beforeGates ++ afterGates) ⊆ gateListSet (beforeGates ++ v :: afterGates) := by
  intro w hw
  rw [gateListSet_mem_iff, List.mem_append] at hw ⊢
  exact hw.elim Or.inl (fun h ↦ Or.inr (List.mem_cons_of_mem v h))

variable (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)
  (hanti : ∀ {x y}, R x y → R y x → x = y)
  (hbound : ∀ {a b} {q : SimplexCategoryᵒᵖ} (x : (flagHom X a b).obj q) w,
    w ∈ flagVertexSupport x → R a w ∧ R w b)
  (hm : ∀ {a b} (P : NecklacesOver X a b),
    (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)

/-- The forward isomorphism followed by original total composition is the original inclusion. -/
theorem gateListIso_hom_comp (a b : X.obj (op ⦋0⦌))
    (vs : List (X.obj (op ⦋0⦌))) (h : vs.Pairwise R) :
    (gateListIso R hanti hbound hm a b vs h).hom ≫ gateListComposition a b vs =
      (flagGateSubcomplex a b (gateListSet vs)).ι := by
  rw [← gateListIso_inv_ι R hanti hbound hm a b vs h, Iso.hom_inv_id_assoc]

/-- The naturality square for deletion is proved for the explicit adjacent-composition map. -/
theorem gateListDelete_naturality (a b : X.obj (op ⦋0⦌))
    (beforeGates : List (X.obj (op ⦋0⦌))) (v : X.obj (op ⦋0⦌))
    (afterGates : List (X.obj (op ⦋0⦌)))
    (hs : (beforeGates ++ v :: afterGates).Pairwise R) (ht : (beforeGates ++ afterGates).Pairwise R) :
    (gateListIso R hanti hbound hm a b (beforeGates ++ v :: afterGates) hs).hom ≫
        gateListDelete a b beforeGates v afterGates =
      Subfunctor.homOfLe (flagGateSubcomplex_antitone a b (gateListDelete_subset beforeGates v afterGates)) ≫
        (gateListIso R hanti hbound hm a b (beforeGates ++ afterGates) ht).hom := by
  have : Mono (gateListComposition a b (beforeGates ++ afterGates)) := by
    rw [← gateListIso_inv_ι R hanti hbound hm a b (beforeGates ++ afterGates) ht]
    infer_instance
  apply (cancel_mono (gateListComposition a b (beforeGates ++ afterGates))).mp
  rw [Category.assoc, gateListDelete_comp, gateListIso_hom_comp,
    Category.assoc, gateListIso_hom_comp, Subfunctor.homOfLe_ι]

/-- The original binary target has the same deletion square, with no additional order premises. -/
theorem productCutGateListDelete_naturality
    (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌))
    (beforeGates : List ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌)))
    (v : (productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌))
    (afterGates : List ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌)))
    (hs : (beforeGates ++ v :: afterGates).Pairwise (productCutVertexLE n factor T))
    (ht : (beforeGates ++ afterGates).Pairwise (productCutVertexLE n factor T)) :
    (productCutGateListIso n factor T a b (beforeGates ++ v :: afterGates) hs).hom ≫
        gateListDelete a b beforeGates v afterGates =
      Subfunctor.homOfLe (flagGateSubcomplex_antitone a b (gateListDelete_subset beforeGates v afterGates)) ≫
        (productCutGateListIso n factor T a b (beforeGates ++ afterGates) ht).hom :=
  gateListDelete_naturality (productCutVertexLE n factor T)
    (productCutVertexLE_antisymm n factor T) (productCut_support_bounds n factor T)
    (productCut_necklace_mono_of_nondegenerate n factor T) a b beforeGates v afterGates hs ht

end

end DaggerOriginalProductGadget
