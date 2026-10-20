import OriginalGateInsertIso

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- The set of required gates in a finite list, retaining empty and repeated-gate cases. -/
def gateListSet {V : Type u} : List V → Set V
  | [] => ∅
  | v :: vs => insert v (gateListSet vs)

theorem gateListSet_mem_iff {V : Type u} (vs : List V) (w : V) :
    w ∈ gateListSet vs ↔ w ∈ vs := by
  induction vs with
  | nil => simp [gateListSet]
  | cons v vs ih => simp [gateListSet, ih]

variable {X : SSet.{u}}

/-- The actual right-associated product of the original Hom spaces between consecutive gates. -/
def gateListHom (a b : X.obj (op ⦋0⦌)) : List (X.obj (op ⦋0⦌)) → SSet.{u}
  | [] => flagHom X a b
  | v :: vs => flagHom X a v ⊗ gateListHom v b vs

/-- The iterated original composition, with the empty list giving the unchanged Hom. -/
def gateListComposition (a b : X.obj (op ⦋0⦌)) :
    ∀ vs, gateListHom a b vs ⟶ flagHom X a b
  | [] => 𝟙 _
  | v :: vs => (𝟙 (flagHom X a v) ⊗ₘ gateListComposition v b vs) ≫ flagComposition X a v b

/-- Requiring no gates is exactly the original Hom, via its original inclusion. -/
def emptyGateHomIso (a b : X.obj (op ⦋0⦌)) :
    (flagGateSubcomplex a b ∅).toFunctor ≅ flagHom X a b where
  hom := (flagGateSubcomplex a b ∅).ι
  inv := { app _ x := ⟨x, Set.empty_subset _⟩, naturality _ _ _ := rfl }
  hom_inv_id := by ext q x; rfl
  inv_hom_id := rfl

variable (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)
  (hanti : ∀ {x y}, R x y → R y x → x = y)
  (hbound : ∀ {a b} {q : SimplexCategoryᵒᵖ} (x : (flagHom X a b).obj q) w,
    w ∈ flagVertexSupport x → R a w ∧ R w b)
  (hm : ∀ {a b} (P : NecklacesOver X a b),
    (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)

/-- Every finite ordered list of gates decomposes the literal gate subcomplex into
all consecutive original Hom factors, with no distinct-endpoint assumption. -/
def gateListIso (a b : X.obj (op ⦋0⦌)) : ∀ vs, vs.Pairwise R →
    ((flagGateSubcomplex a b (gateListSet vs)).toFunctor ≅ gateListHom a b vs)
  | [], _ => emptyGateHomIso a b
  | v :: vs, h =>
    gateInsertIso a v b (gateListSet vs) hm R hanti hbound
      (fun w hw ↦ (List.pairwise_cons.mp h).1 w ((gateListSet_mem_iff vs w).mp hw)) ≪≫
        tensorIso (Iso.refl _) (gateListIso v b vs (List.pairwise_cons.mp h).2)

/-- The inverse followed by the original inclusion is exactly iterated original composition. -/
theorem gateListIso_inv_ι (a b : X.obj (op ⦋0⦌))
    (vs : List (X.obj (op ⦋0⦌))) (h : vs.Pairwise R) :
    (gateListIso R hanti hbound hm a b vs h).inv ≫
        (flagGateSubcomplex a b (gateListSet vs)).ι = gateListComposition a b vs := by
  induction vs generalizing a with
  | nil => rfl
  | cons v vs ih =>
    apply NatTrans.ext
    funext q x
    exact congrArg (flagCompApp x.1)
      (congrFun (NatTrans.congr_app (ih v (List.pairwise_cons.mp h).2) q) x.2)

/-- The actual binary product discharges all order, support and monomorphism hypotheses. -/
def productCutGateListIso (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌))
    (vs : List ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌)))
    (h : vs.Pairwise (productCutVertexLE n factor T)) :
    (flagGateSubcomplex a b (gateListSet vs)).toFunctor ≅ gateListHom a b vs :=
  gateListIso (productCutVertexLE n factor T) (productCutVertexLE_antisymm n factor T)
    (productCut_support_bounds n factor T) (productCut_necklace_mono_of_nondegenerate n factor T)
    a b vs h

/-- The product specialization retains the same original composition for every finite gate list. -/
theorem productCutGateListIso_inv_ι (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌))
    (vs : List ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌)))
    (h : vs.Pairwise (productCutVertexLE n factor T)) :
    (productCutGateListIso n factor T a b vs h).inv ≫
        (flagGateSubcomplex a b (gateListSet vs)).ι = gateListComposition a b vs :=
  gateListIso_inv_ι (productCutVertexLE n factor T) (productCutVertexLE_antisymm n factor T)
    (productCut_support_bounds n factor T) (productCut_necklace_mono_of_nondegenerate n factor T)
    a b vs h

end

end DaggerOriginalProductGadget
