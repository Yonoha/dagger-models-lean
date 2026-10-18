import OriginalGateChainEnumeration
import OriginalGateListFilter

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type u} (R : V → V → Prop)
  (hrefl : ∀ x, R x x)
  (htrans : ∀ {x y z}, R x y → R y z → R x z)
  (hanti : ∀ {x y}, R x y → R y x → x = y)

/-- Filtering the larger chain by membership in the smaller chain gives its exact enumeration. -/
theorem gateChainList_filter {S T : Set V} (hS : S.Finite) (hcS : IsChain R S)
    (hT : T.Finite) (hcT : IsChain R T) (hST : S ⊆ T) :
    ((gateChainList R hrefl htrans hanti T hT hcT).filter (fun w ↦ decide (w ∈ S))) =
      gateChainList R hrefl htrans hanti S hS hcS := by
  classical
  let : Std.Antisymm R := ⟨fun _ _ h k ↦ hanti h k⟩
  have hmem : ∀ w,
      w ∈ (gateChainList R hrefl htrans hanti T hT hcT).filter (fun w ↦ decide (w ∈ S)) ↔
        w ∈ gateChainList R hrefl htrans hanti S hS hcS := by
    intro w
    simp only [List.mem_filter, decide_eq_true_eq,
      gateChainList_mem R hrefl htrans hanti]
    exact ⟨And.right, fun h ↦ ⟨hST h, h⟩⟩
  apply List.Perm.eq_of_pairwise'
    ((gateChainList_pairwise R hrefl htrans hanti T hT hcT).sublist List.filter_sublist)
    (gateChainList_pairwise R hrefl htrans hanti S hS hcS)
  exact (List.subperm_of_subset
    ((gateChainList_nodup R hrefl htrans hanti T hT hcT).sublist List.filter_sublist)
    (fun w hw ↦ (hmem w).mp hw)).antisymm
    (List.subperm_of_subset (gateChainList_nodup R hrefl htrans hanti S hS hcS)
      (fun w hw ↦ (hmem w).mpr hw))

variable {X : SSet.{u}}

/-- Relabeling equal gate sets retains the original subcomplex inclusion. -/
theorem gateSubcomplex_eqToHom_ι (a b : X.obj (op ⦋0⦌))
    {S T : Set (X.obj (op ⦋0⦌))} (h : S = T) :
    eqToHom (congrArg (fun K ↦ (flagGateSubcomplex a b K).toFunctor) h) ≫
      (flagGateSubcomplex a b T).ι = (flagGateSubcomplex a b S).ι := by
  subst T
  rfl

variable (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)
  (hrefl : ∀ x, R x x)
  (htrans : ∀ {x y z}, R x y → R y z → R x z)
  (hanti : ∀ {x y}, R x y → R y x → x = y)
  (hbound : ∀ {a b} {q : SimplexCategoryᵒᵖ} (x : (flagHom X a b).obj q) w,
    w ∈ flagVertexSupport x → R a w ∧ R w b)
  (hm : ∀ {a b} (P : NecklacesOver X a b),
    (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)
  (a b : X.obj (op ⦋0⦌)) (A : Set (X.obj (op ⦋0⦌)))

/-- Enumerate each object of the unchanged finite-chain-set index. -/
def gateIndexList (S : FlagGateIndex A R) : List (X.obj (op ⦋0⦌)) :=
  gateChainList R hrefl htrans hanti S.val S.property.2.1 S.property.2.2.2

theorem gateIndexList_set (S : FlagGateIndex A R) :
    gateListSet (gateIndexList R hrefl htrans hanti A S) = S.val :=
  gateChainList_set R hrefl htrans hanti S.val S.property.2.1 S.property.2.2.2

theorem gateIndexList_pairwise (S : FlagGateIndex A R) :
    (gateIndexList R hrefl htrans hanti A S).Pairwise R :=
  gateChainList_pairwise R hrefl htrans hanti S.val S.property.2.1 S.property.2.2.2

/-- The finite-list isomorphism on each actual gate-set-index object. -/
def gateChainHomIso (S : FlagGateIndex A R) :
    (flagGateSubcomplex a b S.val).toFunctor ≅
      gateListHom a b (gateIndexList R hrefl htrans hanti A S) :=
  eqToIso (congrArg (fun K ↦ (flagGateSubcomplex a b K).toFunctor)
    (gateIndexList_set R hrefl htrans hanti A S).symm) ≪≫
      gateListIso R hanti hbound hm a b (gateIndexList R hrefl htrans hanti A S)
        (gateIndexList_pairwise R hrefl htrans hanti A S)

/-- The inverse still augments by the original iterated composition. -/
theorem gateChainHomIso_inv_ι (S : FlagGateIndex A R) :
    (gateChainHomIso R hrefl htrans hanti hbound hm a b A S).inv ≫
      (flagGateSubcomplex a b S.val).ι =
        gateListComposition a b (gateIndexList R hrefl htrans hanti A S) := by
  dsimp only [gateChainHomIso, Iso.trans_inv, eqToIso.inv]
  rw [Category.assoc,
    gateSubcomplex_eqToHom_ι a b (gateIndexList_set R hrefl htrans hanti A S),
    gateListIso_inv_ι]

theorem gateChainHomIso_hom_comp (S : FlagGateIndex A R) :
    (gateChainHomIso R hrefl htrans hanti hbound hm a b A S).hom ≫
      gateListComposition a b (gateIndexList R hrefl htrans hanti A S) =
        (flagGateSubcomplex a b S.val).ι := by
  rw [← gateChainHomIso_inv_ι R hrefl htrans hanti hbound hm a b A S,
    Iso.hom_inv_id_assoc]

include hbound hm in
/-- Total composition is monic because it is the inverse isomorphism followed by inclusion. -/
theorem gateChainComposition_mono (S : FlagGateIndex A R) :
    Mono (gateListComposition a b (gateIndexList R hrefl htrans hanti A S)) := by
  rw [← gateChainHomIso_inv_ι R hrefl htrans hanti hbound hm a b A S]
  infer_instance

end

end DaggerOriginalProductGadget
