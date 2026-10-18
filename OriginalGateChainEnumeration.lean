import OriginalGateListDeletion
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {V : Type u} (R : V → V → Prop)
  (hrefl : ∀ x, R x x)
  (htrans : ∀ {x y z}, R x y → R y z → R x z)
  (hanti : ∀ {x y}, R x y → R y x → x = y)

include hrefl htrans hanti in
/-- Sort only within the supplied finite chain; the ambient relation need not be total. -/
theorem exists_gateChainList (S : Set V) (hfin : S.Finite) (hchain : IsChain R S) :
    ∃ vs : List V, vs.Nodup ∧ vs.Pairwise R ∧ ∀ w, w ∈ vs ↔ w ∈ S := by
  classical
  let r : S → S → Prop := fun x y ↦ R x.val y.val
  let : Fintype S := hfin.fintype
  let : IsTrans S r := ⟨fun _ _ _ h k ↦ htrans h k⟩
  let : Std.Antisymm r := ⟨fun _ _ h k ↦ Subtype.ext (hanti h k)⟩
  let : Std.Total r := ⟨fun x y ↦ by
    by_cases h : x.val = y.val
    · left
      change R x.val y.val
      rw [← h]
      exact hrefl x.val
    · exact hchain x.property y.property h⟩
  let vs := (Finset.univ : Finset S).sort r
  refine ⟨vs.map Subtype.val, ?_, ?_, ?_⟩
  · exact (List.nodup_map_iff Subtype.val_injective).mpr (Finset.sort_nodup _ _)
  · exact List.pairwise_map.mpr (Finset.pairwise_sort _ _)
  · intro w
    simp only [List.mem_map]
    constructor
    · rintro ⟨v, _, rfl⟩
      exact v.property
    · intro hw
      exact ⟨⟨w, hw⟩, (Finset.mem_sort r).mpr (Finset.mem_univ _), rfl⟩

/-- The unique ordered enumeration of the supplied finite chain. -/
def gateChainList (S : Set V) (hfin : S.Finite) (hchain : IsChain R S) : List V :=
  (exists_gateChainList R hrefl htrans hanti S hfin hchain).choose

theorem gateChainList_nodup (S : Set V) (hfin : S.Finite) (hchain : IsChain R S) :
    (gateChainList R hrefl htrans hanti S hfin hchain).Nodup :=
  (exists_gateChainList R hrefl htrans hanti S hfin hchain).choose_spec.1

theorem gateChainList_pairwise (S : Set V) (hfin : S.Finite) (hchain : IsChain R S) :
    (gateChainList R hrefl htrans hanti S hfin hchain).Pairwise R :=
  (exists_gateChainList R hrefl htrans hanti S hfin hchain).choose_spec.2.1

theorem gateChainList_mem (S : Set V) (hfin : S.Finite) (hchain : IsChain R S) (w : V) :
    w ∈ gateChainList R hrefl htrans hanti S hfin hchain ↔ w ∈ S :=
  (exists_gateChainList R hrefl htrans hanti S hfin hchain).choose_spec.2.2 w

theorem gateChainList_set (S : Set V) (hfin : S.Finite) (hchain : IsChain R S) :
    gateListSet (gateChainList R hrefl htrans hanti S hfin hchain) = S := by
  ext w
  exact (gateListSet_mem_iff _ w).trans (gateChainList_mem R hrefl htrans hanti S hfin hchain w)

/-- Inclusion of chains is the actual sublist relation on their ordered enumerations. -/
theorem gateChainList_sublist {S T : Set V} (hS : S.Finite) (hcS : IsChain R S)
    (hT : T.Finite) (hcT : IsChain R T) (hST : S ⊆ T) :
    List.Sublist (gateChainList R hrefl htrans hanti S hS hcS)
      (gateChainList R hrefl htrans hanti T hT hcT) := by
  let : Std.Antisymm R := ⟨fun _ _ h k ↦ hanti h k⟩
  apply List.sublist_of_subperm_of_pairwise
    (List.subperm_of_subset (gateChainList_nodup R hrefl htrans hanti S hS hcS) ?_)
    (gateChainList_pairwise R hrefl htrans hanti S hS hcS)
    (gateChainList_pairwise R hrefl htrans hanti T hT hcT)
  intro w hw
  exact (gateChainList_mem R hrefl htrans hanti T hT hcT w).mpr
    (hST ((gateChainList_mem R hrefl htrans hanti S hS hcS w).mp hw))

/-- The componentwise relation used by the original binary target is reflexive. -/
theorem productCutVertexLE_refl (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (x : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)) :
    productCutVertexLE n factor T x x := ⟨fun _ ↦ le_rfl, le_rfl⟩

/-- The same original relation is transitive, with no total-order assumption on the product. -/
theorem productCutVertexLE_trans (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    {x y z : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    (h : productCutVertexLE n factor T x y) (k : productCutVertexLE n factor T y z) :
    productCutVertexLE n factor T x z := ⟨fun i ↦ (h.1 i).trans (k.1 i), h.2.trans k.2⟩

end

end DaggerOriginalProductGadget
