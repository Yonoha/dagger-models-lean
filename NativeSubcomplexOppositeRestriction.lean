import OriginalHornFillingReversal
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-! Pointwise opposite restriction for arbitrary original subcomplexes, with inclusion control. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
universe u
namespace DaggerNativeSubcomplexOppositeRestriction
noncomputable section
variable {X : SSet.{u}} (A : X.Subcomplex) (B : X.op.Subcomplex)

def forward (h : ∀ q (s : (A : SSet.{u}).op.obj q), s.val ∈ B.obj q) :
    (A : SSet.{u}).op ⟶ (B : SSet.{u}) where
  app q s := ⟨s.val, h q s⟩
  naturality _ _ _ := by
    funext s
    apply Subtype.ext
    rfl

def backward (h : ∀ q (s : (B : SSet.{u}).obj q), s.val ∈ A.obj q) :
    (B : SSet.{u}) ⟶ (A : SSet.{u}).op where
  app q s := ⟨s.val, h q s⟩
  naturality _ _ _ := by
    funext s
    apply Subtype.ext
    rfl

theorem forward_val (h : ∀ q (s : (A : SSet.{u}).op.obj q), s.val ∈ B.obj q)
    (q : SimplexCategoryᵒᵖ) (s : (A : SSet.{u}).op.obj q) :
    ((forward A B h).app q s).val = s.val := rfl

theorem backward_val (h : ∀ q (s : (B : SSet.{u}).obj q), s.val ∈ A.obj q)
    (q : SimplexCategoryᵒᵖ) (s : (B : SSet.{u}).obj q) :
    ((backward A B h).app q s).val = s.val := rfl

def restrictionIso
    (h : ∀ q (s : (A : SSet.{u}).op.obj q), s.val ∈ B.obj q)
    (k : ∀ q (s : (B : SSet.{u}).obj q), s.val ∈ A.obj q) :
    (A : SSet.{u}).op ≅ (B : SSet.{u}) where
  hom := forward A B h
  inv := backward A B k
  hom_inv_id := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    rfl

theorem forward_comp_inclusion
    (h : ∀ q (s : (A : SSet.{u}).op.obj q), s.val ∈ B.obj q) :
    forward A B h ≫ B.ι = SSet.opFunctor.map A.ι := by
  apply NatTrans.ext
  funext q s
  rfl

theorem backward_comp_inclusion
    (k : ∀ q (s : (B : SSet.{u}).obj q), s.val ∈ A.obj q) :
    backward A B k ≫ SSet.opFunctor.map A.ι = B.ι := by
  apply NatTrans.ext
  funext q s
  rfl

end
end DaggerNativeSubcomplexOppositeRestriction
