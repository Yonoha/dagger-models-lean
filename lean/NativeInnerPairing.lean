import NativeInnerHornFactorization
import TopCatModelCategory.SSet.Pairing

/-!
# Existing regular inner pairings generate the exact native inner-left class

Retain the whole original pairing filtration, its actual cell maps and its colimit.
At each step, restrict the allowed cell family to the cells actually attached.
The original IsInner condition proves that each such cell is an original inner horn.
No inner anodyne closure or weak-equivalence conclusion is supplied as a hypothesis.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty
open DaggerNativeInnerHornFactorization
universe w t v u
namespace DaggerNativeInnerPairing
noncomputable section

/-- Restrict the type of permitted cells to the actual cells of the same attachment record. -/
def selectedAttachCells {C : Type u} [Category.{v} C] {α : Type t} {A B : α → C}
    {g : ∀ a, A a ⟶ B a} {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f) :
    AttachCells.{w} (fun a : c.ι ↦ g (c.π a)) f where
  ι := c.ι
  π := id
  cofan₁ := c.cofan₁
  cofan₂ := c.cofan₂
  isColimit₁ := c.isColimit₁
  isColimit₂ := c.isColimit₂
  m := c.m
  hm := c.hm
  g₁ := c.g₁
  g₂ := c.g₂
  isPushout := c.isPushout

/-- Every original inner horn in any dimension is in the full exact inner-left class. -/
theorem horn_innerAnodyne {n : ℕ} (i : Fin (n + 1)) (h0 : 0 < i)
    (hn : i < Fin.last n) : innerAnodyne (SSet.horn.{u} n i).ι := by
  obtain _ | _ | n := n
  · simp only [Fin.lt_def, Fin.val_last, Fin.val_zero] at h0 hn
    omega
  · simp only [Fin.lt_def, Fin.val_last, Fin.val_zero] at h0 hn
    omega
  · change innerAnodyne (generator ⟨n, ⟨i, h0, hn⟩⟩)
    exact le_llp_rlp generators _ (ofHoms.mk _)

/-- The original regular inner pairing proves full native inner-left membership. -/
theorem pairing_innerAnodyne {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] (hInner : P.IsInner) : innerAnodyne A.ι := by
  haveI : innerAnodyne.{u}.IsStableUnderCobaseChange := by
    unfold innerAnodyne
    infer_instance
  haveI : MorphismProperty.IsStableUnderCoproducts.{u} innerAnodyne.{u} := by
    unfold innerAnodyne
    infer_instance
  haveI : innerAnodyne.{u}.IsStableUnderTransfiniteCompositionOfShape ℕ := by
    unfold innerAnodyne
    infer_instance
  apply transfiniteCompositionsOfShape_le innerAnodyne ℕ A.ι
  refine ⟨{ toTransfiniteCompositionOfShape := P.relativeCellComplex.toTransfiniteCompositionOfShape
            map_mem := ?_ }⟩
  intro n hn
  let c := P.relativeCellComplex.attachCells n hn
  have hcells : ofHoms (fun a : c.ι ↦
      (SSet.horn ((c.π a).1 + 1) (c.π a).2).ι) ≤ innerAnodyne := by
    intro U V i hi
    obtain ⟨a⟩ := hi
    have h := hInner a.1
    apply horn_innerAnodyne
    · exact Fin.pos_iff_ne_zero.mpr h.1
    · exact Fin.lt_last_iff_ne_last.mpr h.2
  exact ((pushouts_le_iff).2 ((coproducts_le_iff).2 hcells)) _
    (selectedAttachCells c).pushouts_coproducts

end
end DaggerNativeInnerPairing
