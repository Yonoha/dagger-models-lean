import CoproductPartialBatch
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

set_option autoImplicit false

/-! Compare a full partial batch with the same original coproduct pushout and both its legs. -/

open CategoryTheory Limits DaggerCoproductPartialBatch

universe w v u

namespace DaggerCoproductBatchEndpoint

noncomputable section

variable {C : Type u} [Category.{v} C] {I : Type w}
  [HasCoproducts.{w} C]

/-- Reindex a given full original coproduct by a subset containing all original indices. -/
def fullCoproductIso (A : I → C) (S : Set I) (hS : ∀ i, i ∈ S)
    (c : Cofan A) (hc : IsColimit c) : (∐ fun i : S ↦ A i.1) ≅ c.pt where
  hom := Sigma.desc (fun i : S ↦ c.inj i.1)
  inv := Cofan.IsColimit.desc hc (fun i ↦ Sigma.ι (fun j : S ↦ A j.1) ⟨i, hS i⟩)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    simp
  inv_hom_id := by
    apply Cofan.IsColimit.hom_ext hc
    intro i
    simp

@[reassoc (attr := simp)]
theorem ι_fullCoproductIso_hom (A : I → C) (S : Set I) (hS : ∀ i, i ∈ S)
    (c : Cofan A) (hc : IsColimit c) (i : S) :
    Sigma.ι (fun j : S ↦ A j.1) i ≫ (fullCoproductIso A S hS c hc).hom = c.inj i.1 := by
  simp [fullCoproductIso]

@[reassoc (attr := simp)]
theorem inj_fullCoproductIso_inv (A : I → C) (S : Set I) (hS : ∀ i, i ∈ S)
    (c : Cofan A) (hc : IsColimit c) (i : I) :
    c.inj i ≫ (fullCoproductIso A S hS c hc).inv =
      Sigma.ι (fun j : S ↦ A j.1) ⟨i, hS i⟩ := by
  simp [fullCoproductIso]

variable (A B : I → C) (p : ∀ i, A i ⟶ B i)
  (S : Set I) (hS : ∀ i, i ∈ S)
  (cA : Cofan A) (cB : Cofan B) (hA : IsColimit cA) (hB : IsColimit cB)
  (pSum : cA.pt ⟶ cB.pt) (hpSum : ∀ i, cA.inj i ≫ pSum = p i ≫ cB.inj i)
  {X Y : C} (q : cA.pt ⟶ X) {f : X ⟶ Y} {g : cB.pt ⟶ Y}
  (sq : IsPushout q pSum f g)

include hpSum in
/-- The entire original coproduct map agrees with the partial map through both cofan isos. -/
theorem full_cellMap :
    (fullCoproductIso A S hS cA hA).hom ≫ pSum =
      cellMap A B p S ≫ (fullCoproductIso B S hS cB hB).hom := by
  apply Sigma.hom_ext
  intro i
  simpa [cellMap, Category.assoc] using hpSum i.1

theorem full_attaching :
    (fullCoproductIso A S hS cA hA).hom ≫ q =
      attaching A (fun i ↦ cA.inj i ≫ q) S := by
  apply Sigma.hom_ext
  intro i
  simp [attaching]

include hA hpSum sq in
/-- Transport the original square with the same X, Y, f and complete original g leg. -/
theorem fullBatch_isPushout :
    IsPushout (attaching A (fun i ↦ cA.inj i ≫ q) S) (cellMap A B p S)
      f ((fullCoproductIso B S hS cB hB).hom ≫ g) := by
  apply sq.of_iso' (fullCoproductIso A S hS cA hA) (Iso.refl X)
    (fullCoproductIso B S hS cB hB) (Iso.refl Y)
  · simpa using full_attaching A S hS cA hA q
  · exact full_cellMap A B p S hS cA cB hA hB pSum hpSum
  · simp
  · simp

variable [HasPushouts C]

/-- The final partial-batch object is identified with the original given pushout apex. -/
def fullBatchIso : batch A B p (fun i ↦ cA.inj i ≫ q) S ≅ Y :=
  (IsPushout.of_hasPushout (attaching A (fun i ↦ cA.inj i ≫ q) S)
    (cellMap A B p S)).isoIsPushout _ _
      (fullBatch_isPushout A B p S hS cA cB hA hB pSum hpSum q sq)

@[reassoc (attr := simp)]
theorem base_fullBatchIso_hom :
    base A B p (fun i ↦ cA.inj i ≫ q) S ≫
      (fullBatchIso A B p S hS cA cB hA hB pSum hpSum q sq).hom = f := by
  simp [base, fullBatchIso]

/-- This is equality of the complete B-coproduct leg, before taking its components. -/
@[reassoc (attr := simp)]
theorem inr_fullBatchIso_hom :
    pushout.inr (attaching A (fun i ↦ cA.inj i ≫ q) S) (cellMap A B p S) ≫
      (fullBatchIso A B p S hS cA cB hA hB pSum hpSum q sq).hom =
        (fullCoproductIso B S hS cB hB).hom ≫ g := by
  simp [fullBatchIso]

@[reassoc (attr := simp)]
theorem cell_fullBatchIso_hom (i : S) :
    cell A B p (fun i ↦ cA.inj i ≫ q) S i ≫
      (fullBatchIso A B p S hS cA cB hA hB pSum hpSum q sq).hom = cB.inj i.1 ≫ g := by
  simp [cell, Category.assoc]

@[reassoc (attr := simp)]
theorem original_fullBatchIso_inv :
    f ≫ (fullBatchIso A B p S hS cA cB hA hB pSum hpSum q sq).inv =
      base A B p (fun i ↦ cA.inj i ≫ q) S := by
  rw [Iso.comp_inv_eq]
  exact (base_fullBatchIso_hom A B p S hS cA cB hA hB pSum hpSum q sq).symm

@[reassoc (attr := simp)]
theorem full_leg_fullBatchIso_inv :
    ((fullCoproductIso B S hS cB hB).hom ≫ g) ≫
      (fullBatchIso A B p S hS cA cB hA hB pSum hpSum q sq).inv =
        pushout.inr (attaching A (fun i ↦ cA.inj i ≫ q) S) (cellMap A B p S) := by
  rw [Iso.comp_inv_eq]
  exact (inr_fullBatchIso_hom A B p S hS cA cB hA hB pSum hpSum q sq).symm

/-- The original entire g leg is recovered using the inverse coproduct comparison. -/
theorem original_g_fullBatchIso_inv :
    g ≫ (fullBatchIso A B p S hS cA cB hA hB pSum hpSum q sq).inv =
      (fullCoproductIso B S hS cB hB).inv ≫
        pushout.inr (attaching A (fun i ↦ cA.inj i ≫ q) S) (cellMap A B p S) := by
  rw [Iso.eq_inv_comp]
  simpa [Category.assoc] using
    full_leg_fullBatchIso_inv A B p S hS cA cB hA hB pSum hpSum q sq

end

end DaggerCoproductBatchEndpoint
