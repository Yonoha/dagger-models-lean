import CoproductBatchContinuity
import CoproductBatchEndpoint
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.SetTheory.Cardinal.Order

set_option autoImplicit false

/-! Serialize the same arbitrary original coproduct pushout by its original indexed cells. -/

open CategoryTheory Limits DaggerCoproductPartialBatch
open DaggerCoproductBatchContinuity DaggerCoproductBatchEndpoint

universe w v u

namespace DaggerCoproductCellSerialization

noncomputable section

variable {C : Type u} [Category.{v} C] {I : Type w}
  [HasCoproducts.{w} C] [HasPushouts C]

section Ordered

variable [LinearOrder I] (A B : I → C) (p : ∀ i, A i ⟶ B i)
  {X : C} (a : ∀ i, A i ⟶ X)

section Successors

variable [SuccOrder (WithTop I)]

/-- A successor prefix adds precisely the same original index. -/
theorem prefix_succ (i : I) :
    prefixSet (Order.succ (i : WithTop I)) = insert i (prefixSet (i : WithTop I)) := by
  ext k
  simpa only [prefixSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_Iio,
    WithTop.coe_inj] using
    (Set.ext_iff.mp (Order.Iio_succ_eq_insert_of_not_isMax
      (not_isMax_of_lt (WithTop.coe_lt_top i))) (k : WithTop I))

/-- The entire successor square retains the literal original p_i. -/
theorem successor_isPushout (i : I) :
    IsPushout (a i ≫ base A B p a (prefixSet (i : WithTop I))) (p i)
      ((chain A B p a).map (homOfLE (Order.le_succ (i : WithTop I))))
      (cell A B p a (prefixSet (Order.succ (i : WithTop I))) ⟨i, coe_lt_succ i⟩) := by
  have aux (T : Set I) (hT : T = insert i (prefixSet (i : WithTop I)))
      (hST : prefixSet (i : WithTop I) ⊆ T) (hi : i ∈ T) :
      IsPushout (a i ≫ base A B p a (prefixSet (i : WithTop I))) (p i)
        (transition A B p a hST) (cell A B p a T ⟨i, hi⟩) := by
    subst T
    exact singleton_isPushout A B p a (prefixSet (i : WithTop I)) i
      (by change ¬ (i : WithTop I) < i; exact lt_irrefl _)
  exact aux _ (prefix_succ i) (prefix_mono (Order.le_succ (i : WithTop I))) (coe_lt_succ i)

end Successors

variable (cA : Cofan A) (cB : Cofan B) (hA : IsColimit cA) (hB : IsColimit cB)
  (pSum : cA.pt ⟶ cB.pt) (hpSum : ∀ i, cA.inj i ≫ pSum = p i ≫ cB.inj i)
  {Y : C} (q : cA.pt ⟶ X) {f : X ⟶ Y} {g : cB.pt ⟶ Y}
  (sq : IsPushout q pSum f g)

include hpSum sq in
omit [HasCoproducts.{w} C] [HasPushouts C] [LinearOrder I] in
theorem original_relation (i : I) :
    (cA.inj i ≫ q) ≫ f = p i ≫ (cB.inj i ≫ g) := by
  rw [Category.assoc, sq.w, ← Category.assoc, hpSum, Category.assoc]

/-- Every stage maps to the SAME original Y by the entire original f and B_i legs. -/
def inclusionApp (j : WithTop I) :
    (chain A B p (fun i ↦ cA.inj i ≫ q)).obj j ⟶ Y :=
  desc A B p (fun i ↦ cA.inj i ≫ q) (prefixSet j) f
    (fun i ↦ cB.inj i.1 ≫ g)
    (fun i ↦ original_relation A B p cA cB pSum hpSum q sq i.1)

@[reassoc (attr := simp)]
theorem base_inclusionApp (j : WithTop I) :
    base A B p (fun i ↦ cA.inj i ≫ q) (prefixSet j) ≫
      inclusionApp A B p cA cB pSum hpSum q sq j = f := by
  simp [inclusionApp]

@[reassoc (attr := simp)]
theorem cell_inclusionApp (j : WithTop I) (i : prefixSet j) :
    cell A B p (fun i ↦ cA.inj i ≫ q) (prefixSet j) i ≫
      inclusionApp A B p cA cB pSum hpSum q sq j = cB.inj i.1 ≫ g := by
  simp [inclusionApp]

/-- Naturality includes every entire original partial-batch transition. -/
def inclusion : chain A B p (fun i ↦ cA.inj i ≫ q) ⟶ (Functor.const _).obj Y where
  app := inclusionApp A B p cA cB pSum hpSum q sq
  naturality j k φ := by
    dsimp
    apply DaggerCoproductPartialBatch.hom_ext A B p (fun i ↦ cA.inj i ≫ q) (prefixSet j)
    · simp
    · intro i
      simp

/-- The top object is compared to the original pushout with both complete original legs. -/
def topIso : (chain A B p (fun i ↦ cA.inj i ≫ q)).obj ⊤ ≅ Y :=
  fullBatchIso A B p (prefixSet (⊤ : WithTop I)) (fun i ↦ WithTop.coe_lt_top i)
    cA cB hA hB pSum hpSum q sq

theorem inclusion_eq_top (j : WithTop I) :
    (inclusion A B p cA cB pSum hpSum q sq).app j =
      (chain A B p (fun i ↦ cA.inj i ≫ q)).map (homOfLE le_top) ≫
        (topIso A B p cA cB hA hB pSum hpSum q sq).hom := by
  apply DaggerCoproductPartialBatch.hom_ext A B p (fun i ↦ cA.inj i ≫ q) (prefixSet j)
  · simp [inclusion, topIso]
  · intro i
    simp [inclusion, topIso]

/-- The original Y cocone has the complete arbitrary-target colimit universal property. -/
def finalIsColimit : IsColimit (Cocone.mk Y (inclusion A B p cA cB pSum hpSum q sq)) :=
  (colimitOfDiagramTerminal isTerminalTop (chain A B p (fun i ↦ cA.inj i ≫ q))).ofIsoColimit
    (Cocones.ext (topIso A B p cA cB hA hB pSum hpSum q sq) (fun j ↦ by
      change (chain A B p (fun i ↦ cA.inj i ≫ q)).map (isTerminalTop.from j) ≫
        (topIso A B p cA cB hA hB pSum hpSum q sq).hom = _
      rw [show isTerminalTop.from j = homOfLE (le_top : j ≤ ⊤) from Subsingleton.elim _ _]
      exact (inclusion_eq_top A B p cA cB hA hB pSum hpSum q sq j).symm))

variable [WellFoundedLT I] [OrderBot (WithTop I)] [SuccOrder (WithTop I)]

/-- A full transfinite record for the SAME original f, with every actual singleton pushout. -/
def orderedSerialization (P : MorphismProperty C) (hp : ∀ i, P (p i)) :
    P.pushouts.TransfiniteCompositionOfShape (WithTop I) f where
  F := chain A B p (fun i ↦ cA.inj i ≫ q)
  isoBot := isoBot A B p (fun i ↦ cA.inj i ≫ q)
  incl := inclusion A B p cA cB pSum hpSum q sq
  isColimit := finalIsColimit A B p cA cB hA hB pSum hpSum q sq
  fac := base_inclusionApp A B p cA cB pSum hpSum q sq ⊥
  map_mem j hj := by
    induction j using WithTop.recTopCoe with
    | top => exact (hj isMax_top).elim
    | coe i =>
      exact P.pushouts_mk (successor_isPushout A B p (fun i ↦ cA.inj i ≫ q) i) (hp i)

end Ordered

/-- Choose a well order on the same original I; the empty I case uses the same zero-edge record. -/
theorem original_mem (P : MorphismProperty C) (A B : I → C) (p : ∀ i, A i ⟶ B i)
    (hp : ∀ i, P (p i)) (cA : Cofan A) (cB : Cofan B)
    (hA : IsColimit cA) (hB : IsColimit cB) (pSum : cA.pt ⟶ cB.pt)
    (hpSum : ∀ i, cA.inj i ≫ pSum = p i ≫ cB.inj i)
    {X Y : C} (q : cA.pt ⟶ X) {f : X ⟶ Y} {g : cB.pt ⟶ Y}
    (sq : IsPushout q pSum f g) : MorphismProperty.transfiniteCompositions.{w} P.pushouts f := by
  obtain ⟨o, ho⟩ := exists_wellOrder I
  let : LinearOrder I := o
  let : WellFoundedLT I := ho
  let : OrderBot (WithTop I) := withTopOrderBot
  let : SuccOrder (WithTop I) := withTopSuccOrder
  exact P.pushouts.transfiniteCompositionsOfShape_le_transfiniteCompositions (WithTop I) _
    ⟨orderedSerialization A B p cA cB hA hB pSum hpSum q sq P hp⟩

omit [HasCoproducts.{w} C] [HasPushouts C] in
/-- Read an arbitrary original discrete cocone as a cofan without changing its vertex. -/
def discreteCofan {F : Discrete I ⥤ C} (c : Cocone F) : Cofan (fun i ↦ F.obj ⟨i⟩) :=
  (Cocones.precompose (Discrete.natIsoFunctor (F := F)).inv).obj c

omit [HasCoproducts.{w} C] [HasPushouts C] in
@[simp]
theorem discreteCofan_pt {F : Discrete I ⥤ C} (c : Cocone F) :
    (discreteCofan c).pt = c.pt := rfl

omit [HasCoproducts.{w} C] [HasPushouts C] in
@[simp]
theorem discreteCofan_inj {F : Discrete I ⥤ C} (c : Cocone F) (i : I) :
    (discreteCofan c).inj i = c.ι.app ⟨i⟩ := by
  change (𝟙 (F.obj ⟨i⟩)) ≫ c.ι.app ⟨i⟩ = c.ι.app ⟨i⟩
  simp

omit [HasCoproducts.{w} C] [HasPushouts C] in
def discreteCofanIsColimit {F : Discrete I ⥤ C} {c : Cocone F} (hc : IsColimit c) :
    IsColimit (discreteCofan c) :=
  (IsColimit.precomposeInvEquiv (Discrete.natIsoFunctor (F := F)) c).symm hc

/-- Arbitrary discrete colimit witnesses and their actual original pushout are serialized. -/
theorem coproduct_pushouts_le (P : MorphismProperty C) :
    (MorphismProperty.coproducts.{w} P).pushouts ≤
      MorphismProperty.transfiniteCompositions.{w} P.pushouts := by
  rintro X Y f ⟨A0, B0, pSum, q, g, hpSum, sq⟩
  obtain ⟨I, hI⟩ := (P.coproducts_iff pSum).mp hpSum
  rcases hI with ⟨F, G, cF, cG, hF, hG, t, ht⟩
  apply original_mem P (fun i ↦ F.obj ⟨i⟩) (fun i ↦ G.obj ⟨i⟩)
    (fun i ↦ t.app ⟨i⟩) (fun i ↦ ht ⟨i⟩) (discreteCofan cF) (discreteCofan cG)
    (discreteCofanIsColimit hF) (discreteCofanIsColimit hG) _ _ q sq
  intro i
  simpa only [discreteCofan_inj, NatTrans.comp_app] using
    hF.fac (Cocone.mk _ (t ≫ cG.ι)) ⟨i⟩

end

end DaggerCoproductCellSerialization
