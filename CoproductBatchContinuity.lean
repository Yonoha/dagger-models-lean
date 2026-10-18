import CoproductPartialBatch
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
import Mathlib.Order.WellFounded
import Mathlib.Order.WithBot

set_option autoImplicit false

/-! The actual original partial-batch chain, with its complete limit-stage universal property. -/

open CategoryTheory Limits
open DaggerCoproductPartialBatch

universe w v u

namespace DaggerCoproductBatchContinuity

variable {C : Type u} [Category.{v} C] {I : Type w}
  [HasCoproducts.{w} C] [HasPushouts C] [LinearOrder I]
  (A B : I → C) (p : ∀ i, A i ⟶ B i) {X : C} (a : ∀ i, A i ⟶ X)

/-- Prefixes use the standard extended order on the same original index type. -/
abbrev prefixSet (j : WithTop I) : Set I := {i | (i : WithTop I) < j}

theorem prefix_mono {j k : WithTop I} (h : j ≤ k) : prefixSet j ⊆ prefixSet k :=
  fun _ hi ↦ hi.trans_le h

/-- Each stage is the original partial pushout; each arrow is its original transition. -/
noncomputable def chain : WithTop I ⥤ C where
  obj j := batch A B p a (prefixSet j)
  map f := transition A B p a (prefix_mono (leOfHom f))
  map_id j := transition_id A B p a (prefixSet j)
  map_comp f g := (transition_comp A B p a
    (prefix_mono (leOfHom f)) (prefix_mono (leOfHom g))).symm

@[reassoc (attr := simp)]
theorem base_map {j k : WithTop I} (f : j ⟶ k) :
    base A B p a (prefixSet j) ≫ (chain A B p a).map f = base A B p a (prefixSet k) :=
  base_transition A B p a (prefix_mono (leOfHom f))

@[reassoc (attr := simp)]
theorem cell_map {j k : WithTop I} (f : j ⟶ k) (i : prefixSet j) :
    cell A B p a (prefixSet j) i ≫ (chain A B p a).map f =
      cell A B p a (prefixSet k) ⟨i.1, prefix_mono (leOfHom f) i.2⟩ :=
  cell_transition A B p a (prefix_mono (leOfHom f)) i

/-- Only the extended type needs a bottom, even when the original index type is empty. -/
noncomputable def withTopOrderBot [WellFoundedLT I] : OrderBot (WithTop I) :=
  WellFoundedLT.toOrderBot

/-- The well-order successor belongs to the standard extended order. -/
noncomputable def withTopSuccOrder [WellFoundedLT I] : SuccOrder (WithTop I) :=
  SuccOrder.ofLinearWellFoundedLT (WithTop I)

variable [OrderBot (WithTop I)]

theorem prefix_bot : prefixSet (⊥ : WithTop I) = ∅ := by
  ext i
  change ((i : WithTop I) < ⊥) ↔ False
  exact iff_false_intro (not_lt_bot : ¬ (i : WithTop I) < ⊥)

/-- The original source iso has inverse literally equal to the original base leg. -/
noncomputable def isoBot : (chain A B p a).obj ⊥ ≅ X where
  hom := desc A B p a (prefixSet ⊥) (𝟙 X)
    (fun i ↦ False.elim (not_lt_bot (show (i.1 : WithTop I) < ⊥ from i.2)))
    (fun i ↦ False.elim (not_lt_bot (show (i.1 : WithTop I) < ⊥ from i.2)))
  inv := base A B p a (prefixSet ⊥)
  hom_inv_id := by
    apply DaggerCoproductPartialBatch.hom_ext A B p a (prefixSet ⊥)
    · rw [← Category.assoc, base_desc]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    · intro i
      exact False.elim (not_lt_bot (show (i.1 : WithTop I) < ⊥ from i.2))
  inv_hom_id := by simp

@[simp]
theorem isoBot_inv : (isoBot A B p a).inv = base A B p a (prefixSet ⊥) := rfl

variable [SuccOrder (WithTop I)]

omit [OrderBot (WithTop I)] in
theorem coe_lt_succ (i : I) : (i : WithTop I) < Order.succ (i : WithTop I) :=
  Order.lt_succ_of_not_isMax (not_isMax_of_lt (WithTop.coe_lt_top i))

/-- The lower diagram is literally the principal segment of the original chain. -/
noncomputable abbrev lowerChain (m : WithTop I) : Set.Iio m ⥤ C :=
  (Set.principalSegIio m).monotone.functor ⋙ chain A B p a

variable {m : WithTop I} (hm : Order.IsSuccLimit m)

def bottomStage : Set.Iio m := ⟨⊥, bot_lt_iff_ne_bot.mpr hm.ne_bot⟩

/-- An original cell first occurs at its actual successor stage, still below the limit. -/
def cellStage (i : prefixSet m) : Set.Iio m :=
  ⟨Order.succ (i.1 : WithTop I), hm.succ_lt_iff.mpr i.2⟩

noncomputable def limitBase (s : Cocone (lowerChain A B p a m)) : X ⟶ s.pt :=
  base A B p a (prefixSet ⊥) ≫ s.ι.app (bottomStage hm)

noncomputable def limitCell (s : Cocone (lowerChain A B p a m)) (i : prefixSet m) :
    B i.1 ⟶ s.pt :=
  cell A B p a (prefixSet (Order.succ (i.1 : WithTop I))) ⟨i.1, coe_lt_succ i.1⟩ ≫
    s.ι.app (cellStage hm i)

omit [SuccOrder (WithTop I)] in
/-- Every earlier base leg agrees with the single chosen bottom component. -/
theorem limitBase_at_stage (s : Cocone (lowerChain A B p a m)) (j : Set.Iio m) :
    base A B p a (prefixSet j.1) ≫ s.ι.app j = limitBase A B p a hm s := by
  have h := congrArg (fun f ↦ base A B p a (prefixSet ⊥) ≫ f)
    (s.w (homOfLE (show (bottomStage hm).1 ≤ j.1 from bot_le) : bottomStage hm ⟶ j))
  change base A B p a (prefixSet ⊥) ≫
    ((chain A B p a).map (homOfLE bot_le) ≫ s.ι.app j) = _ at h
  rw [← Category.assoc, base_map] at h
  exact h

omit [OrderBot (WithTop I)] in
/-- Cocone naturality compares the chosen cell with every earlier occurrence directly. -/
theorem limitCell_at_stage (s : Cocone (lowerChain A B p a m)) (j : Set.Iio m)
    (i : prefixSet j.1) :
    cell A B p a (prefixSet j.1) i ≫ s.ι.app j =
      limitCell A B p a hm s ⟨i.1, prefix_mono j.2.le i.2⟩ := by
  have h := congrArg (fun f ↦
    cell A B p a (prefixSet (Order.succ (i.1 : WithTop I))) ⟨i.1, coe_lt_succ i.1⟩ ≫ f)
    (s.w (homOfLE (show (cellStage hm ⟨i.1, prefix_mono j.2.le i.2⟩).1 ≤ j.1 from
      Order.succ_le_of_lt (show (i.1 : WithTop I) < j.1 from i.2)) :
        cellStage hm ⟨i.1, prefix_mono j.2.le i.2⟩ ⟶ j))
  change cell A B p a (prefixSet (Order.succ (i.1 : WithTop I))) _ ≫
    ((chain A B p a).map (homOfLE (Order.succ_le_of_lt i.2)) ≫ s.ι.app j) = _ at h
  rw [← Category.assoc, cell_map] at h
  exact h

theorem limit_relation (s : Cocone (lowerChain A B p a m)) (i : prefixSet m) :
    a i.1 ≫ limitBase A B p a hm s = p i.1 ≫ limitCell A B p a hm s i := by
  have h := congrArg (fun f ↦ f ≫ s.ι.app (cellStage hm i))
    (relation A B p a (prefixSet (Order.succ (i.1 : WithTop I))) ⟨i.1, coe_lt_succ i.1⟩)
  simp only [Category.assoc] at h
  change a i.1 ≫ (base A B p a (prefixSet (cellStage hm i).1) ≫
    s.ι.app (cellStage hm i)) = p i.1 ≫ limitCell A B p a hm s i at h
  rw [limitBase_at_stage] at h
  exact h

/-- Desc to any cocone target uses the same original base and every original cell leg. -/
noncomputable def limitDesc (s : Cocone (lowerChain A B p a m)) :
    (chain A B p a).obj m ⟶ s.pt :=
  desc A B p a (prefixSet m) (limitBase A B p a hm s) (limitCell A B p a hm s)
    (limit_relation A B p a hm s)

@[reassoc (attr := simp)]
theorem base_limitDesc (s : Cocone (lowerChain A B p a m)) :
    base A B p a (prefixSet m) ≫ limitDesc A B p a hm s = limitBase A B p a hm s :=
  base_desc A B p a _ _ _ _

@[reassoc (attr := simp)]
theorem cell_limitDesc (s : Cocone (lowerChain A B p a m)) (i : prefixSet m) :
    cell A B p a (prefixSet m) i ≫ limitDesc A B p a hm s = limitCell A B p a hm s i :=
  cell_desc A B p a _ _ _ _ i

/-- Every entire lower-stage cocone leg factors, not only eventual cell components. -/
theorem limitDesc_fac (s : Cocone (lowerChain A B p a m)) (j : Set.Iio m) :
    ((Set.principalSegIio m).cocone (chain A B p a)).ι.app j ≫
      limitDesc A B p a hm s = s.ι.app j := by
  change (chain A B p a).map (homOfLE j.2.le) ≫ limitDesc A B p a hm s = s.ι.app j
  apply DaggerCoproductPartialBatch.hom_ext A B p a (prefixSet j.1)
  · rw [← Category.assoc, base_map, base_limitDesc]
    exact (limitBase_at_stage A B p a hm s j).symm
  · intro i
    rw [← Category.assoc, cell_map, cell_limitDesc]
    exact (limitCell_at_stage A B p a hm s j i).symm

/-- An arbitrary morphism with all original lower legs is the same unique desc. -/
theorem limitDesc_unique (s : Cocone (lowerChain A B p a m))
    (f : (chain A B p a).obj m ⟶ s.pt)
    (hf : ∀ j : Set.Iio m,
      ((Set.principalSegIio m).cocone (chain A B p a)).ι.app j ≫ f = s.ι.app j) :
    f = limitDesc A B p a hm s := by
  apply desc_unique A B p a (prefixSet m) _ _ _ f
  · have h := congrArg (fun t ↦ base A B p a (prefixSet ⊥) ≫ t) (hf (bottomStage hm))
    change base A B p a (prefixSet ⊥) ≫
      ((chain A B p a).map (homOfLE (bottomStage hm).2.le) ≫ f) = _ at h
    rw [← Category.assoc, base_map] at h
    exact h
  · intro i
    have h := congrArg (fun t ↦
      cell A B p a (prefixSet (Order.succ (i.1 : WithTop I))) ⟨i.1, coe_lt_succ i.1⟩ ≫ t)
      (hf (cellStage hm i))
    change cell A B p a (prefixSet (Order.succ (i.1 : WithTop I))) _ ≫
      ((chain A B p a).map (homOfLE (cellStage hm i).2.le) ≫ f) = _ at h
    rw [← Category.assoc, cell_map] at h
    exact h

/-- Complete original limit-stage UP, with arbitrary target desc, every fac and full uniq. -/
noncomputable def limitIsColimit :
    IsColimit ((Set.principalSegIio m).cocone (chain A B p a)) where
  desc := limitDesc A B p a hm
  fac := limitDesc_fac A B p a hm
  uniq := limitDesc_unique A B p a hm

instance isWellOrderContinuous : (chain A B p a).IsWellOrderContinuous where
  nonempty_isColimit _ hm := ⟨limitIsColimit A B p a hm⟩

end DaggerCoproductBatchContinuity
