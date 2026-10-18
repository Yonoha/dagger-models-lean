import RigidificationCofFaceData

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

variable {n : ℕ} {A : SC.{u}}

def faceDimension (s : Finset (Fin (n + 1))) : ℕ := s.card - 1

def faceOrderIso (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Fin (faceDimension s + 1) ≃o s :=
  s.orderIsoOfFin (Nat.sub_add_cancel (Finset.card_pos.mpr hs)).symm

def faceForward (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Fin (faceDimension s + 1) →o s where
  toFun i := faceOrderIso s hs i
  monotone' _ _ h := (faceOrderIso s hs).map_rel_iff'.mpr h

def faceBackward (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    s →o Fin (faceDimension s + 1) where
  toFun i := (faceOrderIso s hs).symm i
  monotone' _ _ h := (faceOrderIso s hs).symm.map_rel_iff'.mpr h

def faceOrdinal (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    ⦋faceDimension s⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i => (faceOrderIso s hs i).val
      monotone' := fun _ _ h => (faceOrderIso s hs).map_rel_iff'.mpr h }

theorem faceOrdinal_not_surjective (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (hp : s ≠ Finset.univ) : ¬ Function.Surjective (faceOrdinal s hs).toOrderHom := by
  intro h
  apply hp
  apply Finset.eq_univ_of_forall
  intro i
  obtain ⟨j, rfl⟩ := h i
  exact (faceOrderIso s hs j).property

/-- A proper nonempty face has the full original enriched functor on its literal vertices. -/
def faceFunctor (a : (SSet.boundary n).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (hp : s ≠ Finset.univ) :
    DaggerModels.SimplicialCat.of (SimplicialThickening (ULift.{u} s)) ⟶ A :=
  SimplicialThickening.functor (faceBackward s hs).uliftMap ≫
    simplex (n := ⦋n⦌) a (faceOrdinal s hs) (faceOrdinal_not_surjective s hs hp)

def faceInclusion {s t : Finset (Fin (n + 1))} (hst : s ⊆ t) : s →o t where
  toFun i := ⟨i.val, hst i.property⟩
  monotone' _ _ h := h

def restrictionOrdinal (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) : ⦋faceDimension s⦌ ⟶ ⦋faceDimension t⦌ :=
  SimplexCategory.mkHom ((faceBackward t ht).comp
    ((faceInclusion hst).comp (faceForward s hs)))

theorem restrictionOrdinal_comp (s t : Finset (Fin (n + 1)))
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) :
    restrictionOrdinal s t hs ht hst ≫ faceOrdinal t ht = faceOrdinal s hs := by
  ext i
  change (((faceOrderIso t ht) ((faceOrderIso t ht).symm _)).val).val = _
  simp only [OrderIso.apply_symm_apply]
  rfl

/-- Restriction is equality of WHOLE enriched functors, not only of their vertices. -/
theorem faceFunctor_restrict (a : (SSet.boundary n).toSSet ⟶ N.obj A)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hps : s ≠ Finset.univ) (hpt : t ≠ Finset.univ) (hst : s ⊆ t) :
    SimplicialThickening.functor (faceInclusion hst).uliftMap ≫
      faceFunctor a t ht hpt = faceFunctor a s hs hps := by
  have h₀ := simplex_precompose (n := ⦋n⦌) a (faceOrdinal t ht)
    (faceOrdinal_not_surjective t ht hpt) (restrictionOrdinal s t hs ht hst)
  have h := h₀.trans (simplex_eq (d := ⦋n⦌) a
    (restrictionOrdinal_comp s t hs ht hst) _ (faceOrdinal_not_surjective s hs hps))
  unfold faceFunctor
  rw [← Category.assoc]
  rw [← h, ← Category.assoc]
  congr 1
  change EnrichedFunctor.comp SSet
      (SimplicialThickening.functor (faceInclusion hst).uliftMap)
      (SimplicialThickening.functor (faceBackward t ht).uliftMap) =
    EnrichedFunctor.comp SSet
      (SimplicialThickening.functor (faceBackward s hs).uliftMap)
      (SimplicialThickening.functor
        (restrictionOrdinal s t hs ht hst).toOrderHom.uliftMap)
  rw [← SimplicialThickening.functor_comp, ← SimplicialThickening.functor_comp]
  congr 1
  apply DFunLike.ext
  intro i
  apply ULift.ext
  change (faceOrderIso t ht).symm ((faceInclusion hst) i.down) =
    (faceOrderIso t ht).symm ((faceInclusion hst)
      ((faceOrderIso s hs) ((faceOrderIso s hs).symm i.down)))
  simp only [OrderIso.apply_symm_apply]

end

end DaggerOrdinaryRigidificationCof.BoundaryData
