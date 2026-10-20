import OriginalOrdinalJoinLeft
import OriginalCounitRightConeFunctor
import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-! Native ordinal reversal exchanges the two original vertex-join inclusions. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalCounitRightConeFunctor
namespace DaggerNativeVertexJoinReversal

def reindex (a b : SimplexCategory) (h : a.len = b.len) : a ⟶ b := by
  induction a using SimplexCategory.rec with | h na =>
    induction b using SimplexCategory.rec with | h nb =>
      exact SimplexCategory.mkHom
        ⟨fun i ↦ ⟨i.val, by change na = nb at h; have := i.isLt; omega⟩, fun _ _ h ↦ h⟩

def joinIso (q : SimplexCategory) : (ordinalJoinLeft ⦋0⦌).obj q ≅ ⦋q.len + 1⦌ where
  hom := reindex _ _ (by simp [ordinalJoinLeft, AugmentedSimplexCategory.tensorObjOf])
  inv := reindex _ _ (by simp [ordinalJoinLeft, AugmentedSimplexCategory.tensorObjOf])
  hom_inv_id := by ext i : 3; rfl
  inv_hom_id := by ext i : 3; rfl

theorem reverse_prefix (q : SimplexCategory) :
    SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ q) ≫ (joinIso q).hom =
      AugmentedSimplexCategory.inr' q ⦋0⦌ := by
  ext i : 3
  apply Fin.ext
  change ((SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ q)).toOrderHom i).val =
    ((AugmentedSimplexCategory.inr' q ⦋0⦌).toOrderHom i).val
  rw [SimplexCategory.rev_map_apply]
  have hl := congrArg Fin.val (AugmentedSimplexCategory.inl'_eval ⦋0⦌ q i.rev)
  have hr := congrArg Fin.val (AugmentedSimplexCategory.inr'_eval q ⦋0⦌ i)
  simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    SimplexCategory.len_mk] at *
  dsimp only [SimplexCategory.rev, AugmentedSimplexCategory.tensorObjOf] at *
  simp only [SimplexCategory.len_mk] at *
  have hi := i.isLt
  change i.val < 1 at hi
  omega

theorem reverse_suffix (q : SimplexCategory) :
    SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ q) ≫ (joinIso q).hom =
      AugmentedSimplexCategory.inl' q ⦋0⦌ := by
  ext i : 3
  apply Fin.ext
  change ((SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ q)).toOrderHom i).val =
    ((AugmentedSimplexCategory.inl' q ⦋0⦌).toOrderHom i).val
  rw [SimplexCategory.rev_map_apply]
  have hl := congrArg Fin.val (AugmentedSimplexCategory.inr'_eval ⦋0⦌ q i.rev)
  have hr := congrArg Fin.val (AugmentedSimplexCategory.inl'_eval q ⦋0⦌ i)
  simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    SimplexCategory.len_mk] at *
  dsimp only [SimplexCategory.rev, AugmentedSimplexCategory.tensorObjOf] at *
  simp only [SimplexCategory.len_mk] at *
  have hi := i.isLt
  omega

end DaggerNativeVertexJoinReversal
