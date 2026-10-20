import NativeVertexJoinReversal
import OriginalJoinedCofaces

/-! The exact vertex-join reversal respects EVERY original simplex operator. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalCounitRightConeFunctor
namespace DaggerNativeVertexJoinReversal

theorem right_blocks_ext {q r : SimplexCategory}
    {F G : ⦋q.len + 1⦌ ⟶ r}
    (hp : AugmentedSimplexCategory.inl' q ⦋0⦌ ≫ F =
      AugmentedSimplexCategory.inl' q ⦋0⦌ ≫ G)
    (hs : AugmentedSimplexCategory.inr' q ⦋0⦌ ≫ F =
      AugmentedSimplexCategory.inr' q ⦋0⦌ ≫ G) : F = G := by
  induction q using SimplexCategory.rec with | h m =>
    ext i : 3
    rcases DaggerOriginalJoinedCofaces.vertex_eq_prefix_or_suffix m 0 i with
      ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [DaggerOriginalJoinedHornGeometry.prefixIndex_eq_native]
      exact congrArg (fun h ↦ h.toOrderHom a) hp
    · rw [DaggerOriginalJoinedHornGeometry.suffixIndex_eq_native]
      exact congrArg (fun h ↦ h.toOrderHom a) hs

theorem reversed_blocks_ext {q r : SimplexCategory}
    {F G : (ordinalJoinLeft ⦋0⦌).obj q ⟶ r}
    (hp : SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ q) ≫ F =
      SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ q) ≫ G)
    (hs : SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ q) ≫ F =
      SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ q) ≫ G) : F = G := by
  apply (cancel_epi (joinIso q).inv).mp
  have he1 : AugmentedSimplexCategory.inl' q ⦋0⦌ ≫ (joinIso q).inv =
      SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ q) := by
    apply (cancel_mono (joinIso q).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, reverse_suffix]
  have he2 : AugmentedSimplexCategory.inr' q ⦋0⦌ ≫ (joinIso q).inv =
      SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ q) := by
    apply (cancel_mono (joinIso q).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, reverse_prefix]
  apply right_blocks_ext
  · simpa only [← Category.assoc, he1] using hs
  · simpa only [← Category.assoc, he2] using hp

theorem right_prefix_comp {m n : SimplexCategory} (α : m ⟶ n) :
    AugmentedSimplexCategory.inl' m ⦋0⦌ ≫ joinHom α =
      α ≫ AugmentedSimplexCategory.inl' n ⦋0⦌ :=
  AugmentedSimplexCategory.inl_comp_tensorHom
    (show CategoryTheory.WithInitial.of m ⟶ CategoryTheory.WithInitial.of n from α)
    (𝟙 (CategoryTheory.WithInitial.of ⦋0⦌))

theorem right_suffix_comp {m n : SimplexCategory} (α : m ⟶ n) :
    AugmentedSimplexCategory.inr' m ⦋0⦌ ≫ joinHom α =
      AugmentedSimplexCategory.inr' n ⦋0⦌ := by
  have h := AugmentedSimplexCategory.inr_comp_tensorHom
    (show CategoryTheory.WithInitial.of m ⟶ CategoryTheory.WithInitial.of n from α)
    (𝟙 (CategoryTheory.WithInitial.of ⦋0⦌))
  simpa only [Category.id_comp] using h

theorem join_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    SimplexCategory.rev.map ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.rev.map α)) ≫
        (joinIso n).hom = (joinIso m).hom ≫ joinHom α := by
  cases m using SimplexCategory.rec
  rename_i mLen
  cases n using SimplexCategory.rec
  rename_i nLen
  let m : SimplexCategory := ⦋mLen⦌
  let n : SimplexCategory := ⦋nLen⦌
  apply reversed_blocks_ext (q := m)
  · calc
      _ = SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ m ≫
          (ordinalJoinLeft ⦋0⦌).map (SimplexCategory.rev.map α)) ≫ (joinIso n).hom := by
            rw [Functor.map_comp, Category.assoc]
      _ = SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ n) ≫
          (joinIso n).hom := by
            rw [prefix_comp]
            simp only [SimplexCategory.rev_obj, n]
      _ = AugmentedSimplexCategory.inr' n ⦋0⦌ := reverse_prefix n
      _ = AugmentedSimplexCategory.inr' m ⦋0⦌ ≫ joinHom α := (right_suffix_comp α).symm
      _ = _ := by rw [← Category.assoc, reverse_prefix]
  · calc
      _ = SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ m ≫
          (ordinalJoinLeft ⦋0⦌).map (SimplexCategory.rev.map α)) ≫ (joinIso n).hom := by
            rw [Functor.map_comp, Category.assoc]
      _ = SimplexCategory.rev.map (SimplexCategory.rev.map α ≫
          AugmentedSimplexCategory.inr' ⦋0⦌ n) ≫ (joinIso n).hom := by
            rw [suffix_comp]
            simp only [SimplexCategory.rev_obj, m, n]
      _ = α ≫ AugmentedSimplexCategory.inl' n ⦋0⦌ := by
        rw [Functor.map_comp, SimplexCategory.rev_map_rev_map, Category.assoc]
        exact congrArg (fun f ↦ α ≫ f) (reverse_suffix n)
      _ = AugmentedSimplexCategory.inl' m ⦋0⦌ ≫ joinHom α := (right_prefix_comp α).symm
      _ = _ := by rw [← Category.assoc, reverse_suffix]

end DaggerNativeVertexJoinReversal
