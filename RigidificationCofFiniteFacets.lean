import RigidificationCofOmitted

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.PathFacets

abbrev vertices (n : ℕ) := ULift.{u} (Fin (n + 1))

def deltaEmbedding {n : ℕ} (k : Fin (n + 2)) : vertices.{u} n ↪o vertices.{u} (n + 1) where
  toFun x := ⟨k.succAbove x.down⟩
  inj' _ _ h := ULift.ext _ _ ((Fin.succAboveOrderEmb k).injective (congrArg ULift.down h))
  map_rel_iff' := (Fin.succAboveOrderEmb k).map_rel_iff'

theorem range_deltaEmbedding {n : ℕ} (k : Fin (n + 2)) :
    Set.range (deltaEmbedding.{u} k) = {ULift.up k}ᶜ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ h
    exact Fin.succAbove_ne k y.down (congrArg ULift.down h)
  · intro h
    have h' : x.down ∈ Set.range k.succAbove := by
      rw [Fin.range_succAbove]
      exact fun hx => h (ULift.ext _ _ hx)
    obtain ⟨y, hy⟩ := h'
    exact ⟨⟨y⟩, ULift.ext _ _ hy⟩

theorem deltaEmbedding_toOrderHom {n : ℕ} (k : Fin (n + 2)) :
    (deltaEmbedding.{u} k).toOrderHom = (SimplexCategory.δ k).toOrderHom.uliftMap := rfl

/-- The full omit iso uses the SAME original codimension-one simplex operator. -/
noncomputable def deltaOmittedIso {n : ℕ} (k : Fin (n + 2)) (i j : vertices.{u} n) :
    hom i j ≅ (omitted (deltaEmbedding k i) (deltaEmbedding k j) (ULift.up k)).toSSet :=
  omittedIso (deltaEmbedding k) (ULift.up k) (range_deltaEmbedding k) i j

@[reassoc (attr := simp)] theorem deltaOmittedIso_hom_ι {n : ℕ}
    (k : Fin (n + 2)) (i j : vertices.{u} n) :
    (deltaOmittedIso k i j).hom ≫
      (omitted (deltaEmbedding k i) (deltaEmbedding k j) (ULift.up k)).ι =
      (DaggerModels.OrdinaryRigidification.cosimplicialThickening.map
        (SimplexCategory.δ k)).map (.mk i) (.mk j) := rfl

theorem deltaEmbedding_zero {n : ℕ} (k : Fin (n + 2)) (hk : k ≠ 0) :
    deltaEmbedding.{u} k (ULift.up 0) = ULift.up 0 := by
  apply ULift.ext
  exact Fin.succAbove_ne_zero_zero hk

theorem deltaEmbedding_last {n : ℕ} (k : Fin (n + 2)) (hk : k ≠ Fin.last (n + 1)) :
    deltaEmbedding.{u} k (ULift.up (Fin.last n)) = ULift.up (Fin.last (n + 1)) := by
  apply ULift.ext
  exact Fin.succAbove_ne_last_last hk

/-- All overlap predicates retain every original chain entry. -/
theorem omitted_cut_disjoint {J : Type u} [LinearOrder J] (i j k : J) :
    omitted i j k ⊓ cut i j k = ⊥ := by
  apply le_antisymm
  · intro q γ h
    exact (h.1 0) (h.2 0)
  · exact bot_le

end DaggerOrdinaryRigidificationCof.PathFacets
