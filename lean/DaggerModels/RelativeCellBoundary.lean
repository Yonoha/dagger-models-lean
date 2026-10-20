import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# Boundaries of relative simplicial cells

These are the ordinary simplicial-set ingredients for the relative boundary-cell
presentation in Part I, `dj.lem.free-cof`. Pullback along a simplex-category epimorphism
reflects membership in every subcomplex. Consequently, the characteristic map of a new
nondegenerate `n`-simplex has inverse image of the previous relative stage exactly its
boundary. The characteristic map is not assumed to be a monomorphism.
-/

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.RelativeCellBoundary

/-- Degenerating a simplex reflects as well as preserves membership in a subcomplex. -/
theorem mem_of_epi_pullback_iff {B : SSet.{u}} (K : B.Subcomplex)
    {k n : SimplexCategory} (α : k ⟶ n) [Epi α] (x : B.obj (op n)) :
    B.map α.op x ∈ K.obj (op k) ↔ x ∈ K.obj (op n) := by
  have : IsSplitEpi α := isSplitEpi_of_epi α
  refine ⟨fun hx ↦ ?_, fun hx ↦ K.map α.op hx⟩
  have h := K.map (section_ α).op hx
  change B.map (section_ α).op (B.map α.op x) ∈ K.obj (op n) at h
  simpa only [← FunctorToTypes.map_comp_apply, ← op_comp, IsSplitEpi.id,
    op_id, FunctorToTypes.map_id_apply] using h

/-- The new cell's characteristic map meets the previous relative stage exactly on its boundary. -/
theorem characteristic_preimage_relativeSkeleton {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (n : ℕ) (σ : B.nonDegenerate n)
    (hσ : σ.1 ∉ Set.range (i.app (op ⦋n⦌))) :
    (SSet.skeletonOfMono i n).preimage (SSet.yonedaEquiv.symm σ.1) = SSet.boundary n := by
  ext k s
  change B.map s.down.op σ.1 ∈ (SSet.skeletonOfMono i n).obj k ↔
    ¬ Function.Surjective s.down.toOrderHom
  constructor
  · intro hs hsurj
    have : Epi s.down := SimplexCategory.epi_iff_surjective.mpr hsurj
    have hmem := (mem_of_epi_pullback_iff (SSet.skeletonOfMono i n) s.down σ.1).mp hs
    rcases (SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i σ n).mp hmem with h | h
    · exact hσ h
    · exact (Nat.lt_irrefl n) h
  · intro hs
    cases n with
    | zero =>
        apply False.elim (hs ?_)
        exact fun j ↦ ⟨0, Subsingleton.elim (α := Fin 1) _ _⟩
    | succ n =>
        obtain ⟨j, α, hα⟩ := SimplexCategory.eq_comp_δ_of_not_surjective s.down hs
        rw [hα, op_comp, FunctorToTypes.map_comp_apply]
        apply (SSet.skeletonOfMono i (n + 1)).map α.op
        exact Or.inr (B.mem_skeleton (B.map (SimplexCategory.δ j).op σ.1)
          (Nat.lt_succ_self n))

/-- Every simplex newly appearing at stage `n + 1` is a degeneracy of a new `n`-simplex. -/
theorem relative_stage_normal_form {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    {k n : ℕ} (x : B _⦋k⦌)
    (hx : x ∈ (SSet.skeletonOfMono i (n + 1)).obj (op ⦋k⦌))
    (hx' : x ∉ (SSet.skeletonOfMono i n).obj (op ⦋k⦌)) :
    ∃ (σ : B.nonDegenerate n), σ.1 ∉ Set.range (i.app (op ⦋n⦌)) ∧
      ∃ (α : ⦋k⦌ ⟶ ⦋n⦌), Epi α ∧ x = B.map α.op σ.1 := by
  obtain ⟨m, α, hα, σ, hσ⟩ := B.exists_nonDegenerate x
  have hnext : σ.1 ∈ (SSet.skeletonOfMono i (n + 1)).obj (op ⦋m⦌) :=
    (mem_of_epi_pullback_iff (SSet.skeletonOfMono i (n + 1)) α σ.1).mp (hσ ▸ hx)
  have hprev : σ.1 ∉ (SSet.skeletonOfMono i n).obj (op ⦋m⦌) := by
    intro h
    exact hx' (hσ ▸ (mem_of_epi_pullback_iff (SSet.skeletonOfMono i n) α σ.1).mpr h)
  have hnotRange : σ.1 ∉ Set.range (i.app (op ⦋m⦌)) := by
    intro h
    exact hprev ((SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i σ n).mpr (Or.inl h))
  have hm : m = n := by
    have hlt := (SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i σ (n + 1)).mp hnext
    have hnlt : ¬ m < n := by
      intro h
      exact hprev ((SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i σ n).mpr (Or.inr h))
    rcases hlt with h | h
    · exact (hnotRange h).elim
    · omega
  subst m
  exact ⟨σ, hnotRange, α, hα, hσ⟩

/-- The complement of the previous stage consists exactly of these new-cell normal forms. -/
theorem relative_stage_complement_iff {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    {k n : ℕ} (x : B _⦋k⦌) :
    (x ∈ (SSet.skeletonOfMono i (n + 1)).obj (op ⦋k⦌) ∧
      x ∉ (SSet.skeletonOfMono i n).obj (op ⦋k⦌)) ↔
    ∃ (σ : B.nonDegenerate n), σ.1 ∉ Set.range (i.app (op ⦋n⦌)) ∧
      ∃ (α : ⦋k⦌ ⟶ ⦋n⦌), Epi α ∧ x = B.map α.op σ.1 := by
  refine ⟨fun hx ↦ relative_stage_normal_form i x hx.1 hx.2, ?_⟩
  rintro ⟨σ, hσ, α, hα, rfl⟩
  constructor
  · apply (mem_of_epi_pullback_iff (SSet.skeletonOfMono i (n + 1)) α σ.1).mpr
    exact (SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i σ (n + 1)).mpr
      (Or.inr (Nat.lt_succ_self n))
  · intro hx
    have hmem := (mem_of_epi_pullback_iff (SSet.skeletonOfMono i n) α σ.1).mp hx
    rcases (SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i σ n).mp hmem with h | h
    · exact hσ h
    · exact (Nat.lt_irrefl n) h

/-- The nondegenerate ancestor and its degeneracy map in this normal form are both unique. -/
theorem relative_stage_normal_form_unique {B : SSet.{u}} {k n : ℕ}
    (x : B _⦋k⦌) (σ τ : B.nonDegenerate n)
    (α β : ⦋k⦌ ⟶ ⦋n⦌) [Epi α] [Epi β]
    (hα : x = B.map α.op σ.1) (hβ : x = B.map β.op τ.1) :
    σ = τ ∧ α = β :=
  ⟨B.unique_nonDegenerate_simplex x α σ hα β τ hβ,
    B.unique_nonDegenerate_map x α σ hα β τ hβ⟩

end DaggerModels.RelativeCellBoundary
