import DaggerModels.RelativeCellMaps
import DaggerModels.FreeDaggerCell

/-!
# Relative dagger cells meet the previous stage exactly on their boundary

This supplies the intersection argument in Part I, `dj.lem.free-cof`, for the actual
characteristic maps into the relative skeletal filtration. Neither the characteristic map
nor its free transpose is assumed monic. The argument applies in dimension zero as well.
-/

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.RelativeCellIntersection

open DaggerSSet RelativeCellMaps

variable {X Y : DaggerSSet.{u}} (i : X ⟶ Y) [Mono i]

local instance : Mono i.hom := (mono_iff_mono_hom i).1 inferInstance

/-- The stage inclusion has exactly the previous subcomplex as its degreewise image. -/
theorem stageInclusion_mem_range_iff {n k : ℕ}
    (x : ((relativeSkeleton i).obj (n + 1)).toSSet _⦋k⦌) :
    x ∈ Set.range (((relativeSkeleton i).map (homOfLE (Nat.le_succ n))).hom.app (op ⦋k⦌)) ↔
      x.1 ∈ (SSet.skeletonOfMono i.hom n).obj (op ⦋k⦌) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hx
    exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩

/-- Dagger preserves and reflects membership in the actual relative stage. -/
theorem dagger_mem_relativeStage_iff {k : ℕ} (n : ℕ) (x : Y.toSSet _⦋k⦌) :
    Y.daggerSimplex x ∈ (SSet.skeletonOfMono i.hom n).obj (op ⦋k⦌) ↔
      x ∈ (SSet.skeletonOfMono i.hom n).obj (op ⦋k⦌) := by
  refine ⟨fun hx ↦ ?_, daggerStable_skeletonOfMono i n k x⟩
  have h := daggerStable_skeletonOfMono i n k (Y.daggerSimplex x) hx
  simpa only [Y.dagger_dagger] using h

/-- A new nondegenerate `n`-simplex does not belong to the previous relative stage. -/
theorem new_simplex_not_mem_stage {n : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (hσ : σ.1 ∉ Set.range (i.hom.app (op ⦋n⦌))) :
    σ.1 ∉ (SSet.skeletonOfMono i.hom n).obj (op ⦋n⦌) := by
  intro h
  rcases (SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i.hom σ n).mp h with h | h
  · exact hσ h
  · exact (Nat.lt_irrefl n) h

/-- The actual free cell meets the previous stage precisely on its free boundary. -/
theorem cellMap_mem_stageInclusion_range_iff {n k : ℕ}
    (σ : Y.toSSet.nonDegenerate n)
    (hσ : σ.1 ∉ Set.range (i.hom.app (op ⦋n⦌)))
    (x : (FreeDaggerPushout.underlying (Δ[n] : SSet.{u})) _⦋k⦌) :
    (cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom.app
      (op ⦋k⦌) x ∈
        Set.range (((relativeSkeleton i).map (homOfLE (Nat.le_succ n))).hom.app (op ⦋k⦌)) ↔
      x ∈ FreeDaggerCell.boundaryRange n k := by
  constructor
  · intro hx
    by_contra hxb
    obtain ⟨side, α, hα, rfl⟩ := FreeDaggerCell.exists_copy_epi x hxb
    have hmem := (stageInclusion_mem_range_iff i _).mp hx
    cases side with
    | false =>
        have hval := cellMap_inl_app_val i σ α
        change ((cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom.app
          (op ⦋k⦌) (FreeDaggerCell.copy false α)).1 = Y.toSSet.map α.op σ.1 at hval
        rw [hval] at hmem
        exact new_simplex_not_mem_stage i σ hσ
          ((RelativeCellBoundary.mem_of_epi_pullback_iff
            (SSet.skeletonOfMono i.hom n) α σ.1).mp hmem)
    | true =>
        have hval := cellMap_inr_app_val i σ α
        change ((cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom.app
          (op ⦋k⦌) (FreeDaggerCell.copy true α)).1 =
            Y.toSSet.map (SimplexCategory.rev.map α).op (Y.daggerSimplex σ.1) at hval
        rw [hval, ← Y.dagger_map α σ.1] at hmem
        have hplain := (dagger_mem_relativeStage_iff i n (Y.toSSet.map α.op σ.1)).mp hmem
        exact new_simplex_not_mem_stage i σ hσ
          ((RelativeCellBoundary.mem_of_epi_pullback_iff
            (SSet.skeletonOfMono i.hom n) α σ.1).mp hplain)
  · rintro ⟨a, rfl⟩
    refine ⟨(boundaryMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ hσ).hom.app
      (op ⦋k⦌) a, ?_⟩
    exact (congrArg
      (fun f : FreeDaggerPushout.functor.obj (SSet.boundary.{u} n).toSSet ⟶
        (relativeSkeleton i).obj (n + 1) ↦ f.hom.app (op ⦋k⦌) a)
      (cellMap_boundary i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ hσ)).symm

end DaggerModels.RelativeCellIntersection
