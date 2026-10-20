import DaggerModels.RelativeCellMaps
import DaggerModels.RelativeCellOrbits
import DaggerModels.FreeDaggerCell

/-!
# The chosen dagger cells cover each relative skeletal stage

The ordinary relative normal form and the actual dagger-orbit representatives
show that every new simplex comes from one of the chosen free cells.
On the second copy the simplex operator must be reversed. Vertices are
covered by their individual representatives as prescribed by `cellReps`.
-/

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.RelativeCellCoverage

open DaggerSSet RelativeCellMaps FreeDaggerCell

variable {X Y : DaggerSSet.{u}} (i : X ⟶ Y) [Mono i]

local instance : Mono i.hom := (mono_iff_mono_hom i).1 inferInstance

/-- The preceding stage and the chosen free cells jointly cover the genuine next stage. -/
theorem stage_covered_by_cells {n k : ℕ} (c : CellReps i n)
    (x : ((relativeSkeleton i).obj (n + 1)).toSSet _⦋k⦌) :
    x ∈ Set.range (((relativeSkeleton i).map (homOfLE (Nat.le_succ n))).hom.app
      (op ⦋k⦌)) ∨
    ∃ (r : c.R) (y : (FreeDaggerPushout.underlying (Δ[n] : SSet.{u})) _⦋k⦌),
      (cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction (c.rep r).1).hom.app
        (op ⦋k⦌) y = x := by
  classical
  by_cases hx : x.1 ∈ (SSet.skeletonOfMono i.hom n).obj (op ⦋k⦌)
  · exact Or.inl ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩
  · obtain ⟨σ, hσ, α, _hα, he⟩ :=
      RelativeCellBoundary.relative_stage_normal_form i.hom x.1 x.2 hx
    obtain ⟨r, hr | hr⟩ := c.cover ⟨σ, hσ⟩
    · refine Or.inr ⟨r, left α, Subtype.ext ?_⟩
      have hσr : σ.1 = (c.rep r).1.1 := congrArg (fun z ↦ z.1.1) hr
      exact (cellMap_inl_app_val i (c.rep r).1 α).trans
        ((congrArg (Y.toSSet.map α.op) hσr.symm).trans he.symm)
    · refine Or.inr ⟨r, right (SimplexCategory.rev.map α), Subtype.ext ?_⟩
      have hσr : σ.1 = Y.daggerSimplex (c.rep r).1.1 :=
        congrArg (fun z ↦ z.1.1) hr
      have h := cellMap_inr_app_val i (c.rep r).1 (SimplexCategory.rev.map α)
      rw [SimplexCategory.rev_map_rev_map] at h
      exact h.trans ((congrArg (Y.toSSet.map α.op) hσr.symm).trans he.symm)

end DaggerModels.RelativeCellCoverage
