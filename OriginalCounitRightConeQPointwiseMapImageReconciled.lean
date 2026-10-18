import OriginalCounitRightConeQPushoutSimplexSupportReconciled

/-!
# Pointwise image of an actual map of collapsed-face right cones

The image of `coneMap α` is exactly the union of the collapsed base and
the image of the large-simplex map `joinMap α` inside the target cone.
This uses the literal pushout defining the original right cone.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQPushoutSimplexSupport

universe u

namespace DaggerOriginalCounitRightConeQPointwiseMapImage

noncomputable section

theorem coneMap_pointwise_range_iff {m n : SimplexCategory}
    (α : m ⟶ n) (q : SimplexCategoryᵒᵖ)
    (x : (cone.{u} n.len).obj q) :
    x ∈ Set.range ((coneMap.{u} α).app q) ↔
      x ∈ Set.range ((baseIncl.{u} n.len).app q) ∨
      ∃ y : (Δ[n.len + 1] : SSet.{u}).obj q,
        y ∈ Set.range ((joinMap.{u} α).app q) ∧
          (simplexIncl.{u} n.len).app q y = x := by
  constructor
  · rintro ⟨z, rfl⟩
    rcases cone_simplex_base_or_tip.{u} m.len q z with
      ⟨b, hb⟩ | ⟨s, hs, _⟩
    · left
      refine ⟨b, ?_⟩
      have h := congrFun
        (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ cone.{u} n.len => f.app q)
          (baseIncl_naturality.{u} α)) b
      change (coneMap.{u} α).app q ((baseIncl.{u} m.len).app q b) =
        (baseIncl.{u} n.len).app q b at h
      rw [hb] at h
      exact h.symm
    · right
      refine ⟨(joinMap.{u} α).app q s, ⟨s, rfl⟩, ?_⟩
      have h := congrFun
        (congrArg (fun f : (Δ[m.len + 1] : SSet.{u}) ⟶ cone.{u} n.len =>
            f.app q) (simplexIncl_naturality.{u} α)) s
      change (coneMap.{u} α).app q ((simplexIncl.{u} m.len).app q s) =
        (simplexIncl.{u} n.len).app q ((joinMap.{u} α).app q s) at h
      rw [hs] at h
      exact h.symm
  · rintro (⟨b, rfl⟩ | ⟨y, ⟨s, rfl⟩, rfl⟩)
    · refine ⟨(baseIncl.{u} m.len).app q b, ?_⟩
      have h := congrFun
        (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ cone.{u} n.len => f.app q)
          (baseIncl_naturality.{u} α)) b
      change (coneMap.{u} α).app q ((baseIncl.{u} m.len).app q b) =
        (baseIncl.{u} n.len).app q b at h
      exact h
    · refine ⟨(simplexIncl.{u} m.len).app q s, ?_⟩
      have h := congrFun
        (congrArg (fun f : (Δ[m.len + 1] : SSet.{u}) ⟶ cone.{u} n.len =>
            f.app q) (simplexIncl_naturality.{u} α)) s
      change (coneMap.{u} α).app q ((simplexIncl.{u} m.len).app q s) =
        (simplexIncl.{u} n.len).app q ((joinMap.{u} α).app q s) at h
      exact h

end

end DaggerOriginalCounitRightConeQPointwiseMapImage
