import OriginalEC2SimplicialContraction
import TopCatModelCategory.TopCat.Homotopy
import TopCatModelCategory.TopCat.Adj
import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractibility of the actual realization of the codiscrete C₂ nerve

This transports the already proved simplicial contraction through the original
`SSet.toTop` functor. It makes no assertion about freeness of the realized action.
-/

set_option autoImplicit false

open CategoryTheory
open DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2SimplicialContraction

universe u

namespace DaggerOriginalEC2RealizationContractibility

noncomputable section

private abbrev R : TopCat.{u} := SSet.toTop.obj simplicialEC2.{u}

/-- The actual chosen point of the realization. -/
def realizedPoint : R.{u} := SSet.toTopObjMk (ComposableArrows.mk₀ point.{u})

/-- Convert the actual simplicial contraction to the ordinary interval convention. -/
def realizedContraction : ContinuousMap.Homotopy
    (ContinuousMap.const R.{u} realizedPoint.{u})
    (ContinuousMap.id R.{u}) := by
  let h := contraction.{u}.toTop
  refine
    { toFun := fun p ↦ h.h (p.2, TopCat.homeomorphI.{u}.symm p.1)
      continuous_toFun := h.h.hom.continuous.comp
        (continuous_snd.prodMk
          (TopCat.homeomorphI.{u}.symm.continuous.comp continuous_fst))
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro x
    have h₀ := congrArg (fun f : R.{u} ⟶ R.{u} ↦ f x) h.h₀
    change h.h (x, (0 : TopCat.I.{u})) =
      (SSet.toTop.map
        (SSet.const (ComposableArrows.mk₀ point.{u}))) x at h₀
    rw [SSet.toTop_map_const_apply] at h₀
    change h.h (x, (0 : TopCat.I.{u})) = realizedPoint.{u}
    exact h₀
  · intro x
    have h₁ := congrArg (fun f : R.{u} ⟶ R.{u} ↦ f x) h.h₁
    change h.h (x, (1 : TopCat.I.{u})) =
      (SSet.toTop.map (𝟙 simplicialEC2.{u})) x at h₁
    change h.h (x, (1 : TopCat.I.{u})) = x
    simpa using h₁

/-- The underlying actual topological realization of simplicial `EC₂` is contractible. -/
theorem realizedContractibleSpace : ContractibleSpace R.{u} := by
  apply (contractible_iff_id_nullhomotopic R.{u}).2
  refine ⟨realizedPoint.{u}, ?_⟩
  exact ⟨realizedContraction.{u}.symm⟩

end

end DaggerOriginalEC2RealizationContractibility
