import OriginalNecklaceSimple

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- A vertex inclusion into any necklace satisfies the full endpoint lifting condition. -/
theorem pointAt_necklaceSimple (T : NecklaceCode) (v : Vertices.{u} T) :
    NecklaceSimple (pointAt T v) := by
  intro S a b f hfirst hlast
  have h0 : orderMap f 0 = v.down := by
    have he := congrArg SSet.yonedaEquiv hfirst
    simp only [SSet.yonedaEquiv_comp, pointAt_vertex] at he
    change f.app _ S.first = _ at he
    change (T.verticesEquiv (f.app _ S.first)).down = v.down
    rw [he]
    change T.inclusion.app _ ((pointAt T v).app _ (SSet.yonedaEquiv a)) 0 = v.down
    exact pointAt_inclusion_apply T v _ 0
  have h1 : orderMap f (Fin.last S.len) = v.down := by
    have he := congrArg SSet.yonedaEquiv hlast
    simp only [SSet.yonedaEquiv_comp, pointAt_vertex] at he
    change f.app _ S.last = _ at he
    change (T.verticesEquiv (f.app _ S.last)).down = v.down
    rw [he]
    change T.inclusion.app _ ((pointAt T v).app _ (SSet.yonedaEquiv b)) 0 = v.down
    exact pointAt_inclusion_apply T v _ 0
  let l : S.toSSet ⟶ (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from _
  refine ⟨l, ?_, SSet.stdSimplex.isTerminalObj₀.hom_ext _ _,
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  apply hom_ext_vertices
  funext z
  cases z with
  | up z =>
    apply ULift.ext
    change T.inclusion.app _
      ((pointAt T v).app _ (l.app _ (S.verticesEquiv.symm (ULift.up z)))) 0 = orderMap f z
    rw [pointAt_inclusion_apply]
    have hl := (orderMap f).monotone (Fin.zero_le z)
    have hr := (orderMap f).monotone (Fin.le_last z)
    rw [h0] at hl
    rw [h1] at hr
    exact le_antisymm hl hr

/-- These are the joint inclusions occurring in the product-necklace gluing step. -/
theorem productPointAt_necklaceSimple (K : SSet.{u}) (T : NecklaceCode)
    (v : Vertices.{u} T) : NecklaceSimple (prod.map (𝟙 K) (pointAt T v)) :=
  necklaceSimple_prod (pointAt T v) (pointAt_necklaceSimple T v) K

end

end DaggerOriginalProductGadget
