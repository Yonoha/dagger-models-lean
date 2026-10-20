import ActualRightConePointSupport
import OriginalNecklaceSimple
import ChosenNecklaceSingleBead
import ChosenNecklacePointMaps
import ChosenNecklaceUnitCodeMaps

/-! Endpoint point inclusions into the actual collapsed-face cone lift all necklaces. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRetractionHomFactorization
open DaggerOriginalCounitRightConeQZeroFaceIntersection
open DaggerChosenRigidificationNecklace hiding C RV
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget
open DaggerActualRightConePointSupport
universe u

namespace DaggerActualRightConePointNecklaceSimple
noncomputable section

theorem projection_vertex_injective (n : ℕ) :
    Function.Injective ((projection.{u} n).app (op ⦋0⦌)) := by
  intro x y h
  rcases DaggerActualRightConeObjectClassification.vertex_cases n x with rfl | rfl <;>
    rcases DaggerActualRightConeObjectClassification.vertex_cases n y with rfl | rfl
  · rfl
  · rw [projection_alpha, projection_omega] at h
    have h01 := congrArg (fun z : (Δ[1] : SSet.{u}).obj (op ⦋0⦌) ↦ z 0) h
    exact False.elim ((by decide : (0 : Fin 2) ≠ 1) h01)
  · rw [projection_omega, projection_alpha] at h
    have h10 := congrArg (fun z : (Δ[1] : SSet.{u}).obj (op ⦋0⦌) ↦ z 0) h
    exact False.elim ((by decide : (1 : Fin 2) ≠ 0) h10)
  · rfl

/-- A directed necklace returning to the same formal endpoint has constant vertex image. -/
theorem vertex_constant (n : ℕ) (T : NecklaceCode) (f : T.toSSet ⟶ cone.{u} n)
    (e : (cone.{u} n).obj (op ⦋0⦌))
    (hfirst : f.app _ T.first = e) (hlast : f.app _ T.last = e)
    (z : T.toSSet.obj (op ⦋0⦌)) : f.app _ z = e := by
  let g : T.toSSet ⟶ (single 1).toSSet := f ≫ projection n ≫ (singleIso 1).inv
  have ho (i : Fin (T.len + 1)) :
      orderMap g i = SSet.stdSimplex.obj₀Equiv
        ((projection n).app _ (f.app _ (T.verticesEquiv.symm (ULift.up i)))) := by
    change ((single 1).verticesEquiv (g.app _ (T.verticesEquiv.symm (ULift.up i)))).down = _
    rw [← singleIso_vertex]
    have h := congrFun (NatTrans.congr_app (singleIso.{u} 1).inv_hom_id (op ⦋0⦌))
      ((projection n).app _ (f.app _ (T.verticesEquiv.symm (ULift.up i))))
    exact congrArg SSet.stdSimplex.obj₀Equiv h
  have h0 : orderMap g 0 = SSet.stdSimplex.obj₀Equiv ((projection n).app _ e) := by
    rw [ho]
    change SSet.stdSimplex.obj₀Equiv ((projection n).app _ (f.app _ T.first)) = _
    rw [hfirst]
  have h1 : orderMap g (Fin.last T.len) =
      SSet.stdSimplex.obj₀Equiv ((projection n).app _ e) := by
    rw [ho]
    change SSet.stdSimplex.obj₀Equiv ((projection n).app _ (f.app _ T.last)) = _
    rw [hlast]
  let i := (T.verticesEquiv z).down
  have hl := (orderMap g).monotone (Fin.zero_le i)
  have hr := (orderMap g).monotone (Fin.le_last i)
  rw [h0] at hl
  rw [h1] at hr
  have he := le_antisymm hr hl
  rw [ho] at he
  have hz : T.verticesEquiv.symm (ULift.up i) = z := T.verticesEquiv.symm_apply_apply z
  rw [hz] at he
  exact projection_vertex_injective n (SSet.stdSimplex.obj₀Equiv.injective he)

private theorem point_vertex {X : SSet.{u}} (j : (Δ[0] : SSet.{u}) ⟶ X)
    (z : (Δ[0] : SSet.{u}).obj (op ⦋0⦌)) : j.app _ z = SSet.yonedaEquiv j := by
  simpa only [Equiv.symm_apply_apply] using
    (pointAt_vertex_apply (SSet.yonedaEquiv j) z)

private theorem supported_factor {X : SSet.{u}} (n : ℕ) (f : X ⟶ cone.{u} n)
    (j : (Δ[0] : SSet.{u}) ⟶ cone.{u} n)
    (hs : ∀ m (x : X.obj (op ⦋m⦌)), f.app _ x ∈ Set.range (j.app (op ⦋m⦌))) :
    SSet.stdSimplex.isTerminalObj₀.from X ≫ j = f := by
  ext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ m
  obtain ⟨z, hz⟩ := hs m x
  change j.app _ ((SSet.stdSimplex.isTerminalObj₀.from X).app _ x) = f.app _ x
  rw [zeroSimplex_unique ((SSet.stdSimplex.isTerminalObj₀.from X).app _ x),
    ← zeroSimplex_unique z]
  exact hz

/-- The actual base point, with full endpoint equations, satisfies the original lifting property. -/
theorem alpha_necklaceSimple (n : ℕ) : NecklaceSimple (alphaMap.{u} n) := by
  intro T a b f hfirst hlast
  have h0 : f.app _ T.first = alpha n := by
    have h := congrArg SSet.yonedaEquiv hfirst
    have he : SSet.yonedaEquiv (alphaMap.{u} n) = alpha n :=
      (point_vertex (alphaMap n) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))).symm
    simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, point_vertex, he] using h
  have h1 : f.app _ T.last = alpha n := by
    have h := congrArg SSet.yonedaEquiv hlast
    have he : SSet.yonedaEquiv (alphaMap.{u} n) = alpha n :=
      (point_vertex (alphaMap n) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))).symm
    simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, point_vertex, he] using h
  refine ⟨SSet.stdSimplex.isTerminalObj₀.from _, ?_,
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _, SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  apply supported_factor n
  intro m x
  apply alpha_supported n m
  intro i
  have h := (congrFun (f.naturality (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op) x).symm
  change (cone n).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op (f.app _ x) =
    f.app _ (T.toSSet.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op x) at h
  exact h.trans (vertex_constant n T f (alpha n) h0 h1 _)

/-- The actual tip point satisfies the same full lifting property. -/
theorem omega_necklaceSimple (n : ℕ) : NecklaceSimple (omegaMap.{u} n) := by
  intro T a b f hfirst hlast
  have h0 : f.app _ T.first = omega n := by
    have h := congrArg SSet.yonedaEquiv hfirst
    have he : SSet.yonedaEquiv (omegaMap.{u} n) = omega n :=
      (point_vertex (omegaMap n) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))).symm
    simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, point_vertex, he] using h
  have h1 : f.app _ T.last = omega n := by
    have h := congrArg SSet.yonedaEquiv hlast
    have he : SSet.yonedaEquiv (omegaMap.{u} n) = omega n :=
      (point_vertex (omegaMap n) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))).symm
    simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, point_vertex, he] using h
  refine ⟨SSet.stdSimplex.isTerminalObj₀.from _, ?_,
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _, SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  apply supported_factor n
  intro m x
  apply omega_supported n m
  intro i
  have h := (congrFun (f.naturality (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op) x).symm
  change (cone n).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op (f.app _ x) =
    f.app _ (T.toSSet.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op x) at h
  exact h.trans (vertex_constant n T f (omega n) h0 h1 _)

end
end DaggerActualRightConePointNecklaceSimple
