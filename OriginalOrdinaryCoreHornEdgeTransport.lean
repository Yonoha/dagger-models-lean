import OriginalHornEdgesMembership

/-!
# Original unit arrows selected by core-valued horn edges

An actual filling equation transports each edge present in the horn to the same
edge of the filler. Naturality of the original unit identifies its arrow in the
original homotopy category. No filling or equivalence premise is replaced.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreNerveMembership
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality
open DaggerOriginalOrdinaryKanCoreInnerHorns
open DaggerOriginalHornEdgesMembership

universe u

namespace DaggerOriginalOrdinaryCoreHornEdgeTransport

noncomputable section

/-- A core-valued horn edge gives an iso arrow of the exact original unit-image filler. -/
theorem unit_map_isIso_of_core_horn_edge (X : SSet.{u}) {n : ℕ} {i : Fin (n + 1)}
    (σ₀ : (Λ[n, i] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}))
    (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (hσ : σ₀ ≫ (ordinaryCoreCandidate X).ι = Λ[n, i].ι ≫ σ)
    {a b : Fin (n + 1)} (f : a ⟶ b)
    (hedge : (SSet.stdSimplex.objEquiv.symm (pairOperator a b (leOfHom f)) :
      (Δ[n] : SSet.{u}).obj (op ⦋1⦌)) ∈ (Λ[n, i]).obj (op ⦋1⦌)) :
    IsIso (((homotopyCategoryUnit X).app (op ⦋n⦌) (SSet.yonedaEquiv σ)).map f) := by
  let α := pairOperator a b (leOfHom f)
  let e : (Λ[n, i] : SSet.{u}).obj (op ⦋1⦌) :=
    ⟨SSet.stdSimplex.objEquiv.symm α, hedge⟩
  have he := (mem_ordinaryCoreCandidate_one_iff X (σ₀.app (op ⦋1⦌) e).val).mp
    (σ₀.app (op ⦋1⦌) e).property
  have hf := congrArg
    (fun g : (Λ[n, i] : SSet.{u}) ⟶ X ↦ g.app (op ⦋1⦌) e) hσ
  change (σ₀.app (op ⦋1⦌) e).val =
    σ.app (op ⦋1⦌) (SSet.stdSimplex.objEquiv.symm α) at hf
  rw [simplex_app_operator] at hf
  dsimp [edgeIsInvertible] at he
  rw [hf] at he
  have hu := congrFun ((homotopyCategoryUnit X).naturality α.op) (SSet.yonedaEquiv σ)
  change (homotopyCategoryUnit X).app (op ⦋1⦌) (X.map α.op (SSet.yonedaEquiv σ)) =
    (nerve (SSet.hoFunctor.obj X)).map α.op
      ((homotopyCategoryUnit X).app (op ⦋n⦌) (SSet.yonedaEquiv σ)) at hu
  have he' := Eq.mp (congrArg
    (fun t : ComposableArrows (SSet.hoFunctor.obj X) 1 ↦ IsIso t.hom) hu) he
  change IsIso (((nerve (SSet.hoFunctor.obj X)).map α.op
    ((homotopyCategoryUnit X).app (op ⦋n⦌) (SSet.yonedaEquiv σ))).hom) at he'
  exact he'

/-- Every actual horn filler in dimension at least three remains in the same original core. -/
theorem core_horn_filler_mem_of_three_le (X : SSet.{u}) {n : ℕ} {i : Fin (n + 1)}
    (hn : 3 ≤ n)
    (σ₀ : (Λ[n, i] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}))
    (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (hσ : σ₀ ≫ (ordinaryCoreCandidate X).ι = Λ[n, i].ι ≫ σ) :
    SSet.yonedaEquiv σ ∈ (ordinaryCoreCandidate X).obj (op ⦋n⦌) := by
  apply (mem_ordinaryCoreCandidate_iff_unit_arrows_iso X (op ⦋n⦌) _).mpr
  intro a b f
  exact unit_map_isIso_of_core_horn_edge X σ₀ σ hσ f
    (pairOperator_mem_horn_of_three_le hn i a b (leOfHom f))

end

end DaggerOriginalOrdinaryCoreHornEdgeTransport
