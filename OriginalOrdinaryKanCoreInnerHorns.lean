import OriginalInnerHornAdjacentEdges

/-!
# Inner-horn fillers stay in the original ordinary core candidate

Every adjacent edge belongs to the actual inner horn. The original unit sends
these edges to isomorphisms, so their composites give every arrow of the unit
image of the filler. The literal preimage core criterion then retains the filler.
This proves the inner-horn part in arbitrary universe; outer horns remain separate.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreNerveMembership
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality
open DaggerOriginalInnerHornFillers
open DaggerOriginalComposableArrowsAdjacentIsomorphisms
open DaggerOriginalInnerHornAdjacentEdges

universe u

namespace DaggerOriginalOrdinaryKanCoreInnerHorns

noncomputable section

/-- Evaluation on an actual simplex operator is the corresponding face of the exact simplex. -/
theorem simplex_app_operator {X : SSet.{u}} {m n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    σ.app (op ⦋m⦌) (SSet.stdSimplex.objEquiv.symm α) =
      X.map α.op (SSet.yonedaEquiv σ) := by
  have h := congrFun (σ.naturality α.op) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))
  change σ.app (op ⦋m⦌) (SSet.stdSimplex.objEquiv.symm (α ≫ 𝟙 ⦋n⦌)) =
    X.map α.op (SSet.yonedaEquiv σ) at h
  simpa only [Category.comp_id] using h

/-- Every actual inner-horn filler with core-valued faces remains in the same original core. -/
theorem core_innerHorn_filler_mem (X : SSet.{u}) {n : ℕ} {i : Fin (n + 1)}
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : (Λ[n, i] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}))
    (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (hσ : σ₀ ≫ (ordinaryCoreCandidate X).ι = Λ[n, i].ι ≫ σ) :
    SSet.yonedaEquiv σ ∈ (ordinaryCoreCandidate X).obj (op ⦋n⦌) := by
  apply (mem_ordinaryCoreCandidate_iff_unit_arrows_iso X (op ⦋n⦌) _).mpr
  apply all_arrows_iso_of_adjacent
  intro k
  let α := pairOperator k.castSucc k.succ (Fin.castSucc_le_succ k)
  let a : (Λ[n, i] : SSet.{u}).obj (op ⦋1⦌) :=
    ⟨SSet.stdSimplex.objEquiv.symm α, adjacentOperator_mem_innerHorn i h0 hn k⟩
  have ha := (σ₀.app (op ⦋1⦌) a).property
  have he := (mem_ordinaryCoreCandidate_one_iff X (σ₀.app (op ⦋1⦌) a).val).mp ha
  have hf := congrArg
    (fun f : (Λ[n, i] : SSet.{u}) ⟶ X ↦ f.app (op ⦋1⦌) a) hσ
  change (σ₀.app (op ⦋1⦌) a).val =
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

/-- The original core candidate satisfies every inner-horn filling condition of the input. -/
theorem innerHornFillers_ordinaryCoreCandidate (X : SSet.{u}) (hX : innerHornFillers X) :
    innerHornFillers (ordinaryCoreCandidate X : SSet.{u}) := by
  intro n i h0 hn σ₀
  obtain ⟨σ, hσ⟩ := hX h0 hn (σ₀ ≫ (ordinaryCoreCandidate X).ι)
  have hs := core_innerHorn_filler_mem X h0 hn σ₀ σ hσ
  let cs : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋n⦌) := ⟨SSet.yonedaEquiv σ, hs⟩
  let τ : (Δ[n] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}) :=
    SSet.yonedaEquiv.symm cs
  have hτ : τ ≫ (ordinaryCoreCandidate X).ι = σ := by
    apply (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).injective
    rw [SSet.yonedaEquiv_comp]
    change (ordinaryCoreCandidate X).ι.app (op ⦋n⦌)
      (SSet.yonedaEquiv (SSet.yonedaEquiv.symm cs)) = SSet.yonedaEquiv σ
    rw [Equiv.apply_symm_apply]
    rfl
  refine ⟨τ, ?_⟩
  apply (cancel_mono (ordinaryCoreCandidate X).ι).mp
  rw [Category.assoc, hτ]
  exact hσ

/-- In universe zero the same original core of a native quasi-category is a quasi-category. -/
theorem native_quasicategory_ordinaryCoreCandidate (X : SSet.{0}) [X.Quasicategory] :
    (ordinaryCoreCandidate X : SSet.{0}).Quasicategory := by
  apply (innerHornFillers_iff_native_quasicategory _).mp
  apply innerHornFillers_ordinaryCoreCandidate
  exact (innerHornFillers_iff_native_quasicategory X).mpr inferInstance

end

end DaggerOriginalOrdinaryKanCoreInnerHorns
