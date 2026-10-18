import OriginalRelativeLeftTwoHornInverses

/-!
# Original edges lifted from a specified source through the native left one-horn

Use the native terminal zero simplex to prescribe the source vertex of the
actual (1,0)-horn. The relative lift retains that vertex and the exact original
base one-simplex. The target equality is recorded explicitly, without replacing
the map or passing to a homotopy class. All simplicial sets have arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreKanInverseEdges

universe u

namespace DaggerOriginalRelativeLeftOneHornEdges

noncomputable section

/-- The native relative left one-horn lifts the exact base edge from a prescribed source vertex.
-/
theorem lift_edge_from_source {E X : SSet.{u}} (p : E ⟶ X)
    [HasLiftingProperty (Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).ι p]
    (a : E.obj (op ⦋0⦌)) {y : X.obj (op ⦋0⦌)}
    (e : SSet.Edge (p.app (op ⦋0⦌) a) y) :
    ∃ b : E.obj (op ⦋0⦌), p.app (op ⦋0⦌) b = y ∧
      ∃ g : SSet.Edge a b, p.app (op ⦋1⦌) g.edge = e.edge := by
  let a₀ : (Δ[0] : SSet.{u}) ⟶ E := SSet.yonedaEquiv.symm a
  let φ : (Λ[1, 0] : SSet.{u}) ⟶ E :=
    SSet.stdSimplex.isTerminalObj₀.from (Λ[1, 0] : SSet.{u}) ≫ a₀
  let β : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm e.edge
  have hterm : SSet.horn.ι 0 1 (by decide) ≫
      SSet.stdSimplex.isTerminalObj₀.from (Λ[1, 0] : SSet.{u}) = 𝟙 Δ[0] :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hφ : SSet.horn.ι 0 1 (by decide) ≫ φ = a₀ := by
    dsimp only [φ]
    rw [← Category.assoc, hterm, Category.id_comp]
  have hβ : SSet.stdSimplex.δ 1 ≫ β = a₀ ≫ p := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, SSet.yonedaEquiv_comp]
    simp only [β, a₀, Equiv.apply_symm_apply, e.src_eq]
  have w : φ ≫ p = (Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).ι ≫ β := by
    apply SSet.horn.hom_ext
    intro j hj
    have hj1 : j = 1 := by
      apply Fin.ext
      change j.val = 1
      have hlt : j.val < 2 := j.isLt
      have hn : j.val ≠ 0 := by intro hz; exact hj (Fin.ext hz)
      omega
    subst j
    have h : SSet.horn.ι 0 1 (by decide) ≫ (φ ≫ p) =
        SSet.horn.ι 0 1 (by decide) ≫ (Λ[1, 0].ι ≫ β) := by
      rw [← Category.assoc, hφ, ← hβ, SSet.horn.ι_ι_assoc]
    simpa only [SSet.yonedaEquiv_comp, SSet.horn.yonedaEquiv_ι] using
      congrArg SSet.yonedaEquiv h
  let sq : CommSq φ (Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).ι p β := ⟨w⟩
  haveI : sq.HasLift := HasLiftingProperty.sq_hasLift sq
  let μ := sq.lift
  have hμ : SSet.stdSimplex.δ 1 ≫ μ = a₀ := by
    rw [← SSet.horn.ι_ι 0 1 (by decide), Category.assoc, sq.fac_left]
    exact hφ
  have hs : E.δ 1 (SSet.yonedaEquiv μ) = a := by
    simpa only [yonedaEquiv_coface, a₀, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv hμ
  let b := E.δ 0 (SSet.yonedaEquiv μ)
  let g : SSet.Edge a b := ⟨SSet.yonedaEquiv μ, hs, rfl⟩
  have hgp : p.app (op ⦋1⦌) g.edge = e.edge := by
    have h := congrArg SSet.yonedaEquiv sq.fac_right
    simpa only [SSet.yonedaEquiv_comp, β, Equiv.apply_symm_apply] using h
  have hb : p.app (op ⦋0⦌) b = y := by
    have h := (g.map p).tgt_eq
    change X.δ 0 (p.app (op ⦋1⦌) g.edge) = p.app (op ⦋0⦌) b at h
    rw [hgp, e.tgt_eq] at h
    exact h.symm
  exact ⟨b, hb, g, hgp⟩

end

end DaggerOriginalRelativeLeftOneHornEdges
