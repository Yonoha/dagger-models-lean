import OriginalHornReversal

/-!
# Transport actual native horn extensions through simplicial reversal

The original horn map is reversed through the exact horn isomorphism. A filler
of that reversed map gives a filler of the original map by the native
double-opposite isomorphism. Every equation is an equality of the entire
original maps, with the original horn and simplex inclusions unchanged.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalStandardSimplexReversal DaggerOriginalHornReversal

universe u

namespace DaggerOriginalHornFillingReversal

noncomputable section

/-- Reverse the entire actual original horn map through the exact native horn iso. -/
def reverseHornMap {X : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (φ : (Λ[n, i] : SSet.{u}) ⟶ X) : (Λ[n, i.rev] : SSet.{u}) ⟶ X.op :=
  hornReversalInv n i ≫ SSet.opFunctor.map φ

/-- A filler of the exact reversed map supplies a filler of the entire original horn map. -/
theorem horn_extension_of_reversed_extension {X : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (φ : (Λ[n, i] : SSet.{u}) ⟶ X) (τ : (Δ[n] : SSet.{u}) ⟶ X.op)
    (hτ : reverseHornMap n i φ = Λ[n, i.rev].ι ≫ τ) :
    ∃ σ : (Δ[n] : SSet.{u}) ⟶ X, φ = Λ[n, i].ι ≫ σ := by
  let ε := SSet.opFunctorCompOpFunctorIso.{u}
  let σ : (Δ[n] : SSet.{u}) ⟶ X := ε.inv.app Δ[n] ≫
    SSet.opFunctor.map (standardSimplexReversalHom n) ≫
      SSet.opFunctor.map τ ≫ ε.hom.app X
  have hhi : hornReversalHom.{u} n i ≫ hornReversalInv n i = 𝟙 _ :=
    (hornReversalIso n i).hom_inv_id
  have hh := congrArg (fun f ↦ hornReversalHom n i ≫ f) hτ
  change hornReversalHom n i ≫ (hornReversalInv n i ≫ SSet.opFunctor.map φ) =
    hornReversalHom n i ≫ (Λ[n, i.rev].ι ≫ τ) at hh
  rw [← Category.assoc, hhi, Category.id_comp, ← Category.assoc,
    hornReversalHom_comp_ι, Category.assoc] at hh
  have ho := congrArg SSet.opFunctor.map hh
  simp only [Functor.map_comp] at ho
  have hn := ε.inv.naturality (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι
  change Λ[n, i].ι ≫ ε.inv.app Δ[n] = ε.inv.app (Λ[n, i] : SSet.{u}) ≫
    SSet.opFunctor.map (SSet.opFunctor.map Λ[n, i].ι) at hn
  have hf := ε.hom.naturality φ
  change SSet.opFunctor.map (SSet.opFunctor.map φ) ≫ ε.hom.app X =
    ε.hom.app (Λ[n, i] : SSet.{u}) ≫ φ at hf
  have hc : ε.inv.app (Λ[n, i] : SSet.{u}) ≫
      ε.hom.app (Λ[n, i] : SSet.{u}) = 𝟙 _ := (ε.app _).inv_hom_id
  refine ⟨σ, ?_⟩
  calc
    φ = ε.inv.app (Λ[n, i] : SSet.{u}) ≫
        (SSet.opFunctor.map (SSet.opFunctor.map φ) ≫ ε.hom.app X) := by
      rw [hf, ← Category.assoc, hc, Category.id_comp]
    _ = ε.inv.app (Λ[n, i] : SSet.{u}) ≫
        (SSet.opFunctor.map (SSet.opFunctor.map Λ[n, i].ι) ≫
          (SSet.opFunctor.map (standardSimplexReversalHom n) ≫
            (SSet.opFunctor.map τ ≫ ε.hom.app X))) := by
      rw [ho]
      simp only [Category.assoc]
    _ = Λ[n, i].ι ≫ σ := by
      dsimp only [σ]
      simp only [← Category.assoc]
      rw [hn]

/-- Filling every actual reversed-index horn in the native opposite fills the original horn. -/
theorem horn_filling_of_reversed_filling {X : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (h : ∀ ψ : (Λ[n, i.rev] : SSet.{u}) ⟶ X.op,
      ∃ τ : (Δ[n] : SSet.{u}) ⟶ X.op, ψ = Λ[n, i.rev].ι ≫ τ)
    (φ : (Λ[n, i] : SSet.{u}) ⟶ X) :
    ∃ σ : (Δ[n] : SSet.{u}) ⟶ X, φ = Λ[n, i].ι ≫ σ := by
  obtain ⟨τ, hτ⟩ := h (reverseHornMap n i φ)
  exact horn_extension_of_reversed_extension n i φ τ hτ

end

end DaggerOriginalHornFillingReversal
