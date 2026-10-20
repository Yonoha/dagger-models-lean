import OriginalOrdinaryCoreKan
import OriginalRelativeLeftTwoHornInverses

/-!
# Nonfinal horn lifting over a terminal simplicial set

A map to a terminal simplicial set lifting every nonfinal horn has Kan source.
The existing relative left two-horn theorem makes each source edge invertible.
Thus the original ordinary core equals the whole source, and the already proved
all-dimensional Kan theorem for that same core supplies the remaining horns.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalVertexCosliceLeftLifting
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality
open DaggerOriginalOrdinaryKanCoreContainsKanSubcomplexes
open DaggerOriginalRelativeLeftTwoHornInverses DaggerOriginalOrdinaryCoreKan
open DaggerOriginalNativeKanFromHornFillers

universe u

namespace DaggerOriginalNonfinalHornTerminalKan

noncomputable section

/-- A terminal simplicial set fills the original horns in every universe. -/
theorem terminal_kan (T : SSet.{u}) (hT : Limits.IsTerminal T) : T.KanComplex := by
  apply kanComplex_of_hornFillers
  intro n i φ
  exact ⟨hT.from _, hT.hom_ext _ _⟩

/-- Nonfinal lifting over a terminal base makes every actual source edge invertible. -/
theorem source_edgeIsInvertible {E T : SSet.{u}} (p : E ⟶ T)
    (hT : Limits.IsTerminal T)
    (hleft : ∀ (n : ℕ) (i : Fin (n + 2)), i < Fin.last (n + 1) →
      HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι p)
    (e : E.obj (op ⦋1⦌)) : edgeIsInvertible E e := by
  haveI : T.KanComplex := terminal_kan T hT
  haveI := hleft 1 0 (by decide)
  exact edgeIsInvertible_of_invertible_image p (innerHornFillers_of_kan T)
    (SSet.Edge.mk' e) (kan_edgeIsInvertible T _)

/-- The original unit-preimage core contains every simplex of the same source. -/
theorem source_ordinaryCore_eq_top {E T : SSet.{u}} (p : E ⟶ T)
    (hT : Limits.IsTerminal T)
    (hleft : ∀ (n : ℕ) (i : Fin (n + 2)), i < Fin.last (n + 1) →
      HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι p) :
    ordinaryCoreCandidate E = ⊤ := by
  apply le_antisymm le_top
  apply (le_ordinaryCoreCandidate_iff_edges_iso E ⊤).mpr
  intro e _
  exact source_edgeIsInvertible p hT hleft e

/-- A source lifting all nonfinal horns over a terminal simplicial set is Kan. -/
theorem kan_of_nonfinal_lifting_over_terminal {E T : SSet.{u}} (p : E ⟶ T)
    (hT : Limits.IsTerminal T)
    (hleft : ∀ (n : ℕ) (i : Fin (n + 2)), i < Fin.last (n + 1) →
      HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι p) :
    E.KanComplex := by
  haveI : T.KanComplex := terminal_kan T hT
  have hE : innerHornFillers E :=
    innerHornFillers_of_nonfinal_lifting p (innerHornFillers_of_kan T) hleft
  have hcore := source_ordinaryCore_eq_top p hT hleft
  let e : (ordinaryCoreCandidate E : SSet.{u}) ≅ E :=
    eqToIso (congrArg (fun A : E.Subcomplex ↦ (A : SSet.{u})) hcore) ≪≫
      SSet.Subcomplex.topIso E
  apply kanComplex_of_hornFillers
  intro n i φ
  obtain ⟨σ, hσ⟩ := hornFillers_ordinaryCoreCandidate E hE n i (φ ≫ e.inv)
  refine ⟨σ ≫ e.hom, ?_⟩
  calc
    φ = (φ ≫ e.inv) ≫ e.hom := by simp
    _ = Λ[n + 1, i].ι ≫ (σ ≫ e.hom) := by rw [hσ, Category.assoc]

end

end DaggerOriginalNonfinalHornTerminalKan
