import OriginalVertexCosliceLeftLifting
import OriginalRelativeLeftTwoHornInverses
import NativeQuasicategoryGroupoidKan
import NativePullbackFibreIso

/-! Original nonfinal horn lifting gives Kan fibres, using the existing relative inverse proof. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreContainsKanSubcomplexes
open DaggerNativeKanSourceOriginalCoreFactor
universe u
namespace DaggerNativeNonfinalLiftingKanFibres
noncomputable section

def NonfinalLifting {E B : SSet.{u}} (p : E ⟶ B) : Prop :=
  ∀ (n : ℕ) (i : Fin (n + 2)), i < Fin.last (n + 1) →
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι p

theorem core_eq_top {E B : SSet.{u}} (p : E ⟶ B) [B.KanComplex]
    (h : NonfinalLifting p) : ordinaryCoreCandidate E = ⊤ := by
  apply le_antisymm le_top
  intro q s _
  apply (mem_ordinaryCoreCandidate_iff_edges_iso E q s).2
  intro α
  have : HasLiftingProperty (Λ[2, 0] : (Δ[2] : SSet.{u}).Subcomplex).ι p :=
    h 1 0 (by decide)
  exact DaggerOriginalRelativeLeftTwoHornInverses.edgeIsInvertible_of_invertible_image p
    (DaggerNativeHoIsoTriangles.native_inner_fillers B) (SSet.Edge.mk' (E.map α.op s))
    (kan_edgeIsInvertible B _)

theorem source_kan {E B : SSet.{u}} (p : E ⟶ B) [B.KanComplex]
    (h : NonfinalLifting p) : E.KanComplex := by
  have hE : DaggerOriginalInnerHornFillers.innerHornFillers E :=
    DaggerOriginalVertexCosliceLeftLifting.innerHornFillers_of_nonfinal_lifting p
    (DaggerNativeHoIsoTriangles.native_inner_fillers B) h
  have : E.Quasicategory := ⟨fun n i φ h0 hn ↦ hE h0 hn φ⟩
  have := native_quasi_core_kan E
  exact DaggerNativeKanSimplicialOpposite.kan_of_iso
    (SSet.Subcomplex.isoOfEq (core_eq_top p h) ≪≫ SSet.Subcomplex.topIso E)

theorem pullback_nonfinal {P E A B : SSet.{u}}
    {i : P ⟶ E} {q : P ⟶ A} {p : E ⟶ B} {f : A ⟶ B}
    (hs : IsPullback i q p f) (h : NonfinalLifting p) : NonfinalLifting q := by
  intro n k hk
  have := h n k hk
  exact hs.hasLiftingProperty _

theorem fiber_kan {E B : SSet.{u}} (p : E ⟶ B) (b : B.obj (op ⦋0⦌))
    (h : NonfinalLifting p) : (SSet.Subcomplex.fiber p b : SSet.{u}).KanComplex := by
  have : (Δ[0] : SSet.{u}).KanComplex := by
    apply DaggerOriginalNativeKanFromHornFillers.kanComplex_of_hornFillers
    intro n i φ
    exact ⟨SSet.stdSimplex.objZeroIsTerminal.from _,
      SSet.stdSimplex.objZeroIsTerminal.hom_ext _ _⟩
  exact source_kan _ (pullback_nonfinal (SSet.Subcomplex.fiber_isPullback p b) h)

end
end DaggerNativeNonfinalLiftingKanFibres
