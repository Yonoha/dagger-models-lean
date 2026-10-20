import NativeFullChainInjectivity
import NativeSimplicialReplacementReindex

/-! Object-injective faithful reindexing preserves every whole replacement cell injectively. -/
set_option autoImplicit false
open CategoryTheory Opposite
open DaggerNativeFullChainInjectivity DaggerNativeSimplicialReplacementReindex
open DaggerNativeSimplicialReplacement
universe u
namespace DaggerNativeSimplicialReplacementReindexMonos
noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- All parameter simplices are retained after the entire index chain is recovered. -/
theorem diagonalReindex_mono (F : C ⥤ D) [F.Faithful] (hF : Function.Injective F.obj)
    (G : D ⥤ SSet.{u}) : Mono (diagonalReindex F G) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro q
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y h
  have hc : x.1 = y.1 :=
    postcomp_injective F hF (Fin (q.unop.len + 1)) (congrArg Sigma.fst h)
  rcases x with ⟨c, s⟩
  rcases y with ⟨d, t⟩
  dsimp only at hc
  cases hc
  have ht : s = t := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  cases ht
  rfl

end
end DaggerNativeSimplicialReplacementReindexMonos
