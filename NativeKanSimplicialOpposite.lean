import NativeQuasicategoryOpposite
import OriginalNativeKanFromHornFillers

/-! Native Kan complexes are preserved by actual simplicial reversal. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalHornFillingReversal DaggerOriginalNativeKanFromHornFillers
universe u
namespace DaggerNativeKanSimplicialOpposite
noncomputable section

theorem kan_of_iso {X Y : SSet.{u}} [X.KanComplex] (e : X ≅ Y) : Y.KanComplex := by
  apply kanComplex_of_hornFillers
  intro n i φ
  obtain ⟨σ, hσ⟩ := SSet.KanComplex.hornFilling (φ ≫ e.inv)
  refine ⟨σ ≫ e.hom, ?_⟩
  have h := congrArg (fun f ↦ f ≫ e.hom) hσ
  simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using h

theorem kan_op (X : SSet.{u}) [X.KanComplex] : X.op.KanComplex := by
  apply kanComplex_of_hornFillers
  intro n i φ
  let ε := SSet.opFunctorCompOpFunctorIso.{u}.app X
  letI : X.op.op.KanComplex := kan_of_iso (X := X) (Y := X.op.op) ε.symm
  exact horn_filling_of_reversed_filling (n + 1) i
    (fun ψ ↦ SSet.KanComplex.hornFilling ψ) φ

end
end DaggerNativeKanSimplicialOpposite
