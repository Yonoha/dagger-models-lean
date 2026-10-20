import OriginalHornFillingReversal
import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
# Native quasicategories under actual simplicial reversal

Reuse the established exact horn-reversal isomorphisms and the native double-opposite
isomorphism. Only inner horns are used, with their reversed indices proved to remain inner.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalHornFillingReversal
universe u
namespace DaggerNativeQuasicategoryOpposite

/-- Transport a native quasicategory across an actual simplicial-set isomorphism. -/
theorem quasicategory_of_iso {X Y : SSet.{u}} [SSet.Quasicategory X] (e : X ≅ Y) :
    SSet.Quasicategory Y where
  hornFilling' n i φ h0 hn := by
    obtain ⟨σ, hσ⟩ := SSet.Quasicategory.hornFilling h0 hn (φ ≫ e.inv)
    refine ⟨σ ≫ e.hom, ?_⟩
    have h := congrArg (fun f ↦ f ≫ e.hom) hσ
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using h

/-- Native simplicial reversal preserves the exact inner-horn quasicategory property. -/
theorem quasicategory_op (X : SSet.{u}) [SSet.Quasicategory X] :
    SSet.Quasicategory X.op where
  hornFilling' n i φ h0 hn := by
    have hr0 : 0 < i.rev := by
      simp only [Fin.lt_def, Fin.val_rev, Fin.val_zero, Fin.val_last] at h0 hn ⊢
      omega
    have hrn : i.rev < Fin.last (n + 2) := by
      simp only [Fin.lt_def, Fin.val_rev, Fin.val_zero, Fin.val_last] at h0 hn ⊢
      omega
    let ε := SSet.opFunctorCompOpFunctorIso.{u}.app X
    letI : SSet.Quasicategory X.op.op :=
      quasicategory_of_iso (X := X) (Y := X.op.op) ε.symm
    exact horn_filling_of_reversed_filling (n + 2) i
      (fun ψ ↦ SSet.Quasicategory.hornFilling hr0 hrn ψ) φ

end DaggerNativeQuasicategoryOpposite
