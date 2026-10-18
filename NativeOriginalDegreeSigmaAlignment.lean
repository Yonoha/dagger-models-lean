import NativeOrdinaryGroupoidSigma
import OriginalStrictDaggerGroupoidSigma

/-! The generic inverse-dagger functor is EXACTLY the original strict Sigma in every degree. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerNativeDaggerDegreeCotensor
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictDaggerGroupoidSigma DaggerNativeOrdinaryGroupoidSigma
universe u
namespace DaggerNativeOriginalDegreeSigmaAlignment
noncomputable section

/-- Retain the entire original degree functor of the OLD original enriched Sigma. -/
theorem degreeSigma_eq (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (n : SimplexCategoryᵒᵖ) :
    letI := strictDegreeGroupoid C.toSimplicialCat hC n
    letI := degreeDaggerCategory C n
    degreeFunctor (strictSigmaFunctor C hC) n =
      sigmaFunctor (degreeObjects C.toSimplicialCat n) := by
  letI := strictDegreeGroupoid C.toSimplicialCat hC n
  letI := degreeDaggerCategory C n
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro x y f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

end
end DaggerNativeOriginalDegreeSigmaAlignment
