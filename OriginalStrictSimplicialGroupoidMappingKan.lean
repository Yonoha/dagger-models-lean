import OriginalStrictGroupoidHomAllHornFaces
import OriginalNativeKanFromHornFillers

/-!
# The original strict simplicial groupoid mapping objects are Kan

The actual native horn map has an extension in every positive dimension. Degree-one
horns use the previously verified native degenerate edge; higher horns use the full
original groupoid correction induction. Native horn extensionality identifies the
extension on the entire horn. The original all-horn criterion gives native Kan fibrancy.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictSimplicialGroupoidHomOperations
open DaggerOriginalStrictGroupoidHomHornFaces
open DaggerOriginalStrictGroupoidHomAllHornFaces
open DaggerOriginalJoinedHornPrefix DaggerOriginalNativeKanFromHornFillers

universe u

namespace DaggerOriginalStrictSimplicialGroupoidMappingKan

noncomputable section

/-- Every actual higher-dimensional horn extends on the unchanged original mapping object. -/
theorem strictHom_higher_horn_filler (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (n : ℕ) (x y : C.Obj) (i : Fin (n + 3))
    (h : (Λ[n + 2, i] : SSet.{u}) ⟶ C.enriched.Hom x y) :
    ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ C.enriched.Hom x y, h = Λ[n + 2, i].ι ≫ σ := by
  obtain ⟨w, hw⟩ := exists_all_faces_filled C hC n x y i h
  let σ : (Δ[n + 2] : SSet.{u}) ⟶ C.enriched.Hom x y := SSet.yonedaEquiv.symm w
  refine ⟨σ, ?_⟩
  apply SSet.horn.hom_ext
  intro r hr
  change hornFaceValue i h r hr = hornFaceValue i (Λ[n + 2, i].ι ≫ σ) r hr
  rw [← hornFaceValue_yoneda, ← hornFaceValue_yoneda, ← Category.assoc, SSet.horn.ι_ι]
  have hv : SSet.yonedaEquiv (SSet.stdSimplex.δ r ≫ σ) = (C.enriched.Hom x y).δ r w := by
    simpa only [σ, Equiv.apply_symm_apply] using
      yonedaEquiv_precomp_operator σ (SimplexCategory.δ r)
  rw [hornFaceValue_yoneda, hv]
  exact (hw r hr).symm

/-- The complete positive-dimensional horn condition holds on the original strict mapping Hom.
-/
theorem strictHom_hornFillers (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (x y : C.Obj) : hornFillers (C.enriched.Hom x y) := by
  intro n i h
  cases n with
  | zero => exact one_horn_filler i h
  | succ k => exact strictHom_higher_horn_filler C hC k x y i h

/-- Every original strict simplicial groupoid has native Kan mapping simplicial sets. -/
theorem strictHom_kan (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (x y : C.Obj) :
    (C.enriched.Hom x y).KanComplex :=
  kanComplex_of_hornFillers (strictHom_hornFillers C hC x y)

/-- The actual original completed mapping simplicial set is a native Kan complex. -/
theorem completedHom_kan (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    (completedHom C x y).KanComplex :=
  strictHom_kan (completion C) (completion_isStrictGroupoid C) x y

end

end DaggerOriginalStrictSimplicialGroupoidMappingKan
