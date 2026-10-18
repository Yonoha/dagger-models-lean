import NativeFixedDaggerPartMappingFibrationMono

/-! Reuse Mathlib's ORIGINAL simplicial-category Hom/zero-simplex equivalence.
The SAME whole original factor gives coverage of actual mapping vertices.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectDaggerCategories DaggerNativeFixedDaggerIsomorphismPart
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerNativeFixedDaggerPartFactor
open DaggerOriginalFixedObjectDaggerDegreeCategories DaggerOriginalFixedObjectDegreeCategories
universe u
namespace DaggerNativeFixedDaggerPartMappingVertices
noncomputable section

theorem homEquiv'_post {O : Type u} {A B D : FixedDaggerCategory O}
    (F : A ⟶ B) (G : B ⟶ D) :
    (eHomWhiskerLeft SSet A G).app (op ⦋0⦌) (SimplicialCategory.homEquiv' A B F) =
      SimplicialCategory.homEquiv' A D (F ≫ G) := by
  apply Functor.HomObj.ext
  funext q α
  apply degreeDaggerHom_ext
  apply degreeHom_ext
  intro i j s
  rfl

theorem mapping_vertices_surjective {O : Type u} (A D : FixedDaggerCategory O)
    (hA : HasActualComponentGroupoid (originalDagger A).toSimplicialCat) :
    Function.Surjective ((eHomWhiskerLeft SSet A (inclusion D)).app (op ⦋0⦌)) := by
  intro v
  let F := (SimplicialCategory.homEquiv' A D).symm v
  refine ⟨SimplicialCategory.homEquiv' A (part D) (factor F hA), ?_⟩
  rw [homEquiv'_post, factor_comp_inclusion]
  exact (SimplicialCategory.homEquiv' A D).apply_symm_apply v

end
end DaggerNativeFixedDaggerPartMappingVertices
