import NativeRealEdgewiseParameters

/-! Palindromic parameters as a natural transformation of the native realization weights. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseParameters
open DaggerOriginalTopologicalSimplexReversal
universe u
namespace DaggerNativeRealEdgewiseTopologicalParameters
noncomputable section

def parameter₀ : SimplexCategory.toTop₀ ⟶ epsilon ⋙ SimplexCategory.toTop₀ where
  app n := TopCat.ofHom ⟨parameter n, continuous_parameter n⟩
  naturality n m f := by
    ext t
    exact (parameter_natural f t).symm

def parameterMap : SimplexCategory.toTop.{u} ⟶ epsilon ⋙ SimplexCategory.toTop.{u} :=
  Functor.whiskerRight parameter₀ TopCat.uliftFunctor ≫
    (Functor.associator epsilon SimplexCategory.toTop₀ TopCat.uliftFunctor).hom

theorem parameterMap_apply (n : SimplexCategory) (t : SimplexCategory.toTop.{u}.obj n) :
    ((parameterMap.{u}.app n) t).down = parameter n t.down := rfl

theorem parameterMap_palindromic (n : SimplexCategory) :
    parameterMap.{u}.app n ≫ reversalIso.{u}.hom.app (epsilon.obj n) =
      parameterMap.{u}.app n := by
  ext t
  apply ULift.ext
  exact reverse_parameter n t.down

theorem parameterMap_palindromic_inv (n : SimplexCategory) :
    parameterMap.{u}.app n ≫ reversalIso.{u}.inv.app (epsilon.obj n) =
      parameterMap.{u}.app n := by
  ext t
  apply ULift.ext
  exact reverse_parameter n t.down

end
end DaggerNativeRealEdgewiseTopologicalParameters
