import NativeSSetMonoFibrationIso
import NativeFixedDaggerPartMappingVertices

/-! The WHOLE ORIGINAL actual enriched mapping ISO for groupoidal cofibrant sources.
Its hom is EXACTLY original postcomposition with the original part inclusion.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectDaggerCategories DaggerNativeFixedDaggerIsomorphismPart
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerNativeFixedDaggerPartMappingFibrationMono DaggerNativeFixedDaggerPartMappingVertices
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeFixedDaggerPartMappingIso
noncomputable section

theorem mapping_isIso {O : Type u} (A D : FixedDaggerCategory O) [IsCofibrant A]
    (hA : HasActualComponentGroupoid (originalDagger A).toSimplicialCat) :
    IsIso (eHomWhiskerLeft SSet A (inclusion D)) := by
  have := mapping_fibration A D
  have := mapping_mono A D
  exact DaggerNativeSSetMonoFibrationIso.isIso_of_vertices _ (mapping_vertices_surjective A D hA)

def mappingIso {O : Type u} (A D : FixedDaggerCategory O) [IsCofibrant A]
    (hA : HasActualComponentGroupoid (originalDagger A).toSimplicialCat) :
    (A ⟶[SSet.{u}] part D) ≅ (A ⟶[SSet.{u}] D) :=
  have := mapping_isIso A D hA
  asIso (eHomWhiskerLeft SSet A (inclusion D))

theorem hom_eq {O : Type u} (A D : FixedDaggerCategory O) [IsCofibrant A]
    (hA : HasActualComponentGroupoid (originalDagger A).toSimplicialCat) :
    (mappingIso A D hA).hom = eHomWhiskerLeft SSet A (inclusion D) := rfl

theorem target_natural {O : Type u} (A : FixedDaggerCategory O) [IsCofibrant A]
    (hA : HasActualComponentGroupoid (originalDagger A).toSimplicialCat)
    {D E : FixedDaggerCategory O} (F : D ⟶ E) :
    eHomWhiskerLeft SSet A (map F) ≫ (mappingIso A E hA).hom =
      (mappingIso A D hA).hom ≫ eHomWhiskerLeft SSet A F := by
  change eHomWhiskerLeft SSet A (map F) ≫ eHomWhiskerLeft SSet A (inclusion E) =
    eHomWhiskerLeft SSet A (inclusion D) ≫ eHomWhiskerLeft SSet A F
  rw [← eHomWhiskerLeft_comp, ← eHomWhiskerLeft_comp, inclusion_natural]

theorem source_natural {O : Type u} {A B : FixedDaggerCategory O}
    [IsCofibrant A] [IsCofibrant B]
    (hA : HasActualComponentGroupoid (originalDagger A).toSimplicialCat)
    (hB : HasActualComponentGroupoid (originalDagger B).toSimplicialCat)
    (F : A ⟶ B) (D : FixedDaggerCategory O) :
    eHomWhiskerRight SSet F (part D) ≫ (mappingIso A D hA).hom =
      (mappingIso B D hB).hom ≫ eHomWhiskerRight SSet F D :=
  eHom_whisker_exchange SSet F (inclusion D)

end
end DaggerNativeFixedDaggerPartMappingIso
