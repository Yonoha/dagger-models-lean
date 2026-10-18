import ActualDaggerIsomorphismComponentPart
import NativeDaggerEnrichedHomFactor

/-! Every original dagger functor restricts to the ALL-isomorphism-component parts. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerActualSimplicialIsomorphismComponentPart
open DaggerActualDaggerIsomorphismComponentPart
universe u
namespace DaggerActualDaggerIsomorphismComponentMaps
noncomputable section

def map {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) : part C ⟶ part D :=
  DaggerNativeDaggerEnrichedHomFactor.factor (inclusion C ≫ F)
    (homSubcomplex D.toSimplicialCat) (id_mem D.toSimplicialCat) (comp_mem D.toSimplicialCat)
    (dagger_mem D) (DaggerActualSimplicialIsomorphismComponentMaps.map_mem F.toEnrichedFunctor)

theorem map_underlying {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    (map F).toEnrichedFunctor =
      (DaggerActualSimplicialIsomorphismComponentMaps.map F.toEnrichedFunctor :
        (part C).toSimplicialCat ⟶ (part D).toSimplicialCat) :=
  rfl

theorem inclusion_natural {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    map F ≫ inclusion D = inclusion C ≫ F :=
  DaggerNativeDaggerEnrichedHomFactor.factor_comp_inclusion _ _ _ _ _ _

theorem map_id (C : DaggerSimplicialCat.{u, u}) : map (𝟙 C) = 𝟙 (part C) := by
  apply DaggerSimplicialCat.Hom.ext
  exact DaggerActualSimplicialIsomorphismComponentMaps.map_id C.toSimplicialCat

theorem map_comp {C D E : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) (G : D ⟶ E) :
    map (F ≫ G) = map F ≫ map G := by
  apply DaggerSimplicialCat.Hom.ext
  exact DaggerActualSimplicialIsomorphismComponentMaps.map_comp
    F.toEnrichedFunctor G.toEnrichedFunctor

end
end DaggerActualDaggerIsomorphismComponentMaps
