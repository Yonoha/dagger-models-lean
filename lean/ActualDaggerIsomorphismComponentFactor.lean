import ActualDaggerIsomorphismComponentPart
import ActualSimplicialIsomorphismComponentFactor
import NativeDaggerEnrichedHomFactor

/-! The original dagger functor factors through the ALL-isomorphism part with the same values. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerActualSimplicialIsomorphismComponentPart
open DaggerOriginalAmbientDaggerPiZeroGroupoid
universe u
namespace DaggerActualDaggerIsomorphismComponentFactor
noncomputable section

def factor {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (hC : HasActualComponentGroupoid C.toSimplicialCat) :
    C ⟶ DaggerActualDaggerIsomorphismComponentPart.part D :=
  DaggerNativeDaggerEnrichedHomFactor.factor F (homSubcomplex D.toSimplicialCat)
    (id_mem D.toSimplicialCat) (comp_mem D.toSimplicialCat)
    (DaggerActualDaggerIsomorphismComponentPart.dagger_mem D)
    (DaggerActualSimplicialIsomorphismComponentFactor.image_mem F.toEnrichedFunctor hC)

theorem factor_comp_inclusion {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (hC : HasActualComponentGroupoid C.toSimplicialCat) :
    factor F hC ≫ DaggerActualDaggerIsomorphismComponentPart.inclusion D = F :=
  DaggerNativeDaggerEnrichedHomFactor.factor_comp_inclusion _ _ _ _ _ _

theorem factor_map_val {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (hC : HasActualComponentGroupoid C.toSimplicialCat) (x y : C.Obj)
    (q : SimplexCategoryᵒᵖ) (s : (C.enriched.Hom x y).obj q) :
    ((factor F hC).map x y |>.app q s).val = (F.map x y).app q s :=
  rfl

end
end DaggerActualDaggerIsomorphismComponentFactor
