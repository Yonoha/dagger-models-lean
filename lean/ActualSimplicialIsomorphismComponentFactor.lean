import ActualSimplicialIsomorphismComponentMaps
import OriginalPiZeroGroupoidLocalWeakInvariance

/-! An original functor from a pi-zero groupoid lands in all isomorphism components. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerActualConstantSimplicialCategory
open DaggerActualSimplicialIsomorphismComponentPart
open DaggerActualSimplicialIsomorphismComponentMaps
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalPiZeroGroupoidLocalWeakInvariance
universe u
namespace DaggerActualSimplicialIsomorphismComponentFactor
noncomputable section

local instance (C : SimplicialCat.{u, u}) :
    EnrichedCategory SSet.{u} (constant (componentObjects C)).Obj :=
  (constant (componentObjects C)).enriched

theorem image_mem {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hC : HasActualComponentGroupoid C) (x y : C.Obj) (q : SimplexCategoryᵒᵖ)
    (s : (C.enriched.Hom x y).obj q) :
    (F.map x y).app q s ∈ (homSubcomplex D (F.obj x) (F.obj y)).obj q := by
  change IsIso (((projection D).map (F.obj x) (F.obj y)).app q ((F.map x y).app q s))
  rw [projection_map_apply]
  have : IsIso (((projection C).map x y).app q s) := component_isIso C hC _
  infer_instance

def factor {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hC : HasActualComponentGroupoid C) : C ⟶ part D :=
  DaggerNativeEnrichedHomSubcomplexFactor.factor F (homSubcomplex D)
    (id_mem D) (comp_mem D) (image_mem F hC)

theorem factor_comp_inclusion {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hC : HasActualComponentGroupoid C) : factor F hC ≫ inclusion D = F :=
  DaggerNativeEnrichedHomSubcomplexFactor.factor_comp_inclusion _ _ _ _ _

theorem factor_map_val {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hC : HasActualComponentGroupoid C) (x y : C.Obj) (q : SimplexCategoryᵒᵖ)
    (s : (C.enriched.Hom x y).obj q) :
    ((factor F hC).map x y |>.app q s).val = (F.map x y).app q s :=
  rfl

end
end DaggerActualSimplicialIsomorphismComponentFactor
