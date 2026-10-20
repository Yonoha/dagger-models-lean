import ActualDaggerOrdinaryCore
import NativeDaggerSubcomplexMaps

/-! Actual dagger maps restrict to the exact original core and preserve its inclusion. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerActualDaggerOrdinaryCore DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerActualOrdinaryCoreMapValue
universe u
namespace DaggerActualDaggerOrdinaryCoreMaps
noncomputable section

def inclusion (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] : coreDagger X ⟶ X :=
  DaggerNativeDaggerSubcomplexRestriction.inclusion X
    (ordinaryCoreCandidate X.toSSet) (dagger_stable X)

def map {X Y : DaggerSSet.{u}} [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory]
    (f : X ⟶ Y) : coreDagger X ⟶ coreDagger Y :=
  DaggerNativeDaggerSubcomplexMaps.map
    (ordinaryCoreCandidate X.toSSet) (ordinaryCoreCandidate Y.toSSet)
    (dagger_stable X) (dagger_stable Y) f (core_map_mem f.hom)

theorem map_val {X Y : DaggerSSet.{u}} [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory]
    (f : X ⟶ Y) (q : SimplexCategoryᵒᵖ) (s : (coreDagger X).toSSet.obj q) :
    ((map f).hom.app q s).val = f.hom.app q s.val :=
  DaggerNativeDaggerSubcomplexMaps.map_val _ _ _ _ _ _ q s

theorem inclusion_natural {X Y : DaggerSSet.{u}} [X.toSSet.Quasicategory]
    [Y.toSSet.Quasicategory] (f : X ⟶ Y) :
    map f ≫ inclusion Y = inclusion X ≫ f :=
  DaggerNativeDaggerSubcomplexMaps.inclusion_natural _ _ _ _ _ _

theorem inclusion_hom (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    (inclusion X).hom = (ordinaryCoreCandidate X.toSSet).ι :=
  DaggerNativeDaggerSubcomplexRestriction.inclusion_hom _ _ _

theorem map_id (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    map (𝟙 X) = 𝟙 (coreDagger X) :=
  DaggerNativeDaggerSubcomplexMaps.map_id _ _ _

theorem map_comp {X Y Z : DaggerSSet.{u}} [X.toSSet.Quasicategory]
    [Y.toSSet.Quasicategory] [Z.toSSet.Quasicategory] (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ map g :=
  DaggerNativeDaggerSubcomplexMaps.map_comp _ _ _ _ _ _ f g _ _ _

theorem map_vertices {X Y : DaggerSSet.{u}} [X.toSSet.Quasicategory]
    [Y.toSSet.Quasicategory] (f : X ⟶ Y) (s : (coreDagger X).toSSet _⦋0⦌) :
    coreVerticesEquiv Y ((map f).hom.app (op ⦋0⦌) s) =
      f.hom.app (op ⦋0⦌) (coreVerticesEquiv X s) :=
  map_val f (op ⦋0⦌) s

end
end DaggerActualDaggerOrdinaryCoreMaps
