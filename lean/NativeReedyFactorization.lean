import NativeReedySmallObjectRows

/-! Actual functorial factorizations have rowwise anodyne units and genuine Reedy projections. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeReedySmallObject
open DaggerNativeReedyGeneratingLifting DaggerNativeReedySmallObjectRows
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeReedyFactorization
noncomputable section

def obj {X Y : BiSSet.{u}} (f : X ⟶ Y) : BiSSet.{u} := factorizationData.Z.obj (Arrow.mk f)
def inclusion {X Y : BiSSet.{u}} (f : X ⟶ Y) : X ⟶ obj f :=
  factorizationData.i.app (Arrow.mk f)
def projection {X Y : BiSSet.{u}} (f : X ⟶ Y) : obj f ⟶ Y :=
  factorizationData.p.app (Arrow.mk f)

theorem fac {X Y : BiSSet.{u}} (f : X ⟶ Y) : inclusion f ≫ projection f = f :=
  NatTrans.congr_app factorizationData.fac (Arrow.mk f)

theorem inclusion_row_trivial {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (h : SimplexCategoryᵒᵖ) : trivialCofibrations SSet.{u} ((inclusion f).app h) :=
  left_rows_trivial (inclusion f) (factorizationData.hi (Arrow.mk f)) h

theorem projection_reedy {X Y : BiSSet.{u}} (f : X ⟶ Y) :
    ReedyFibration (projection f) :=
  rlp_implies_reedy (projection f) (factorizationData.hp (Arrow.mk f))

def map {X Y X' Y' : BiSSet.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'} (s : Arrow.mk f ⟶ Arrow.mk g) :
    obj f ⟶ obj g := factorizationData.Z.map s

theorem map_id {X Y : BiSSet.{u}} (f : X ⟶ Y) : map (𝟙 (Arrow.mk f)) = 𝟙 (obj f) :=
  factorizationData.Z.map_id (Arrow.mk f)

theorem map_comp {X Y X' Y' X'' Y'' : BiSSet.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'} {r : X'' ⟶ Y''}
    (s : Arrow.mk f ⟶ Arrow.mk g) (t : Arrow.mk g ⟶ Arrow.mk r) :
    map (s ≫ t) = map s ≫ map t := factorizationData.Z.map_comp s t

theorem inclusion_natural {X Y X' Y' : BiSSet.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (s : Arrow.mk f ⟶ Arrow.mk g) : inclusion f ≫ map s = s.left ≫ inclusion g :=
  (factorizationData.i.naturality s).symm

theorem projection_natural {X Y X' Y' : BiSSet.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (s : Arrow.mk f ⟶ Arrow.mk g) : map s ≫ projection g = projection f ≫ s.right :=
  factorizationData.p.naturality s

end
end DaggerNativeReedyFactorization
