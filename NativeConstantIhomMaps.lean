import NativeHoIsoWholeWalkingHomotopy

/-! Constant full internal-Hom maps retain the exact ordinary map under uncurrying. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial
open DaggerNativeIhomHoObjects
universe u
namespace DaggerNativeConstantIhomMaps
noncomputable section

def unitMap (K : SSet.{u}) : K ⟶ (𝟙_ SSet.{u}) where
  app _ _ := PUnit.unit
  naturality _ _ _ := rfl

def constantHom {A Z : SSet.{u}} (K : SSet.{u}) (f : A ⟶ Z) :
    K ⟶ (ihom A).obj Z := unitMap K ≫ MonoidalClosed.curry' f

theorem constantHom_point {A Z : SSet.{u}} (f : A ⟶ Z) :
    constantHom (Δ[0] : SSet.{u}) f = SSet.yonedaEquiv.symm
      (SSet.hoFunctor.obj.equiv ((ihom A).obj Z) (homObject f)) := by
  apply SSet.yonedaEquiv.injective
  rfl

theorem constantHom_comp {A Z K L : SSet.{u}} (g : K ⟶ L) (f : A ⟶ Z) :
    g ≫ constantHom L f = constantHom K f := by
  unfold constantHom
  rw [← Category.assoc]
  congr 1

theorem constantHom_pre {A B Z : SSet.{u}} (j : A ⟶ B) (f : B ⟶ Z) (K : SSet.{u}) :
    constantHom K f ≫ (MonoidalClosed.pre j).app Z = constantHom K (j ≫ f) := by
  unfold constantHom
  rw [Category.assoc, curry'_pre]

theorem uncurry_constant {A Z : SSet.{u}} (K : SSet.{u}) (f : A ⟶ Z) :
    MonoidalClosed.uncurry (constantHom K f) = fst A K ≫ f := by
  rw [constantHom, MonoidalClosed.uncurry_natural_left, MonoidalClosed.curry',
    MonoidalClosed.uncurry_curry]
  have hu : A ◁ unitMap K ≫ (ρ_ A).hom = fst A K := by
    apply NatTrans.ext
    rfl
  rw [← Category.assoc, hu]

end
end DaggerNativeConstantIhomMaps
