import ActualQKanCotensorComparison

/-! Native closed adjunctions exchange the two simplicial parameters, with full naturality. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed
universe u

namespace DaggerActualSSetCotensorExchange
noncomputable section

/-- Exchange by the two unchanged native closed adjunctions and the native braiding. -/
def exchangeHomEquiv (A B X : SSet.{u}) :
    (A ⟶ (ihom B).obj X) ≃ (B ⟶ (ihom A).obj X) :=
  ((ihom.adjunction B).homEquiv A X).symm.trans
    ((Iso.homCongr (β_ A B).symm (Iso.refl X)).trans
      ((ihom.adjunction A).homEquiv B X))

/-- The exchange is precisely uncurry, braid, and curry. -/
theorem exchangeHomEquiv_apply (A B X : SSet.{u}) (f : A ⟶ (ihom B).obj X) :
    exchangeHomEquiv A B X f = curry ((β_ A B).hom ≫ uncurry f) := by
  change curry ((β_ A B).hom ≫ uncurry f ≫ 𝟙 X) = _
  rw [Category.comp_id]

/-- Precomposition in the first parameter is the original internal-Hom restriction. -/
theorem exchangeHomEquiv_source {A A' B X : SSet.{u}} (i : A' ⟶ A)
    (f : A ⟶ (ihom B).obj X) :
    exchangeHomEquiv A' B X (i ≫ f) =
      exchangeHomEquiv A B X f ≫ (MonoidalClosed.pre i).app X := by
  rw [exchangeHomEquiv_apply, exchangeHomEquiv_apply, uncurry_natural_left, curry_pre_app]
  congr 1

/-- Restriction in the second parameter is precomposition after the native exchange. -/
theorem exchangeHomEquiv_parameter {A B B' X : SSet.{u}} (i : B' ⟶ B)
    (f : A ⟶ (ihom B).obj X) :
    exchangeHomEquiv A B' X (f ≫ (MonoidalClosed.pre i).app X) =
      i ≫ exchangeHomEquiv A B X f := by
  rw [exchangeHomEquiv_apply, exchangeHomEquiv_apply, uncurry_pre_app,
    ← curry_natural_left]
  congr 1

/-- Exchange also commutes with every actual target map. -/
theorem exchangeHomEquiv_target {A B X Y : SSet.{u}} (f : A ⟶ (ihom B).obj X)
    (g : X ⟶ Y) :
    exchangeHomEquiv A B Y (f ≫ (ihom B).map g) =
      exchangeHomEquiv A B X f ≫ (ihom A).map g := by
  rw [exchangeHomEquiv_apply, exchangeHomEquiv_apply, uncurry_natural_right,
    ← curry_natural_right, Category.assoc]

end
end DaggerActualSSetCotensorExchange
