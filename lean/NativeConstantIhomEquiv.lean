import NativeDegreeCotensorYoneda

/-! Constant-set to internal-Hom maps are identified by the ORIGINAL adjunction and Yoneda. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial
universe u
namespace DaggerNativeConstantIhomEquiv
noncomputable section

/-- Retain a fixed original element of the constant source in every degree. -/
def pointOf {S : Type u} {K X : SSet.{u}}
    (phi : (Functor.const SimplexCategoryᵒᵖ).obj S ⟶ (ihom K).obj X) (a : S) :
    𝟙_ SSet.{u} ⟶ (ihom K).obj X where
  app q _ := phi.app q a
  naturality _ _ i := by
    funext p
    exact congrFun (phi.naturality i) a

/-- Curry each original parameter map using the SAME native closed adjunction. -/
def fromMaps {S : Type u} {K X : SSet.{u}} (g : S → (K ⟶ X)) :
    (Functor.const SimplexCategoryᵒᵖ).obj S ⟶ (ihom K).obj X where
  app q a := (MonoidalClosed.curry' (g a)).app q PUnit.unit
  naturality _ _ i := by
    funext a
    exact congrFun ((MonoidalClosed.curry' (g a)).naturality i) PUnit.unit

/-- The native adjunction gives both inverse identities for the ENTIRE Hom map. -/
def mapsEquiv (S : Type u) (K X : SSet.{u}) :
    ((Functor.const SimplexCategoryᵒᵖ).obj S ⟶ (ihom K).obj X) ≃ (S → (K ⟶ X)) where
  toFun phi a := MonoidalClosed.curryHomEquiv'.symm (pointOf phi a)
  invFun := fromMaps
  left_inv phi := by
    apply NatTrans.ext
    funext q a
    let e : (K ⟶ X) ≃ (𝟙_ SSet.{u} ⟶ (ihom K).obj X) :=
      MonoidalClosed.curryHomEquiv'
    change (e (e.symm (pointOf phi a))).app q PUnit.unit = phi.app q a
    rw [e.apply_symm_apply]
    rfl
  right_inv g := by
    funext a
    let e : (K ⟶ X) ≃ (𝟙_ SSet.{u} ⟶ (ihom K).obj X) :=
      MonoidalClosed.curryHomEquiv'
    change e.symm (pointOf (fromMaps g) a) = g a
    apply e.injective
    rw [e.apply_symm_apply]
    apply NatTrans.ext
    funext q p
    cases p
    rfl

/-- The native Yoneda equivalence identifies the actual whole constant-source Hom map. -/
def degreeEquiv (S : Type u) (X : SSet.{u}) (n : SimplexCategory) :
    ((Functor.const SimplexCategoryᵒᵖ).obj S ⟶
      (ihom (SSet.stdSimplex.obj n)).obj X) ≃ (S → X.obj (op n)) :=
  (mapsEquiv S (SSet.stdSimplex.obj n) X).trans
    (Equiv.piCongrRight (fun _ ↦ SSet.yonedaEquiv))

/-- Its formula evaluates at the same degree and the two actual identity operators. -/
theorem degreeEquiv_apply {S : Type u} (X : SSet.{u}) (n : SimplexCategory)
    (phi : (Functor.const SimplexCategoryᵒᵖ).obj S ⟶
      (ihom (SSet.stdSimplex.obj n)).obj X) (a : S) :
    degreeEquiv S X n phi a =
      (phi.app (op n) a).app (op n) (𝟙 (op n)) (SSet.stdSimplex.objEquiv.symm (𝟙 n)) := rfl

end
end DaggerNativeConstantIhomEquiv
