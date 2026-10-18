import NativeOriginalCotensorFunctor

/-! Evaluate the two ORIGINAL internal-Hom parameters along an arbitrary parameter map. -/
set_option autoImplicit false
open CategoryTheory MonoidalClosed
universe u
namespace DaggerNativeIhomParameterDiagonal
noncomputable section

/-- Pointwise evaluation along the graph of theta, with both native naturality laws. -/
def diagonalHom {I K : SSet.{u}} (theta : K ⟶ I) (X : SSet.{u}) :
    (ihom I).obj ((ihom K).obj X) ⟶ (ihom K).obj X where
  app q F :=
    { app r a k := (F.app r a (theta.app r k)).app r (𝟙 r) k
      naturality {r s} b a := by
        funext k
        have ht := congrFun (theta.naturality b) k
        change theta.app s (K.map b k) = I.map b (theta.app r k) at ht
        have hF := congrFun (F.naturality b a) (theta.app r k)
        change F.app s (a ≫ b) (I.map b (theta.app r k)) =
          ((ihom K).obj X).map b (F.app r a (theta.app r k)) at hF
        change (F.app s (a ≫ b) (theta.app s (K.map b k))).app s (𝟙 s)
          (K.map b k) = X.map b ((F.app r a (theta.app r k)).app r (𝟙 r) k)
        rw [ht, hF]
        simpa only [Category.id_comp, Category.comp_id] using
          congrFun ((F.app r a (theta.app r k)).naturality b (𝟙 r)) k }
  naturality _ _ _ := by
    funext F
    apply Functor.HomObj.ext
    funext r a k
    rfl

/-- Every original target map commutes with this entire internal-Hom map. -/
theorem diagonalHom_naturality {I K X Y : SSet.{u}} (theta : K ⟶ I) (f : X ⟶ Y) :
    (ihom I).map ((ihom K).map f) ≫ diagonalHom theta Y =
      diagonalHom theta X ≫ (ihom K).map f := by
  apply NatTrans.ext
  funext q F
  apply Functor.HomObj.ext
  funext r a k
  rfl

end
end DaggerNativeIhomParameterDiagonal
