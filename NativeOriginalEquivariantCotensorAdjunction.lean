import OriginalSimplicialEquivariantEnrichedAdjunction

/-! Reuse the existing full equivariant currying proof for arbitrary ORIGINAL C2 targets. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalSimplicialEquivariantParameterTensor
universe u
namespace DaggerNativeOriginalEquivariantCotensorAdjunction
noncomputable section

def cotensorAction (K : SSet.{u}) (B : Action SSet.{u} C2.{u}) :
    Action SSet.{u} C2.{u} := ((ihom K).mapAction C2.{u}).obj B

theorem cotensor_action (K : SSet.{u}) (B : Action SSet.{u} C2.{u}) (g : C2.{u}) :
    ((cotensorAction K B).ρ g).asHom = (ihom K).map ((B.ρ g).asHom) := rfl

/-- Uncurry the entire original equivariant Hom map, with action on the first factor. -/
def uncurryAction (K : SSet.{u}) (A : Action SSet.{u} C2.{u})
    (B : Action SSet.{u} C2.{u})
    (f : A ⟶ cotensorAction K B) :
    simplicialParameterTensor A K ⟶ B where
  hom := (β_ A.V K).hom ≫ uncurry f.hom
  comm g := by
    apply NatTrans.ext
    funext n p
    rcases p with ⟨e, k⟩
    have h := congrFun (NatTrans.congr_app (f.comm g) n) e
    change f.hom.app n (((A.ρ g).asHom).app n e) =
      (((cotensorAction K B).ρ g).asHom).app n
        (f.hom.app n e) at h
    rw [cotensor_action] at h
    exact congrArg (fun z ↦ z.app n (𝟙 n) k) h

/-- Curry each full parameter family, retaining equivariance of every original action element. -/
def curryAction (K : SSet.{u}) (A : Action SSet.{u} C2.{u})
    (B : Action SSet.{u} C2.{u})
    (q : simplicialParameterTensor A K ⟶ B) :
    A ⟶ cotensorAction K B where
  hom := curry ((β_ K A.V).hom ≫ q.hom)
  comm g := by
    apply NatTrans.ext
    funext n e
    change (curry ((β_ K A.V).hom ≫ q.hom)).app n (((A.ρ g).asHom).app n e) =
      (((cotensorAction K B).ρ g).asHom).app n
        ((curry ((β_ K A.V).hom ≫ q.hom)).app n e)
    rw [cotensor_action]
    apply Functor.HomObj.ext
    funext m i k
    have ha := (congrFun (((A.ρ g).asHom).naturality i) e).symm
    change A.V.map i (((A.ρ g).asHom).app n e) =
      ((A.ρ g).asHom).app m (A.V.map i e) at ha
    change q.hom.app m (A.V.map i (((A.ρ g).asHom).app n e), k) =
      ((B).ρ g).asHom.app m (q.hom.app m (A.V.map i e, k))
    rw [ha]
    exact congrFun (NatTrans.congr_app (q.comm g) m) (A.V.map i e, k)

/-- Exact equivariant currying on all original simplicial parameters. -/
def cotensorActionHomEquiv (K : SSet.{u}) (A : Action SSet.{u} C2.{u})
    (B : Action SSet.{u} C2.{u}) :
    (A ⟶ cotensorAction K B) ≃
      (simplicialParameterTensor A K ⟶ B) where
  toFun := uncurryAction K A B
  invFun := curryAction K A B
  left_inv f := by
    apply Action.Hom.ext
    change curry ((β_ K A.V).hom ≫ ((β_ A.V K).hom ≫ uncurry f.hom)) = f.hom
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]
  right_inv q := by
    apply Action.Hom.ext
    change (β_ A.V K).hom ≫ uncurry (curry ((β_ K A.V).hom ≫ q.hom)) = q.hom
    rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end
end DaggerNativeOriginalEquivariantCotensorAdjunction
