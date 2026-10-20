import OriginalFixedObjectCotensors

/-! Reuse the original chosen-product comparison for the native internal Hom. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite CartesianMonoidalCategory
open DaggerOriginalFixedObjectCotensors
attribute [local instance] ihomBraided
universe u
namespace DaggerNativeIhomBinaryProduct
noncomputable section

def tensorIhomIso (K X Y : SSet.{u}) :
    (ihom K).obj X ⊗ (ihom K).obj Y ≅ (ihom K).obj (X ⊗ Y) :=
  Functor.Monoidal.μIso (ihom K) X Y

theorem tensorIhomIso_app (K X Y : SSet.{u}) (n m : SimplexCategoryᵒᵖ)
    (α : n ⟶ m) (f : ((ihom K).obj X).obj n) (g : ((ihom K).obj Y).obj n)
    (a : K.obj m) :
    ((tensorIhomIso K X Y).hom.app n (f, g)).app m α a =
      (f.app m α a, g.app m α a) := by
  apply Prod.ext
  · have h := congrFun (NatTrans.congr_app (Functor.Monoidal.μ_fst (ihom K) X Y) n) (f, g)
    exact congrArg (fun t : ((ihom K).obj X).obj n ↦ t.app m α a) h
  · have h := congrFun (NatTrans.congr_app (Functor.Monoidal.μ_snd (ihom K) X Y) n) (f, g)
    exact congrArg (fun t : ((ihom K).obj Y).obj n ↦ t.app m α a) h

end
end DaggerNativeIhomBinaryProduct
