import NativeNerveOppositeIso
import NativeDaggerDegreeCotensor

/-! The ordinary nerve dagger uses the existing native reversal of composable arrows. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalNerveOppositeMap DaggerNativeNerveOppositeIso
universe u
namespace DaggerNativeOrdinaryDaggerNerve
noncomputable section
variable (A : Type u) [Category.{u} A] [DaggerCategory A]

/-- The original ordinary dagger, regarded as a covariant functor to the opposite. -/
def toOpposite : A ⥤ Aᵒᵖ where
  obj := op
  map f := (DaggerCategory.dagger f).op
  map_id x := by rw [DaggerCategory.dagger_id]; rfl
  map_comp f g := by rw [DaggerCategory.dagger_comp]; rfl

/-- Reuse the previously verified native nerve/opposite isomorphism. -/
def reversal : nerve A ⟶ (nerve A).op :=
  nerveMap (toOpposite A) ≫ (nerveOppositeIso A).inv

/-- Every original object of a chain is retained, in the reversed order. -/
theorem reversal_obj (n : SimplexCategory) (F : Fin (n.len + 1) ⥤ A)
    (i : Fin (n.len + 1)) :
    (SSet.opObjEquiv ((reversal A).app (op n) F)).obj i = F.obj i.rev := rfl

/-- Every arrow is exactly the original dagger of its native reversed arrow. -/
theorem reversal_map (n : SimplexCategory) (F : Fin (n.len + 1) ⥤ A)
    {i j : Fin (n.len + 1)} (f : i ⟶ j) :
    (SSet.opObjEquiv ((reversal A).app (op n) F)).map f =
      DaggerCategory.dagger (((reverseDiagram F).map f).unop) := rfl

end
end DaggerNativeOrdinaryDaggerNerve
