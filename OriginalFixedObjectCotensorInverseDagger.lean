import OriginalFixedObjectStrictGroupoidCotensors
import OriginalStrictDaggerGroupoidSigma

/-!
# The original inverse-dagger action on every fixed-object cotensor

Evaluation at each parameter is a native functor on the full original degree
categories. Its preservation of inverses proves that the cotensor inverse and
inverse dagger are the actual internal-Hom images of the original maps. All
parameters, degrees, simplex operators and original fixed objects are retained.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalStrictDaggerGroupoidSigma
universe u
namespace DaggerOriginalFixedObjectCotensorInverseDagger
noncomputable section

/-- Evaluation at any original parameter is a full functor of original degree categories. -/
def evaluationDegreeFunctor (K : SSet.{u}) {O : Type u} (C : FixedSimplicialCategory O)
    (n m : SimplexCategoryᵒᵖ) (i : n ⟶ m) (k : K.obj m) :
    @Functor (degreeObjects (original O (cotensor K C)) n)
      (degreeCategory (original O (cotensor K C)) n)
      (degreeObjects (original O C) m) (degreeCategory (original O C) m) where
  obj x := x
  map f := f.app m i k
  map_id x := cotensor_point_id K C x n m i k
  map_comp {x y z} f g := cotensor_point_comp K C x y z n m i f g k

/-- The inverse on the entire strict cotensor Hom is the internal-Hom image of original inverse. -/
theorem strictCotensor_inverseHom (K : SSet.{u}) {O : Type u} (C : FixedStrictGroupoids O)
    (x y : O) :
    strictInversionHom (original O (strictCotensor K C).obj) (strictCotensor K C).property x y =
      (ihom K).map (strictInversionHom (original O C.obj) C.property x y) := by
  apply NatTrans.ext
  funext n f
  apply Functor.HomObj.ext
  funext m i k
  have : @IsIso (degreeObjects (original O (strictCotensor K C).obj) n)
      (degreeCategory (original O (strictCotensor K C).obj) n) x y f :=
    (strictCotensor K C).property n x y f
  have : @IsIso (degreeObjects (original O C.obj) m)
      (degreeCategory (original O C.obj) m) x y (f.app m i k) :=
    C.property m x y (f.app m i k)
  exact (evaluationDegreeFunctor K C.obj n m i k).map_inv f

/-- Every dagger cotensor carries precisely the original inverse-dagger internal-Hom action. -/
theorem strictDaggerCotensor_sigmaHom (K : SSet.{u}) {O : Type u}
    (C : FixedStrictDaggerGroupoids O) (x y : O) :
    strictSigmaHom (originalDagger (strictDaggerCotensor K C).obj)
      (strictDaggerCotensor K C).property x y =
        (ihom K).map (strictSigmaHom (originalDagger C.obj) C.property x y) := by
  change (ihom K).map (C.obj.dagger.dagger x y) ≫
    strictInversionHom
      (original O (strictCotensor K ⟨C.obj.underlying, C.property⟩).obj)
      (strictCotensor K ⟨C.obj.underlying, C.property⟩).property y x = _
  rw [strictCotensor_inverseHom, ← Functor.map_comp]
  rfl

end
end DaggerOriginalFixedObjectCotensorInverseDagger
