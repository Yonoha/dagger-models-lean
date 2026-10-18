import NativeAmbientDaggerFibrancy
import OriginalFixedObjectLegacyDaggerEquivalence

/-! Reuse the ORIGINAL Hom evaluation and its full limit preservation on the SAME ambient
fixed-object presentation. Maps are precisely the original fixed Hom maps, without transports.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectLegacyDaggerEquivalence
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeAmbientDaggerHomEvaluation
noncomputable section

def homEval (O : Type u) (x y : O) : FixedDaggerCategory O ⥤ SSet.{u} :=
  toLegacyFunctor O ⋙ DaggerFixedCategoryHomLimits.homEval O x y

theorem homEval_obj {O : Type u} (C : FixedDaggerCategory O) (x y : O) :
    (homEval O x y).obj C = C.underlying.enriched.Hom x y := rfl

theorem homEval_map {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) (x y : O) :
    (homEval O x y).map F = F.underlying.map x y := rfl

instance preservesLimits (O : Type u) (x y : O) :
    PreservesLimitsOfSize.{u, u} (homEval O x y) := by
  have : (toLegacyFunctor O).IsRightAdjoint :=
    (legacyDaggerEquivalence O).symm.toAdjunction.isRightAdjoint
  have : PreservesLimitsOfSize.{u, u} (DaggerFixedCategoryHomLimits.homEval O x y) :=
    DaggerFixedCategoryHomLimits.homEvalPreservesSmallLimits O x y
  unfold homEval
  infer_instance

theorem map_isPullback {O : Type u} (x y : O) {A B C D : FixedDaggerCategory O}
    {p : A ⟶ B} {q : A ⟶ C} {f : B ⟶ D} {g : C ⟶ D} (h : IsPullback p q f g) :
    IsPullback (p.underlying.map x y) (q.underlying.map x y)
      (f.underlying.map x y) (g.underlying.map x y) :=
  IsPullback.map (homEval O x y) h

end
end DaggerNativeAmbientDaggerHomEvaluation
