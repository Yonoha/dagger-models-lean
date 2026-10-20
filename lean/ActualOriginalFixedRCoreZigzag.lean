import ActualFixedDaggerCoreComparison
import NativeOriginalFixedDaggerReplacement

/-! The original fixed-object R, first core comparison and full groupoid completion
form the literal three-arrow zigzag, with ALL original Hom maps weak.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance OrdinaryRigidification
open DaggerActualDaggerOrdinaryCore DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectLegacyDaggerEquivalence DaggerNativeDaggerObjectRestriction
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualOriginalFixedRCoreZigzag
noncomputable section

def ambient (X : DaggerSSet.{u})
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj) :
    FixedDaggerCategory DaggerUnitaryInterval.Vertex :=
  restriction (DaggerRigidification.obj X) b

def replacedPart (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj) :
    FixedDaggerCategory DaggerUnitaryInterval.Vertex :=
  DaggerNativeFixedDaggerIsomorphismPart.part
    ((DaggerNativeOriginalFixedDaggerReplacement.replacement R).obj (ambient X b))

def post (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj) :
    DaggerNativeFixedDaggerIsomorphismPart.part (ambient X b) ⟶ replacedPart R X b :=
  DaggerNativeFixedDaggerIsomorphismPart.map
    (DaggerNativeOriginalFixedDaggerReplacement.unit R (ambient X b))

theorem post_weak (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj) :
    WeakEquivalence (post R X b) := by
  have := DaggerNativeOriginalFixedDaggerReplacement.unit_weak R (ambient X b)
  exact DaggerNativeFixedDaggerIsomorphismPart.map_weak _

theorem original_R_unit_exact (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj) :
    toLegacyHom (DaggerNativeOriginalFixedDaggerReplacement.unit R (ambient X b)) =
      R.unit.app (DaggerFixedCategoryConnectedColimits.reindex (DaggerRigidification.obj X) b) :=
  DaggerNativeOriginalFixedDaggerReplacement.roundtrip_hom _

theorem original_R_target_fibrant (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj) :
    IsFibrant ((DaggerNativeOriginalFixedDaggerReplacement.replacement R).obj (ambient X b)) :=
  DaggerNativeOriginalFixedDaggerReplacement.replacement_fibrant R (ambient X b)

theorem post_triangle (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj) :
    post R X b ≫ DaggerNativeFixedDaggerIsomorphismPart.inclusion
        ((DaggerNativeOriginalFixedDaggerReplacement.replacement R).obj (ambient X b)) =
      DaggerNativeFixedDaggerIsomorphismPart.inclusion (ambient X b) ≫
        DaggerNativeOriginalFixedDaggerReplacement.unit R (ambient X b) :=
  DaggerNativeFixedDaggerIsomorphismPart.inclusion_natural _

theorem all_three_arrows_weak (R : FunctorialFibrantReplacement.{u})
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (a : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj (coreDagger X)).Obj)
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj)
    (h : (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X).obj ∘ a = b) :
    WeakEquivalence (post R X b) ∧
    WeakEquivalence (DaggerActualFixedDaggerCoreComparison.comparison X a b h) ∧
    WeakEquivalence (DaggerActualDaggerKanObjectRestriction.comparison (coreDagger X) a) :=
  ⟨post_weak R X b, DaggerActualFixedDaggerCoreComparison.comparison_weak X a b h,
    DaggerActualFixedDaggerCoreComparison.completion_weak X a⟩

end
end DaggerActualOriginalFixedRCoreZigzag
