import NativeDaggerObjectRestriction
import ActualRigidifiedDaggerCoreCompletion
import OriginalFixedObjectOrdinaryCellAdjunction

/-! Keep two distinct labels even when the two original vertices coincide. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalFixedObjectDaggerCategories DaggerNativeDaggerObjectRestriction
open DaggerActualDaggerOrdinaryCore DaggerActualRigidifiedDaggerCoreCompletion
open DaggerOriginalSimplicialGroupoidCompletionDagger
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualDaggerCoreEndpointRestriction
noncomputable section

def labels (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet _⦋0⦌) :
    TwoObjectDaggerGraph.Vertex.{u} → (DaggerRigidification.obj (coreDagger X)).Obj :=
  fun i ↦ if i.down then endpoint X y else endpoint X x

theorem labels_left (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet _⦋0⦌) : labels X x y TwoObjectDaggerGraph.left = endpoint X x :=
  rfl

theorem labels_right (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet _⦋0⦌) : labels X x y TwoObjectDaggerGraph.right = endpoint X y :=
  rfl

def source (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet _⦋0⦌) :
    FixedDaggerCategory TwoObjectDaggerGraph.Vertex.{u} :=
  restriction (DaggerRigidification.obj (coreDagger X)) (labels X x y)

/-- Complete on the whole object set before restricting to the two labels. -/
def target (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet _⦋0⦌) :
    FixedDaggerCategory TwoObjectDaggerGraph.Vertex.{u} :=
  restriction (daggerCompletion (DaggerRigidification.obj (coreDagger X))) (labels X x y)

def comparison (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet _⦋0⦌) :
    source X x y ⟶ target X x y :=
  DaggerNativeDaggerObjectRestriction.map
    (daggerLocalization (DaggerRigidification.obj (coreDagger X))) (labels X x y)

theorem comparison_hom (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet _⦋0⦌) (i j : TwoObjectDaggerGraph.Vertex.{u}) :
    (comparison X x y).underlying.map i j =
      (unit X).underlying.map (labels X x y i) (labels X x y j) :=
  rfl

theorem comparison_weak (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet _⦋0⦌) : WeakEquivalence (comparison X x y) := by
  apply DaggerNativeDaggerObjectRestriction.map_weak
  intro a b
  exact unit_hom_weak X a b

theorem comparison_left_right (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet _⦋0⦌) :
    (comparison X x y).underlying.map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right =
      (unit X).underlying.map (endpoint X x) (endpoint X y) :=
  rfl

end
end DaggerActualDaggerCoreEndpointRestriction
