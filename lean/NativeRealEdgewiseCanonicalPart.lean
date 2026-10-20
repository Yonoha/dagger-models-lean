import NativeRealEdgewiseCanonicalConstants
import OriginalFullVertexWeakEquivalenceRestriction
import OriginalEC2CanonicalVertexKan

/-! Full subcomplexes on literal original edgewise constants and their natural comparison. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeRealEdgewiseCanonicalConstants DaggerNativeRealEdgewiseContinuousComparison
open DaggerNativeRealEdgewiseHomotopyFixedPointComparison
open DaggerOriginalFullVertexSubcomplex DaggerOriginalFullVertexWeakEquivalenceRestriction
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalEC2CanonicalVertexSubcomplex DaggerOriginalEC2CanonicalVertexKan
universe u
namespace DaggerNativeRealEdgewiseCanonicalPart
noncomputable section

def vertices (X : DaggerSSet.{u}) :
    Set ((edgewiseHomotopyFixedPointFunctor.obj X).obj (op ⦋0⦌)) :=
  Set.range (edgewiseCanonicalZero X)

def canonicalSubcomplex (X : DaggerSSet.{u}) :
    (edgewiseHomotopyFixedPointFunctor.obj X).Subcomplex :=
  fullVertexSubcomplex _ (vertices X)

instance canonicalSubcomplex_kan (X : DaggerSSet.{u}) :
    SSet.KanComplex (canonicalSubcomplex X).toSSet := by
  have : SSet.KanComplex (edgewiseHomotopyFixedPointFunctor.obj X) :=
    mappingSing_kan (realizedEdgewiseContinuousFunctor.obj X)
  change SSet.KanComplex
    (fullVertexSubcomplex (edgewiseHomotopyFixedPointFunctor.obj X) (vertices X) : SSet.{u})
  infer_instance

theorem vertices_map {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    ∀ z, z ∈ vertices X →
      (edgewiseHomotopyFixedPointFunctor.map f).app (op ⦋0⦌) z ∈ vertices Y := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f.hom.app (op ⦋0⦌) x, (edgewiseCanonicalZero_natural f x).symm⟩

def map {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    (canonicalSubcomplex X).toSSet ⟶ (canonicalSubcomplex Y).toSSet :=
  restrictedMap (vertices X) (vertices Y) (edgewiseHomotopyFixedPointFunctor.map f)
    (vertices_map f)

theorem map_inclusion {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    map f ≫ (canonicalSubcomplex Y).ι =
      (canonicalSubcomplex X).ι ≫ edgewiseHomotopyFixedPointFunctor.map f :=
  restrictedMap_ι _ _ _ _

def canonicalFunctor : DaggerSSet.{u} ⥤ SSet.{u} where
  obj X := (canonicalSubcomplex X).toSSet
  map := map
  map_id X := by
    apply NatTrans.ext
    funext n s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app (edgewiseHomotopyFixedPointFunctor.map_id X) n) s.1
  map_comp f g := by
    apply NatTrans.ext
    funext n s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app (edgewiseHomotopyFixedPointFunctor.map_comp f g) n) s.1

def inclusion : canonicalFunctor.{u} ⟶ edgewiseHomotopyFixedPointFunctor where
  app X := (canonicalSubcomplex X).ι
  naturality _ _ f := map_inclusion f

theorem comparison_preservesVertices (X : DaggerSSet.{u}) :
    ∀ z, z ∈ vertices X →
      (homotopyFixedPointComparison.app X).app (op ⦋0⦌) z ∈ canonicalVertices X := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x, (canonicalZero_comparison X x).symm⟩

def comparison (X : DaggerSSet.{u}) :
    canonicalFunctor.obj X ⟶ canonicalVertexFunctor.obj X :=
  restrictedMap (vertices X) (canonicalVertices X) (homotopyFixedPointComparison.app X)
    (comparison_preservesVertices X)

theorem comparison_inclusion (X : DaggerSSet.{u}) :
    comparison X ≫ (canonicalVertexSubcomplex X).ι =
      (canonicalSubcomplex X).ι ≫ homotopyFixedPointComparison.app X :=
  restrictedMap_ι _ _ _ _

def naturalComparison : canonicalFunctor.{u} ⟶ canonicalVertexFunctor where
  app := comparison
  naturality X Y f := by
    apply NatTrans.ext
    funext n s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app (homotopyFixedPointComparison.naturality f) n) s.1

end
end DaggerNativeRealEdgewiseCanonicalPart
