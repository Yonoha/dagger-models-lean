import FixedGraphDecomposition
import FreeBC2Generators
import PlacementStructure
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.CategoryTheory.Presentable.Adjunction

/-! Actual upper and free diagonal placements into the original arbitrary-O dagger graph category.
The only object-set choice is the frozen same-type chosen order. -/

open CategoryTheory Limits DaggerModels DaggerFixedGraph DaggerPlacementStructure

universe u

namespace DaggerFixedGraphPlacements

noncomputable section

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable (O : Type u)

abbrev UpperIndex := @Upper O (chosenLinearOrder O)
abbrev UpperFactors := UpperIndex O → SSet.{u}
abbrev DiagonalFactors := O → (DaggerFreeBC2.BC2 ⥤ SSet.{u})

instance familyColimits {I : Type u} {C : Type (u + 1)} [Category.{u} C]
    [HasColimitsOfSize.{u, u} C] : HasColimitsOfSize.{u, u} (I → C) :=
  Adjunction.has_colimits_of_equivalence (piEquivalenceFunctorDiscrete I C).functor

instance familyLimits {I : Type u} {C : Type (u + 1)} [Category.{u} C]
    [HasLimitsOfSize.{u, u} C] : HasLimitsOfSize.{u, u} (I → C) :=
  Adjunction.has_limits_of_equivalence (piEquivalenceFunctorDiscrete I C).functor

/-- Literal original coordinate evaluation, on the original graph objects and maps. -/
def homEval (x y : O) : FixedDaggerSimplicialGraph O ⥤ SSet.{u} where
  obj G := G.Hom x y
  map f := f.map x y

/-- Inactive upper coordinates are the same chosen initial simplicial set. -/
def emptyUpper : UpperFactors O := fun _ ↦ ⊥_ SSet.{u}

/-- Inactive diagonals are actual initial BC₂ diagrams. -/
def emptyDiagonal : DiagonalFactors O := fun _ ↦ ⊥_ (DaggerFreeBC2.BC2 ⥤ SSet.{u})

def emptyUpperIsInitial : IsInitial (emptyUpper O) := initialFamilyIsInitial _
def emptyDiagonalIsInitial : IsInitial (emptyDiagonal O) := initialFamilyIsInitial _

def upperParameterPlacement (p : UpperIndex O) : SSet.{u} ⥤ ChosenFunctorParameters O :=
  single p ⋙ includeLeft (emptyDiagonal O)

def diagonalParameterPlacement (x : O) : SSet.{u} ⥤ ChosenFunctorParameters O :=
  DaggerFreeBC2.free ⋙ single x ⋙ includeRight (emptyUpper O)

def upperPlacement (p : UpperIndex O) : SSet.{u} ⥤ FixedDaggerSimplicialGraph O :=
  upperParameterPlacement O p ⋙ (fixedObjectDecomposition O).inverse

def diagonalPlacement (x : O) : SSet.{u} ⥤ FixedDaggerSimplicialGraph O :=
  diagonalParameterPlacement O x ⋙ (fixedObjectDecomposition O).inverse

def upperParameterEval (p : UpperIndex O) : ChosenFunctorParameters O ⥤ SSet.{u} :=
  CategoryTheory.Prod.fst _ _ ⋙ Pi.eval (fun _ : UpperIndex O ↦ SSet.{u}) p

def diagonalParameterEval (x : O) : ChosenFunctorParameters O ⥤ SSet.{u} :=
  CategoryTheory.Prod.snd _ _ ⋙ Pi.eval (fun _ : O ↦ DaggerFreeBC2.BC2 ⥤ SSet.{u}) x ⋙
    DaggerFreeBC2.ev

def upperParameterAdjunction (p : UpperIndex O) :
    upperParameterPlacement O p ⊣ upperParameterEval O p :=
  (singleAdjunction p).comp (includeLeftAdjunction (emptyDiagonalIsInitial O))

def diagonalParameterAdjunction (x : O) :
    diagonalParameterPlacement O x ⊣ diagonalParameterEval O x :=
  ((DaggerFreeBC2.freeAdjunction.comp (singleAdjunction x)).comp
    (includeRightAdjunction (emptyUpperIsInitial O)))

/-- The upper right adjoint is the original Hom(p₁,p₂), as a whole functor. -/
def upperEvalIso (p : UpperIndex O) :
    (fixedObjectDecomposition O).functor ⋙ upperParameterEval O p ≅
      homEval O p.val.1 p.val.2 := Iso.refl _

/-- Diagonal evaluation forgets the original dagger involution, retaining its underlying Hom. -/
def diagonalEvalIso (x : O) :
    (fixedObjectDecomposition O).functor ⋙ diagonalParameterEval O x ≅
      homEval O x x := Iso.refl _

def upperAdjunction (p : UpperIndex O) : upperPlacement O p ⊣ homEval O p.val.1 p.val.2 :=
  ((upperParameterAdjunction O p).comp (fixedObjectDecomposition O).symm.toAdjunction).ofNatIsoRight
    (upperEvalIso O p)

def diagonalAdjunction (x : O) : diagonalPlacement O x ⊣ homEval O x x :=
  ((diagonalParameterAdjunction O x).comp
    (fixedObjectDecomposition O).symm.toAdjunction).ofNatIsoRight
    (diagonalEvalIso O x)

instance upperParameterEvalPreservesColimits (p : UpperIndex O) :
    PreservesColimitsOfSize.{u, u} (upperParameterEval O p) := by
  dsimp [upperParameterEval]
  infer_instance

instance diagonalParameterEvalPreservesColimits (x : O) :
    PreservesColimitsOfSize.{u, u} (diagonalParameterEval O x) := by
  dsimp [diagonalParameterEval, DaggerFreeBC2.ev]
  infer_instance

instance upperHomEvalPreservesColimits (p : UpperIndex O) :
    PreservesColimitsOfSize.{u, u} (homEval O p.val.1 p.val.2) :=
  preservesColimits_of_natIso (upperEvalIso O p)

instance diagonalHomEvalPreservesColimits (x : O) :
    PreservesColimitsOfSize.{u, u} (homEval O x x) :=
  preservesColimits_of_natIso (diagonalEvalIso O x)

/-- Finite simplicial domains remain finitely presentable in the original fixed-object category. -/
theorem upperPlacement_finitelyPresentable (p : UpperIndex O) (K : SSet.{u}) [K.Finite] :
    IsFinitelyPresentable.{u} ((upperPlacement O p).obj K) :=
  (upperAdjunction O p).isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 K

theorem diagonalPlacement_finitelyPresentable (x : O) (K : SSet.{u}) [K.Finite] :
    IsFinitelyPresentable.{u} ((diagonalPlacement O x).obj K) :=
  (diagonalAdjunction O x).isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 K

end

end DaggerFixedGraphPlacements
