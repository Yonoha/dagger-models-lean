import DaggerModels.SimplicialOpposite
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
Part I `bg.lem.creation`: discrete and codiscrete
simplicial categories give adjoints to the actual object functor. This does not
assert creation by the dagger-forgetful functor.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits

universe o v w w'

noncomputable section

namespace DaggerModels.SimplicialCat

/-- Every mapping space is the actual terminal simplicial set. -/
def codiscreteEnriched (X : Type o) : EnrichedCategory SSet.{v} X where
  Hom _ _ := 𝟙_ SSet.{v}
  id _ := 𝟙 _
  comp _ _ _ := isTerminalTensorUnit.from _
  id_comp _ _ := isTerminalTensorUnit.hom_ext _ _
  comp_id _ _ := isTerminalTensorUnit.hom_ext _ _
  assoc _ _ _ _ := isTerminalTensorUnit.hom_ext _ _

/-- The objects are literally the input type, independently of the hom universe. -/
def codiscrete (X : Type o) : SimplicialCat.{o, v} := ⟨X, codiscreteEnriched X⟩

/-- An arbitrary object function has exactly one codiscrete enriched lift. -/
def codiscreteLift (C : SimplicialCat.{o, v}) {X : Type o} (f : C.Obj → X) :
    C ⟶ codiscrete.{o, v} X where
  obj := f
  map _ _ := isTerminalTensorUnit.from _
  map_id _ := isTerminalTensorUnit.hom_ext _ _
  map_comp _ _ _ := isTerminalTensorUnit.hom_ext _ _

def codiscreteFunctor : Type o ⥤ SimplicialCat.{o, v} where
  obj := codiscrete
  map f := codiscreteLift _ f
  map_id X := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro x y
    exact isTerminalTensorUnit.hom_ext _ _
  map_comp f g := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro x y
    exact isTerminalTensorUnit.hom_ext _ _

/-- The unrestricted object function is the complete codiscrete universal property. -/
def codiscreteHomEquiv (C : SimplicialCat.{o, v}) (X : Type o) :
    (objects.obj C ⟶ X) ≃ (C ⟶ codiscrete.{o, v} X) where
  toFun := codiscreteLift C
  invFun F := F.obj
  left_inv _ := rfl
  right_inv F := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro x y
    exact isTerminalTensorUnit.hom_ext _ _

/-- The actual object functor is left adjoint to the codiscrete construction. -/
def objectsCodiscreteAdjunction : objects.{o, v} ⊣ codiscreteFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := codiscreteHomEquiv
      homEquiv_naturality_left_symm := fun _ _ ↦ rfl
      homEquiv_naturality_right := by
        intro C X Y f g
        apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
        intro x y
        exact isTerminalTensorUnit.hom_ext _ _ }

/-- The object functor preserves colimits of every size; no existence premise is used. -/
theorem objectsPreservesColimitsOfSize : PreservesColimitsOfSize.{w, w'} objects.{o, v} :=
  objectsCodiscreteAdjunction.leftAdjoint_preservesColimits

/-- Equality is proposition-valued, so the discrete hom universe remains `v`. -/
def discreteHom {X : Type o} (x y : X) : SSet.{v} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{v} (PLift (x = y)))

/-- The discrete simplicial enrichment, with independent object and hom universes. -/
def discreteEnriched (X : Type o) : EnrichedCategory SSet.{v} X where
  Hom := discreteHom
  id x := { app := fun _ _ ↦ ⟨⟨rfl⟩⟩ }
  comp x y z := { app := fun _ p ↦ ⟨⟨p.1.down.down.trans p.2.down.down⟩⟩ }
  id_comp x y := by
    ext n p
    exact Subsingleton.elim (α := ULift.{v} (PLift (x = y))) _ _
  comp_id x y := by
    ext n p
    exact Subsingleton.elim (α := ULift.{v} (PLift (x = y))) _ _
  assoc x y z t := by
    ext n p
    exact Subsingleton.elim (α := ULift.{v} (PLift (x = t))) _ _

def discrete (X : Type o) : SimplicialCat.{o, v} := ⟨X, discreteEnriched X⟩

/-- Equality arrows map to enriched identities, transported along the object function. -/
def discreteLift (X : Type o) (C : SimplicialCat.{o, v}) (f : X → C.Obj) :
    discrete.{o, v} X ⟶ C where
  obj := f
  map x y :=
    { app := fun n p ↦ p.down.down ▸ (eId SSet (f x)).app n PUnit.unit
      naturality := by
        intro n m α
        funext p
        obtain ⟨⟨h⟩⟩ := p
        subst y
        exact congrFun ((eId SSet (f x)).naturality α) PUnit.unit }
  map_id x := by
    ext n p
    cases p
    rfl
  map_comp x y z := by
    ext n p
    obtain ⟨⟨⟨h⟩⟩, ⟨⟨h'⟩⟩⟩ := p
    subst y
    subst z
    exact (congrArg (fun k ↦ k.app n ((eId SSet (f x)).app n PUnit.unit))
      (e_id_comp SSet (f x) (f x))).symm

/-- Discrete enriched functors are exactly arbitrary object functions. -/
def discreteHomEquiv (X : Type o) (C : SimplicialCat.{o, v}) :
    (discrete.{o, v} X ⟶ C) ≃ (X ⟶ objects.obj C) where
  toFun F := F.obj
  invFun := discreteLift X C
  left_inv F := by
    apply EnrichedFunctor.ext SSet (F := discreteLift X C F.obj) (G := F) (fun _ ↦ rfl)
    intro x y
    ext n p
    obtain ⟨⟨h⟩⟩ := p
    subst y
    exact (congrArg (fun k ↦ k.app n PUnit.unit) (F.map_id x)).symm
  right_inv _ := rfl

theorem discreteHomEquiv_naturality (X : Type o) (C D : SimplicialCat.{o, v})
    (G : C ⟶ D) (F : discrete.{o, v} X ⟶ C) :
    discreteHomEquiv X D (F ≫ G) = discreteHomEquiv X C F ≫ objects.map G := rfl

/-- The actual discrete construction, with its object and hom universes independent. -/
def discreteFunctor : Type o ⥤ SimplicialCat.{o, v} :=
  Adjunction.leftAdjointOfEquiv discreteHomEquiv discreteHomEquiv_naturality

def discreteObjectsAdjunction : discreteFunctor.{o, v} ⊣ objects :=
  Adjunction.adjunctionOfEquivLeft discreteHomEquiv discreteHomEquiv_naturality

/-- The object functor preserves limits of every size, without an existence premise. -/
theorem objectsPreservesLimitsOfSize : PreservesLimitsOfSize.{w, w'} objects.{o, v} :=
  discreteObjectsAdjunction.rightAdjoint_preservesLimits

end DaggerModels.SimplicialCat
