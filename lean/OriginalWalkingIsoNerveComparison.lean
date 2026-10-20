import OriginalWalkingIsoIntegerObstruction
import DaggerModels.OrdinaryRigidification
import DaggerModels.SimplicialObjectAdjunctions
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
The actual nerve of the ordinary walking isomorphism is compared with the
actual coherent nerve of its codiscrete simplicial enrichment. Both sets of
simplices are controlled by their vertices because their Homs are unique.
-/

set_option autoImplicit false

open CategoryTheory CartesianMonoidalCategory Opposite Simplicial

universe u

namespace DaggerModels.OriginalWalkingIsoNerveComparison

open OriginalWalkingIsoIntegerObstruction

noncomputable section

/-- The original codiscrete simplicial category on the walking isomorphism. -/
def walkingSimplicial : SimplicialCat.{u, u} :=
  SimplicialCat.codiscrete walkingIso.{u}

/-- An ordinary simplex determines the unique enriched simplex with those vertices. -/
def encodeDegree (n : SimplexCategoryᵒᵖ)
    (x : (nerve walkingIso.{u}).obj n) :
    (OrdinaryRigidification.coherentNerve.obj walkingSimplicial.{u}).obj n :=
  ⟨SimplicialCat.codiscreteLift (OrdinaryRigidification.simplexThickening n.unop)
    (fun i ↦ x.obj i.as.down)⟩

/-- An enriched simplex determines the unique ordinary simplex with those vertices. -/
def decodeDegree (n : SimplexCategoryᵒᵖ)
    (P : (OrdinaryRigidification.coherentNerve.obj walkingSimplicial.{u}).obj n) :
    (nerve walkingIso.{u}).obj n where
  obj i := P.down.obj (.mk (ULift.up i))
  map _ := ⟨⟨⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem encodeDegree_vertex (n : SimplexCategoryᵒᵖ)
    (x : (nerve walkingIso.{u}).obj n) (i : Fin (n.unop.len + 1)) :
    (encodeDegree n x).down.obj (.mk (ULift.up i)) = x.obj i := rfl

@[simp]
theorem decodeDegree_vertex (n : SimplexCategoryᵒᵖ)
    (P : (OrdinaryRigidification.coherentNerve.obj walkingSimplicial.{u}).obj n)
    (i : Fin (n.unop.len + 1)) :
    (decodeDegree n P).obj i = P.down.obj (.mk (ULift.up i)) := rfl

private theorem encode_decode (n : SimplexCategoryᵒᵖ)
    (P : (OrdinaryRigidification.coherentNerve.obj walkingSimplicial.{u}).obj n) :
    encodeDegree n (decodeDegree n P) = P := by
  apply ULift.ext
  apply EnrichedFunctor.ext SSet
  · intro i j
    exact isTerminalTensorUnit.hom_ext _ _
  · intro i
    cases i
    rfl

private theorem decode_encode (n : SimplexCategoryᵒᵖ)
    (x : (nerve walkingIso.{u}).obj n) :
    decodeDegree n (encodeDegree n x) = x := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  apply ULift.ext
  exact Unit.ext _ _

/-- The all-degree comparison preserves every simplex operator. -/
def comparisonHom : nerve walkingIso.{u} ⟶
    OrdinaryRigidification.coherentNerve.obj walkingSimplicial.{u} where
  app n := encodeDegree n
  naturality n m f := by
    funext x
    apply ULift.ext
    apply EnrichedFunctor.ext SSet
    · intro i j
      exact isTerminalTensorUnit.hom_ext _ _
    · intro i
      rfl

/-- The inverse comparison uses exactly the same vertex restrictions. -/
def comparisonInv : OrdinaryRigidification.coherentNerve.obj walkingSimplicial.{u} ⟶
    nerve walkingIso.{u} where
  app n := decodeDegree n
  naturality n m f := by
    funext P
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j g
    apply ULift.ext
    exact Unit.ext _ _

/-- The thin ordinary nerve and the original codiscrete coherent nerve coincide. -/
def comparisonIso : nerve walkingIso.{u} ≅
    OrdinaryRigidification.coherentNerve.obj walkingSimplicial.{u} where
  hom := comparisonHom
  inv := comparisonInv
  hom_inv_id := by
    ext n x
    exact decode_encode n x
  inv_hom_id := by
    ext n P
    exact encode_decode n P

/-- At degree zero the comparison is the identity on the chosen object. -/
theorem comparison_zero (x : walkingIso.{u}) :
    (comparisonIso.{u}.hom.app (op ⦋0⦌) (ComposableArrows.mk₀ x)).down.obj
      (.mk (ULift.up (0 : Fin 1))) = x := rfl

/-- The two endpoints of a one-simplex are preserved literally. -/
theorem comparison_one_endpoints {x y : walkingIso.{u}} (f : x ⟶ y) :
    (comparisonIso.{u}.hom.app (op ⦋1⦌) (ComposableArrows.mk₁ f)).down.obj
      (.mk (ULift.up (0 : Fin 2))) = x ∧
    (comparisonIso.{u}.hom.app (op ⦋1⦌) (ComposableArrows.mk₁ f)).down.obj
      (.mk (ULift.up (1 : Fin 2))) = y := by
  constructor <;> rfl

end

end DaggerModels.OriginalWalkingIsoNerveComparison
