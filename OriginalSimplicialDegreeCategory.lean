import DaggerModels.SimplicialCat
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# The original ordinary category in each simplicial degree

Evaluate the original enriched Hom simplicial sets at a simplex-category object. Pointwise
evaluation is lax monoidal with literal identity unit and product comparison maps. Native
transport of enrichment and the native Type-enriched/ordinary-category construction retain
exactly the original objects, Hom degrees, identities and compositions. Every simplicial
operator induces the literal identity-on-objects functor between these degree categories.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial
open DaggerModels

universe u

namespace DaggerOriginalSimplicialDegreeCategory

noncomputable section

/-- Evaluate precisely the original Hom at the same simplicial degree. -/
def degreeEvaluation (n : SimplexCategoryᵒᵖ) : SSet.{u} ⥤ Type u :=
  (evaluation SimplexCategoryᵒᵖ (Type u)).obj n

/-- Original degree evaluation preserves the literal pointwise unit and ordinary products. -/
instance degreeEvaluation_laxMonoidal (n : SimplexCategoryᵒᵖ) :
    (degreeEvaluation.{u} n).LaxMonoidal where
  ε := id
  μ _ _ := id
  μ_natural_left _ _ := rfl
  μ_natural_right _ _ := rfl
  associativity _ _ _ := rfl
  left_unitality _ := rfl
  right_unitality _ := rfl

/-- A type synonym of the same original object type, indexed by its category structure. -/
def degreeObjects (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) : Type u :=
  TransportEnrichment (degreeEvaluation.{u} n) C.Obj

/-- Native transport retains the same original Hom degrees and pointwise operations. -/
instance degreeEnrichment (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    EnrichedCategory (Type u) (degreeObjects C n) :=
  inferInstanceAs (EnrichedCategory (Type u)
    (TransportEnrichment (degreeEvaluation.{u} n) C.Obj))

/-- The native enrichment transport gives the exact original degree category. -/
instance degreeCategory (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    Category.{u} (degreeObjects C n) :=
  categoryOfEnrichedCategoryType (degreeObjects C n)

/-- Degree Hom types are precisely the original Hom simplicial-set degrees. -/
theorem degreeHom_eq (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) (x y : degreeObjects C n) :
    ((x : degreeObjects C n) ⟶ (y : degreeObjects C n)) = (C.enriched.Hom x y).obj n := rfl

/-- The degree identity is the same original enriched identity evaluated at the unit. -/
theorem degreeId_eq (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) (x : degreeObjects C n) :
    (𝟙 (x : degreeObjects C n)) = (C.enriched.id x).app n PUnit.unit := rfl

/-- The degree composition is the same original enriched composition on the original pair. -/
theorem degreeComp_eq (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) {x y z : degreeObjects C n}
    (f : (x : degreeObjects C n) ⟶ y) (g : (y : degreeObjects C n) ⟶ z) :
    f ≫ g = (C.enriched.comp x y z).app n (f, g) := rfl

/-- Every original simplicial operator is an identity-on-objects degree functor. -/
def degreeMap (C : SimplicialCat.{u, u}) {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    degreeObjects C n ⥤ degreeObjects C m where
  obj x := x
  map {x y} f := (C.enriched.Hom x y).map i f
  map_id x := (congrFun ((C.enriched.id x).naturality i) PUnit.unit).symm
  map_comp {x y z} f g := (congrFun ((C.enriched.comp x y z).naturality i) (f, g)).symm

/-- The degree functor for the original identity operator is the identity functor. -/
theorem degreeMap_id (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    degreeMap C (𝟙 n) = 𝟭 (degreeObjects C n) := by
  refine CategoryTheory.Functor.hext (F := degreeMap C (𝟙 n))
    (G := 𝟭 (degreeObjects C n)) (fun _ ↦ rfl) ?_
  intro x y f
  exact heq_of_eq (congrFun ((C.enriched.Hom x y).map_id n) f)

/-- The original composite operator induces exactly the composite degree functor. -/
theorem degreeMap_comp (C : SimplicialCat.{u, u}) {n m k : SimplexCategoryᵒᵖ}
    (i : n ⟶ m) (j : m ⟶ k) : degreeMap C (i ≫ j) = degreeMap C i ⋙ degreeMap C j := by
  refine CategoryTheory.Functor.hext (F := degreeMap C (i ≫ j))
    (G := degreeMap C i ⋙ degreeMap C j) (fun _ ↦ rfl) ?_
  intro x y f
  exact heq_of_eq (congrFun ((C.enriched.Hom x y).map_comp i j) f)

/-- An original enriched functor gives the same object and Hom map in each degree. -/
def degreeFunctor {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (n : SimplexCategoryᵒᵖ) :
    degreeObjects C n ⥤ degreeObjects D n where
  obj x := F.obj x
  map {x y} f := (F.map x y).app n f
  map_id x := congrFun (NatTrans.congr_app (F.map_id x) n) PUnit.unit
  map_comp {x y z} f g := congrFun (NatTrans.congr_app (F.map_comp x y z) n) (f, g)

/-- Every original degree functor commutes with every actual simplicial operator. -/
theorem degreeFunctor_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    degreeMap C i ⋙ degreeFunctor F m = degreeFunctor F n ⋙ degreeMap D i := by
  refine CategoryTheory.Functor.hext (F := degreeMap C i ⋙ degreeFunctor F m)
    (G := degreeFunctor F n ⋙ degreeMap D i) (fun _ ↦ rfl) ?_
  intro x y f
  exact heq_of_eq (congrFun ((F.map x y).naturality i) f)

end

end DaggerOriginalSimplicialDegreeCategory
