import ActualConstantSimplicialCategory
import ActualRigidificationSimplexHomContractibilityFormatted

/-! The original coherent nerve of a thin constant enrichment is its ordinary nerve. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualThickeningPathContractibility
open scoped Simplicial
universe u

namespace DaggerActualThinConstantCoherentNerve
noncomputable section
variable (A : Type u) [Category.{u} A] [Quiver.IsThin A]

local instance : EnrichedCategory SSet.{u} A := DaggerUnitaryDiscrete.ordinaryEnriched A

local instance (a b : A) (q : SimplexCategoryᵒᵖ) :
    Subsingleton ((a ⟶[SSet.{u}] b).obj q) := by
  change Subsingleton (a ⟶ b)
  infer_instance

/-- Evaluate the actual enriched simplex on the shortest path of every ordered pair. -/
def toOrdinary (n : SimplexCategory) (F : cosimplicialThickening.obj n ⟶ constant A) :
    Fin (n.len + 1) ⥤ A where
  obj i := F.obj ⟨⟨i⟩⟩
  map {i j} f := (F.map ⟨⟨i⟩⟩ ⟨⟨j⟩⟩).app (op ⦋0⦌)
    ((CategoryTheory.Functor.const (Fin 1)).obj
      (shortestPath (⟨i⟩ : ULift.{u} (Fin (n.len + 1))) ⟨j⟩
        (show i ≤ j from leOfHom f)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- An ordinary simplex supplies every actual enriched Hom simplex by its endpoint order. -/
def fromOrdinary (n : SimplexCategory) (F : Fin (n.len + 1) ⥤ A) :
    cosimplicialThickening.obj n ⟶ constant A where
  obj i := F.obj i.as.down
  map i j :=
    { app := fun _ γ ↦ F.map (homOfLE (show i.as.down ≤ j.as.down from
        @CategoryTheory.SimplicialThickening.Path.le
          (ULift.{u} (Fin (n.len + 1))) _ i.as j.as (γ.obj 0)))
      naturality := by intros; funext γ; exact Subsingleton.elim _ _ }
  map_id _ := by ext q p; exact Subsingleton.elim _ _
  map_comp _ _ _ := by ext q p; exact Subsingleton.elim _ _

/-- The ordinary composite retains the entire original functor. -/
theorem to_from (n : SimplexCategory) (F : Fin (n.len + 1) ⥤ A) :
    toOrdinary A n (fromOrdinary A n F) = F := by
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro x y f
  exact heq_of_eq (Subsingleton.elim _ _)

/-- The enriched composite retains every original Hom map in every degree. -/
theorem from_to (n : SimplexCategory) (F : cosimplicialThickening.obj n ⟶ constant A) :
    fromOrdinary A n (toOrdinary A n F) = F := by
  apply EnrichedFunctor.ext SSet (fun i ↦ by cases i; rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  ext q γ
  exact Subsingleton.elim _ _

/-- The comparison keeps all objects of the actual coherent simplex. -/
def comparison : coherentNerve.obj (constant A) ⟶ nerve A where
  app q p := toOrdinary A q.unop p.down
  naturality {q r} α := by
    funext p
    refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
    intro x y f
    exact heq_of_eq (Subsingleton.elim _ _)

/-- The inverse reconstructs the whole actual coherent simplex on every ordinary simplex. -/
def inverse : nerve A ⟶ coherentNerve.obj (constant A) where
  app q p := ⟨fromOrdinary A q.unop p⟩
  naturality {q r} α := by
    funext p
    apply ULift.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro i j
    simp only [eqToHom_refl, Category.comp_id]

/-- The literal original coherent nerve is isomorphic to the ordinary nerve of the thin category. -/
def coherentNerveIso : coherentNerve.obj (constant A) ≅ nerve A where
  hom := comparison A
  inv := inverse A
  hom_inv_id := by
    apply NatTrans.ext
    funext q p
    apply ULift.ext
    exact from_to A q.unop p.down
  inv_hom_id := by
    apply NatTrans.ext
    funext q p
    exact to_from A q.unop p

/-- The constant enriched finite ordinal has the original standard simplex as its coherent nerve. -/
def ordinalNerveIso (n : ℕ) :
    coherentNerve.obj (constant (ULift.{u} (Fin (n + 1)))) ≅ (Δ[n] : SSet.{u}) :=
  coherentNerveIso (ULift.{u} (Fin (n + 1))) ≪≫ (SSet.stdSimplex.isoNerve.{u} n).symm

end
end DaggerActualThinConstantCoherentNerve
