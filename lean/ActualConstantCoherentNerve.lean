import ActualConstantCoherentSimplexComparison

/-! The original coherent nerve of every constant enrichment is its ordinary nerve. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory
open DaggerActualConstantCoherentSimplexComparison
open scoped Simplicial
universe u
namespace DaggerActualConstantCoherentNerve
noncomputable section
variable (A : Type u) [Category.{u} A]

local instance : EnrichedCategory SSet.{u} A := DaggerUnitaryDiscrete.ordinaryEnriched A

/-- This actual simplicial map retains every ordinary coherent simplex, in every degree. -/
def inverse : nerve A ⟶ coherentNerve.obj (constant A) where
  app q p := ⟨fromOrdinary A q.unop p⟩
  naturality {q r} α := by
    funext p
    apply ULift.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro i j
    simp only [eqToHom_refl, Category.comp_id]

/-- The component inverse evaluates the entire original enriched simplex, without thinness. -/
def simplexIso (q : SimplexCategoryᵒᵖ) :
    (nerve A).obj q ≅ (coherentNerve.obj (constant A)).obj q where
  hom := (inverse A).app q
  inv p := toOrdinary A q.unop p.down
  hom_inv_id := by
    funext p
    exact to_from A q.unop p
  inv_hom_id := by
    funext p
    apply ULift.ext
    exact from_to A q.unop p.down

/-- The same original coherent nerve is naturally isomorphic to the native ordinary nerve. -/
def coherentNerveIso : coherentNerve.obj (constant A) ≅ nerve A :=
  (NatIso.ofComponents (simplexIso A) (fun α ↦ (inverse A).naturality α)).symm

theorem coherentNerveIso_inv_app (q : SimplexCategoryᵒᵖ) (p : (nerve A).obj q) :
    (coherentNerveIso A).inv.app q p = ⟨fromOrdinary A q.unop p⟩ := rfl

theorem coherentNerveIso_hom_app (q : SimplexCategoryᵒᵖ)
    (p : (coherentNerve.obj (constant A)).obj q) :
    (coherentNerveIso A).hom.app q p = toOrdinary A q.unop p.down := rfl

end
end DaggerActualConstantCoherentNerve
