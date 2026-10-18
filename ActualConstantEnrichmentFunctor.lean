import ActualConstantCoherentNerve

/-! Constant enrichment is functorial, and its original coherent nerve comparison is natural. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualConstantCoherentSimplexComparison
open DaggerActualConstantCoherentNerve
universe u
namespace DaggerActualConstantEnrichmentFunctor
noncomputable section

section
variable {A B : Type u} [Category.{u} A] [Category.{u} B]
local instance : EnrichedCategory SSet.{u} A := DaggerUnitaryDiscrete.ordinaryEnriched A
local instance : EnrichedCategory SSet.{u} B := DaggerUnitaryDiscrete.ordinaryEnriched B

def constantMap (F : A ⥤ B) :
    constant A ⟶ constant B where
  obj := F.obj
  map x y := DaggerUnitaryDiscrete.constMap (fun f : x ⟶ y ↦ F.map f)
  map_id x := by
    ext q p
    exact F.map_id x
  map_comp x y z := by
    ext q p
    exact F.map_comp p.1 p.2

end

def constantFunctor : Cat.{u, u} ⥤ SimplicialCat.{u, u} where
  obj A := constant A
  map F := constantMap F.toFunctor
  map_id A := by
    letI := (constant A).enriched
    apply EnrichedFunctor.ext SSet
      (F := constantMap (𝟭 A)) (G := 𝟙 (constant A)) (fun _ ↦ rfl)
    intro i j
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  map_comp {A B C} F G := by
    letI := (constant A).enriched
    letI := (constant B).enriched
    letI := (constant C).enriched
    apply EnrichedFunctor.ext SSet
      (F := constantMap (F ≫ G).toFunctor)
      (G := constantMap F.toFunctor ≫ constantMap G.toFunctor) (fun _ ↦ rfl)
    intro i j
    simp only [eqToHom_refl, Category.comp_id]
    rfl

theorem inverse_naturality {A B : Type u} [Category.{u} A] [Category.{u} B]
    (F : A ⥤ B) :
    (coherentNerveIso A).inv ≫ coherentNerve.map (constantMap F) =
      nerveMap F ≫ (coherentNerveIso B).inv := by
  letI := (constant B).enriched
  apply NatTrans.ext
  funext q p
  apply ULift.ext
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

/-- Naturality holds for all ordinary categories and all original ordinary functors. -/
def constantCoherentNerveIso : constantFunctor.{u} ⋙ coherentNerve ≅ nerveFunctor :=
  NatIso.ofComponents (fun A ↦ coherentNerveIso A) (by
    intro A B F
    apply (cancel_epi ((coherentNerveIso A).inv)).mp
    change (coherentNerveIso A).inv ≫
        (coherentNerve.map (constantMap F.toFunctor) ≫ (coherentNerveIso B).hom) =
      (coherentNerveIso A).inv ≫ ((coherentNerveIso A).hom ≫ nerveMap F.toFunctor)
    rw [← Category.assoc, inverse_naturality]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc])

end
end DaggerActualConstantEnrichmentFunctor
