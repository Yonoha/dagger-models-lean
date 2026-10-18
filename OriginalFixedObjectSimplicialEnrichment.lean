import OriginalFixedObjectDegreeCategories

/-!
# The full Mathlib simplicial enrichment of the original fixed-object category

The functor into simplicial objects retains all original degrees and operators.
Every natural transformation assembles to the same original enriched functor.
The proved fully faithful inverse transfers Mathlib's complete enrichment and
ordinary-Hom correspondence, without an essential-surjectivity hypothesis.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDegreeCategories
universe u

namespace DaggerOriginalFixedObjectSimplicialEnrichment

noncomputable section

/-- Every degree is exactly the original category structure on the same O. -/
def degreewiseObj {O : Type u} (C : FixedSimplicialCategory O) :
    SimplicialObject (DegreeCategory O) where
  obj n := ⟨degreeCategory (original O C) n⟩
  map i :=
    { map x y := (C.enriched.Hom x y).map i
      map_id x := (congrFun ((C.enriched.id x).naturality i) PUnit.unit).symm
      map_comp x y z f g := (congrFun ((C.enriched.comp x y z).naturality i) (f, g)).symm }
  map_id n := degreeHom_ext (fun x y f ↦ congrFun ((C.enriched.Hom x y).map_id n) f)
  map_comp i j := degreeHom_ext
    (fun x y f ↦ congrFun ((C.enriched.Hom x y).map_comp i j) f)

/-- The same original fixed functor in every degree, with all operator naturality. -/
def degreewiseMap {O : Type u} {C D : FixedSimplicialCategory O} (F : C ⟶ D) :
    degreewiseObj C ⟶ degreewiseObj D where
  app n :=
    { map x y := (F.map x y).app n
      map_id x := congrFun (NatTrans.congr_app (F.map_id x) n) PUnit.unit
      map_comp x y z f g := congrFun (NatTrans.congr_app (F.map_comp x y z) n) (f, g) }
  naturality _ _ i := degreeHom_ext (fun x y f ↦ congrFun ((F.map x y).naturality i) f)

/-- The actual degreewise functor, on all original identity-object-function arrows. -/
def degreewise (O : Type u) : FixedSimplicialCategory O ⥤ SimplicialObject (DegreeCategory O)
    where
  obj := degreewiseObj
  map := degreewiseMap
  map_id C := by
    apply NatTrans.ext
    funext n
    exact degreeHom_ext (fun _ _ _ ↦ rfl)
  map_comp F G := by
    apply NatTrans.ext
    funext n
    exact degreeHom_ext (fun _ _ _ ↦ rfl)

/-- Assemble all degree Hom functions to the exact original enriched functor. -/
def assembled {O : Type u} {C D : FixedSimplicialCategory O}
    (F : degreewiseObj C ⟶ degreewiseObj D) : C ⟶ D where
  map x y :=
    { app n := (F.app n).map x y
      naturality _ _ i := by
        funext f
        exact congrArg (fun h ↦ h.map x y f) (F.naturality i) }
  map_id x := by
    apply NatTrans.ext
    funext n f
    cases f
    exact (F.app n).map_id x
  map_comp x y z := by
    apply NatTrans.ext
    funext n f
    exact (F.app n).map_comp x y z f.1 f.2

/-- Reassembly preserves the entire original natural transformation. -/
theorem degreewiseMap_assembled {O : Type u} {C D : FixedSimplicialCategory O}
    (F : degreewiseObj C ⟶ degreewiseObj D) : degreewiseMap (assembled F) = F := by
  apply NatTrans.ext
  funext n
  exact degreeHom_ext (fun _ _ _ ↦ rfl)

/-- The inverse reconstruction preserves the complete original enriched functor. -/
theorem assembled_degreewiseMap {O : Type u} {C D : FixedSimplicialCategory O} (F : C ⟶ D) :
    assembled (degreewiseMap F) = F := by
  apply fixedHom_ext
  intro x y
  apply NatTrans.ext
  funext n f
  rfl

/-- Full faithfulness is proved on every original Hom, not assumed. -/
def fullyFaithful (O : Type u) : (degreewise O).FullyFaithful where
  preimage := assembled
  map_preimage := degreewiseMap_assembled
  preimage_map := assembled_degreewiseMap

/-- The exact Mathlib mapping object of the original degreewise categories. -/
def mapping {O : Type u} (C D : FixedSimplicialCategory O) : SSet.{u} :=
  (degreewiseObj C).functorHom (degreewiseObj D)

/-- All enrichment laws are the existing Mathlib functor-category laws. -/
instance enriched (O : Type u) : EnrichedCategory SSet.{u} (FixedSimplicialCategory O) where
  Hom := mapping
  id C := eId SSet (degreewiseObj C)
  comp C D E := eComp SSet (degreewiseObj C) (degreewiseObj D) (degreewiseObj E)
  id_comp C D := e_id_comp SSet (degreewiseObj C) (degreewiseObj D)
  comp_id C D := e_comp_id SSet (degreewiseObj C) (degreewiseObj D)
  assoc B C D E := e_assoc SSet (degreewiseObj B) (degreewiseObj C)
    (degreewiseObj D) (degreewiseObj E)

/-- The complete original ordinary-Hom equivalence, retaining both inverses. -/
def homEquiv {O : Type u} {C D : FixedSimplicialCategory O} :
    (C ⟶ D) ≃ (𝟙_ SSet.{u} ⟶ mapping C D) :=
  (fullyFaithful O).homEquiv.trans (eHomEquiv SSet)

/-- The same original ordinary category, now with its full simplicial enrichment. -/
instance simplicial (O : Type u) : SimplicialCategory (FixedSimplicialCategory O) where
  toEnrichedCategory := enriched O
  homEquiv := homEquiv
  homEquiv_id C := by
    change (eHomEquiv SSet) ((degreewise O).map (𝟙 C)) = _
    rw [CategoryTheory.Functor.map_id, eHomEquiv_id]
    rfl
  homEquiv_comp F G := by
    change (eHomEquiv SSet) ((degreewise O).map (F ≫ G)) = _
    rw [CategoryTheory.Functor.map_comp, eHomEquiv_comp]
    rfl

/-- The full parameter family equivalence is Mathlib's existing functor-Hom equivalence. -/
def parameterEquiv {O : Type u} (C D : FixedSimplicialCategory O) (K : SSet.{u}) :
    (K ⟶ mapping C D) ≃ Functor.HomObj (degreewiseObj C) (degreewiseObj D) K :=
  Functor.functorHomEquiv (degreewiseObj C) (degreewiseObj D) K

/-- Every parameter value has precisely the original degree Hom functions on O. -/
theorem parameterEquiv_app {O : Type u} (C D : FixedSimplicialCategory O) (K : SSet.{u})
    (F : K ⟶ mapping C D) (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    (parameterEquiv C D K F).app n k = (F.app n k).app n (𝟙 n) := rfl

/-- Full parameter restriction is the original Mathlib family restriction. -/
theorem parameterEquiv_parameter {O : Type u} (C D : FixedSimplicialCategory O)
    {K L : SSet.{u}} (i : K ⟶ L) (F : L ⟶ mapping C D) :
    parameterEquiv C D K (i ≫ F) = Functor.HomObj.map i (parameterEquiv C D L F) := by
  apply Functor.HomObj.ext
  funext n k
  rfl

end

end DaggerOriginalFixedObjectSimplicialEnrichment
