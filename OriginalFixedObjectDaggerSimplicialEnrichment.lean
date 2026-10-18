import OriginalFixedObjectDaggerDegreeCategories
import OriginalFixedObjectSimplicialEnrichment

/-!
# Full original fixed-object dagger simplicial enrichment

Retain the exact original degreewise dagger and all original identity-object
dagger functors. Prove the inverse assembly for every natural transformation,
then reuse the full Mathlib enrichment of simplicial objects, including all
unit, associativity and original ordinary-Hom correspondence laws.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectDegreeCategories DaggerOriginalFixedObjectDaggerDegreeCategories
universe u

namespace DaggerOriginalFixedObjectDaggerSimplicialEnrichment

noncomputable section

/-- The original dagger and all its original laws in precisely degree n on O. -/
def daggerDegree {O : Type u} (C : FixedDaggerCategory O) (n : SimplexCategoryᵒᵖ) :
    DegreeDaggerCategory O where
  underlying := (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj C.underlying).obj n
  dagger x y := (C.dagger.dagger x y).app n
  involutive x y f := congrFun (NatTrans.congr_app (C.dagger.dagger_involutive x y) n) f
  identity x := congrFun (NatTrans.congr_app (C.dagger.dagger_id x) n) PUnit.unit
  composition x y z f g := by
    have h := congrFun (NatTrans.congr_app (C.dagger.dagger_comp x y z) n) (f, g)
    simpa only [SSet.comp_app, Function.comp_apply, SSet.tensorHom_app_apply,
      sSetBraiding_app_apply] using h

/-- Every original simplex operator preserves the exact original degree dagger. -/
def daggerDegreeMap {O : Type u} (C : FixedDaggerCategory O) {n m : SimplexCategoryᵒᵖ}
    (i : n ⟶ m) : daggerDegree C n ⟶ daggerDegree C m where
  underlying :=
    (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj C.underlying).map i
  map_dagger x y f := (congrFun ((C.dagger.dagger x y).naturality i) f).symm

/-- The complete original degreewise dagger simplicial object. -/
def degreewiseObj {O : Type u} (C : FixedDaggerCategory O) :
    SimplicialObject (DegreeDaggerCategory O) where
  obj := daggerDegree C
  map := daggerDegreeMap C
  map_id n := degreeDaggerHom_ext
    ((DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj C.underlying).map_id n)
  map_comp i j := degreeDaggerHom_ext
    ((DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj C.underlying).map_comp i j)

/-- The original fixed-object dagger functor in every degree. -/
def degreewiseMap {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) :
    degreewiseObj C ⟶ degreewiseObj D where
  app n :=
    { underlying :=
        (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseMap F.underlying).app n
      map_dagger x y f := (congrFun (NatTrans.congr_app (F.map_dagger x y) n) f).symm }
  naturality _ _ i := degreeDaggerHom_ext
    ((DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseMap F.underlying).naturality i)

/-- The unchanged original category maps into exact-O ordinary dagger simplicial objects. -/
def degreewise (O : Type u) :
    FixedDaggerCategory O ⥤ SimplicialObject (DegreeDaggerCategory O) where
  obj := degreewiseObj
  map := degreewiseMap
  map_id C := by
    apply NatTrans.ext
    funext n
    exact degreeDaggerHom_ext (degreeHom_ext (fun _ _ _ ↦ rfl))
  map_comp F G := by
    apply NatTrans.ext
    funext n
    exact degreeDaggerHom_ext (degreeHom_ext (fun _ _ _ ↦ rfl))

/-- Retain the full original underlying natural transformation in all degrees. -/
def underlyingTransformation {O : Type u} {C D : FixedDaggerCategory O}
    (F : degreewiseObj C ⟶ degreewiseObj D) :
    DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj C.underlying ⟶
      DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj D.underlying where
  app n := (F.app n).underlying
  naturality _ _ i := congrArg DegreeDaggerHom.underlying (F.naturality i)

/-- Every natural transformation reassembles to the same original full dagger functor. -/
def assembled {O : Type u} {C D : FixedDaggerCategory O}
    (F : degreewiseObj C ⟶ degreewiseObj D) : C ⟶ D where
  underlying := DaggerOriginalFixedObjectSimplicialEnrichment.assembled (underlyingTransformation F)
  map_dagger x y := by
    apply NatTrans.ext
    funext n f
    exact ((F.app n).map_dagger x y f).symm

/-- Both inverse constructions retain the complete original degreewise dagger functor. -/
theorem degreewiseMap_assembled {O : Type u} {C D : FixedDaggerCategory O}
    (F : degreewiseObj C ⟶ degreewiseObj D) : degreewiseMap (assembled F) = F := by
  apply NatTrans.ext
  funext n
  exact degreeDaggerHom_ext (degreeHom_ext (fun _ _ _ ↦ rfl))

/-- Reassembly retains the entire original enriched dagger functor. -/
theorem assembled_degreewiseMap {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) :
    assembled (degreewiseMap F) = F := by
  apply fixedDaggerHom_ext
  apply fixedHom_ext
  intro x y
  apply NatTrans.ext
  funext n f
  rfl

/-- Full faithfulness is proved for all original dagger arrows. -/
def fullyFaithful (O : Type u) : (degreewise O).FullyFaithful where
  preimage := assembled
  map_preimage := degreewiseMap_assembled
  preimage_map := assembled_degreewiseMap

/-- The actual Mathlib mapping object of the unchanged degreewise dagger categories. -/
def mapping {O : Type u} (C D : FixedDaggerCategory O) : SSet.{u} :=
  (degreewiseObj C).functorHom (degreewiseObj D)

/-- All dagger simplicial enrichment laws reuse the actual Mathlib functor-category laws. -/
instance enriched (O : Type u) : EnrichedCategory SSet.{u} (FixedDaggerCategory O) where
  Hom := mapping
  id C := eId SSet (degreewiseObj C)
  comp C D E := eComp SSet (degreewiseObj C) (degreewiseObj D) (degreewiseObj E)
  id_comp C D := e_id_comp SSet (degreewiseObj C) (degreewiseObj D)
  comp_id C D := e_comp_id SSet (degreewiseObj C) (degreewiseObj D)
  assoc B C D E := e_assoc SSet (degreewiseObj B) (degreewiseObj C)
    (degreewiseObj D) (degreewiseObj E)

/-- The full ordinary-Hom correspondence, with the same actual original dagger arrows. -/
def homEquiv {O : Type u} {C D : FixedDaggerCategory O} :
    (C ⟶ D) ≃ (𝟙_ SSet.{u} ⟶ mapping C D) :=
  (fullyFaithful O).homEquiv.trans (eHomEquiv SSet)

/-- The original fixed dagger category has Mathlib's complete simplicial-category structure. -/
instance simplicial (O : Type u) : SimplicialCategory (FixedDaggerCategory O) where
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

/-- Full K-parameter families use the unchanged Mathlib functor-Hom equivalence. -/
def parameterEquiv {O : Type u} (C D : FixedDaggerCategory O) (K : SSet.{u}) :
    (K ⟶ mapping C D) ≃ Functor.HomObj (degreewiseObj C) (degreewiseObj D) K :=
  Functor.functorHomEquiv (degreewiseObj C) (degreewiseObj D) K

/-- The exact original pointwise dagger functor at each parameter simplex. -/
theorem parameterEquiv_app {O : Type u} (C D : FixedDaggerCategory O) (K : SSet.{u})
    (F : K ⟶ mapping C D) (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    (parameterEquiv C D K F).app n k = (F.app n k).app n (𝟙 n) := rfl

/-- All original dagger parameter restrictions retain the same whole family. -/
theorem parameterEquiv_parameter {O : Type u} (C D : FixedDaggerCategory O)
    {K L : SSet.{u}} (i : K ⟶ L) (F : L ⟶ mapping C D) :
    parameterEquiv C D K (i ≫ F) = Functor.HomObj.map i (parameterEquiv C D L F) := by
  apply Functor.HomObj.ext
  funext n k
  rfl

end

end DaggerOriginalFixedObjectDaggerSimplicialEnrichment
