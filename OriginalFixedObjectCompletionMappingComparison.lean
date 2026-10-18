import OriginalFixedObjectStrictGroupoidCotensors

/-!
# The original completion comparison on cotensor-presented simplicial mapping objects

Use actual fixed-object cotensors in every dimension and every simplex operator.
Their ordinary Hom sets form simplicial mapping objects. The original adjunction
gives a natural isomorphism between these objects, retaining the exact original
localization in every component. Identification with a separately bundled
enrichment and model-category derived mapping objects is a further obligation.
-/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels SSet
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction DaggerOriginalFixedObjectCotensors
open DaggerOriginalFixedObjectStrictGroupoidCotensors
universe u

namespace DaggerOriginalFixedObjectCompletionMappingComparison

noncomputable section

/-- Every original ordinary cotensor and every original simplex restriction. -/
def cotensorDiagram {O : Type u} (D : FixedSimplicialCategory O) :
    SimplexCategoryᵒᵖ ⥤ FixedSimplicialCategory O :=
  SSet.stdSimplex.{u}.op ⋙ cotensorBifunctor O ⋙
    (evaluation (FixedSimplicialCategory O) (FixedSimplicialCategory O)).obj D

/-- Every original dagger cotensor and all original dagger simplex restrictions. -/
def daggerCotensorDiagram {O : Type u} (D : FixedDaggerCategory O) :
    SimplexCategoryᵒᵖ ⥤ FixedDaggerCategory O :=
  SSet.stdSimplex.{u}.op ⋙ daggerCotensorBifunctor O ⋙
    (evaluation (FixedDaggerCategory O) (FixedDaggerCategory O)).obj D

/-- The same ordinary cotensor diagram in the exact fixed-object strict groupoid category. -/
def strictCotensorDiagram {O : Type u} (D : FixedStrictGroupoids O) :
    SimplexCategoryᵒᵖ ⥤ FixedStrictGroupoids O :=
  SSet.stdSimplex.{u}.op ⋙ strictCotensorBifunctor O ⋙
    (evaluation (FixedStrictGroupoids O) (FixedStrictGroupoids O)).obj D

/-- The full strict dagger cotensor diagram, including every simplex operator. -/
def strictDaggerCotensorDiagram {O : Type u} (D : FixedStrictDaggerGroupoids O) :
    SimplexCategoryᵒᵖ ⥤ FixedStrictDaggerGroupoids O :=
  SSet.stdSimplex.{u}.op ⋙ strictDaggerCotensorBifunctor O ⋙
    (evaluation (FixedStrictDaggerGroupoids O) (FixedStrictDaggerGroupoids O)).obj D

/-- Original fixed-object Hom sets into all cotensors form the actual mapping simplicial set. -/
def mapping {O : Type u} (C D : FixedSimplicialCategory O) : SSet.{u} :=
  cotensorDiagram D ⋙ coyoneda.obj (op C)

/-- Original fixed-object dagger Hom sets into the same dagger cotensors. -/
def daggerMapping {O : Type u} (C D : FixedDaggerCategory O) : SSet.{u} :=
  daggerCotensorDiagram D ⋙ coyoneda.obj (op C)

/-- The exact strict groupoid Hom sets into the same original cotensors. -/
def strictMapping {O : Type u} (C D : FixedStrictGroupoids O) : SSet.{u} :=
  strictCotensorDiagram D ⋙ coyoneda.obj (op C)

/-- The exact strict dagger groupoid Hom sets into the same original dagger cotensors. -/
def strictDaggerMapping {O : Type u} (C D : FixedStrictDaggerGroupoids O) : SSet.{u} :=
  strictDaggerCotensorDiagram D ⋙ coyoneda.obj (op C)

/-- The full ordinary completion universal property at any actual cotensor parameter. -/
def parameterHomEquiv {O : Type u} (K : SSet.{u}) (C : FixedSimplicialCategory O)
    (D : FixedStrictGroupoids O) :
    ((fixedCompletion O).obj C ⟶ strictCotensor K D) ≃ (C ⟶ cotensor K D.obj) :=
  fixedCompletionHomEquiv C (strictCotensor K D)

/-- The full dagger completion universal property at any actual cotensor parameter. -/
def daggerParameterHomEquiv {O : Type u} (K : SSet.{u}) (C : FixedDaggerCategory O)
    (D : FixedStrictDaggerGroupoids O) :
    ((fixedDaggerCompletion O).obj C ⟶ strictDaggerCotensor K D) ≃
      (C ⟶ daggerCotensor K D.obj) :=
  fixedDaggerCompletionHomEquiv C (strictDaggerCotensor K D)

/-- All parameter restrictions commute with the same original localization comparison. -/
theorem parameterHomEquiv_natural {O : Type u} {K L : SSet.{u}} (i : K ⟶ L)
    (C : FixedSimplicialCategory O) (D : FixedStrictGroupoids O)
    (F : (fixedCompletion O).obj C ⟶ strictCotensor L D) :
    parameterHomEquiv K C D (F ≫ ObjectProperty.homMk (cotensorPre i D.obj)) =
      parameterHomEquiv L C D F ≫ cotensorPre i D.obj :=
  (Category.assoc (fixedLocalization C) F.hom (cotensorPre i D.obj)).symm

/-- Every dagger parameter restriction retains the exact original factorization square. -/
theorem daggerParameterHomEquiv_natural {O : Type u} {K L : SSet.{u}} (i : K ⟶ L)
    (C : FixedDaggerCategory O) (D : FixedStrictDaggerGroupoids O)
    (F : (fixedDaggerCompletion O).obj C ⟶ strictDaggerCotensor L D) :
    daggerParameterHomEquiv K C D (F ≫ ObjectProperty.homMk (daggerCotensorPre i D.obj)) =
      daggerParameterHomEquiv L C D F ≫ daggerCotensorPre i D.obj :=
  (Category.assoc (fixedDaggerLocalization C) F.hom (daggerCotensorPre i D.obj)).symm

/-- The original adjunction gives an isomorphism of whole ordinary mapping simplicial sets. -/
def completionMappingIso {O : Type u} (C : FixedSimplicialCategory O)
    (D : FixedStrictGroupoids O) :
    strictMapping ((fixedCompletion O).obj C) D ≅ mapping C D.obj := by
  refine NatIso.ofComponents
    (fun n ↦ (parameterHomEquiv (SSet.stdSimplex.obj n.unop) C D).toIso) ?_
  intro n m i
  funext F
  exact parameterHomEquiv_natural (SSet.stdSimplex.map i.unop) C D F

/-- The exact dagger completion comparison is an isomorphism in every dimension and operator. -/
def daggerCompletionMappingIso {O : Type u} (C : FixedDaggerCategory O)
    (D : FixedStrictDaggerGroupoids O) :
    strictDaggerMapping ((fixedDaggerCompletion O).obj C) D ≅ daggerMapping C D.obj := by
  refine NatIso.ofComponents
    (fun n ↦ (daggerParameterHomEquiv (SSet.stdSimplex.obj n.unop) C D).toIso) ?_
  intro n m i
  funext F
  exact daggerParameterHomEquiv_natural (SSet.stdSimplex.map i.unop) C D F

/-- The same ordinary adjunction retains naturality under every original source functor. -/
theorem parameterHomEquiv_source {O : Type u} (K : SSet.{u})
    {C C' : FixedSimplicialCategory O} (D : FixedStrictGroupoids O) (F : C' ⟶ C)
    (G : (fixedCompletion O).obj C ⟶ strictCotensor K D) :
    parameterHomEquiv K C' D ((fixedCompletion O).map F ≫ G) =
      F ≫ parameterHomEquiv K C D G :=
  (fixedCompletionInclusionAdjunction O).homEquiv_naturality_left F G

/-- Every target functor retains the entire original completion comparison at every parameter. -/
theorem parameterHomEquiv_target {O : Type u} (K : SSet.{u})
    (C : FixedSimplicialCategory O) {D E : FixedStrictGroupoids O} (F : D ⟶ E)
    (G : (fixedCompletion O).obj C ⟶ strictCotensor K D) :
    parameterHomEquiv K C E (G ≫ (strictCotensorFunctor O K).map F) =
      parameterHomEquiv K C D G ≫ cotensorMap K F.hom :=
  (fixedCompletionInclusionAdjunction O).homEquiv_naturality_right G
    ((strictCotensorFunctor O K).map F)

/-- Dagger source naturality uses the same original full dagger completion map. -/
theorem daggerParameterHomEquiv_source {O : Type u} (K : SSet.{u})
    {C C' : FixedDaggerCategory O} (D : FixedStrictDaggerGroupoids O) (F : C' ⟶ C)
    (G : (fixedDaggerCompletion O).obj C ⟶ strictDaggerCotensor K D) :
    daggerParameterHomEquiv K C' D ((fixedDaggerCompletion O).map F ≫ G) =
      F ≫ daggerParameterHomEquiv K C D G :=
  (fixedDaggerCompletionInclusionAdjunction O).homEquiv_naturality_left F G

/-- Dagger target naturality retains the same transported dagger functor. -/
theorem daggerParameterHomEquiv_target {O : Type u} (K : SSet.{u})
    (C : FixedDaggerCategory O) {D E : FixedStrictDaggerGroupoids O} (F : D ⟶ E)
    (G : (fixedDaggerCompletion O).obj C ⟶ strictDaggerCotensor K D) :
    daggerParameterHomEquiv K C E (G ≫ (strictDaggerCotensorFunctor O K).map F) =
      daggerParameterHomEquiv K C D G ≫ daggerCotensorMap K F.hom :=
  (fixedDaggerCompletionInclusionAdjunction O).homEquiv_naturality_right G
    ((strictDaggerCotensorFunctor O K).map F)

end

end DaggerOriginalFixedObjectCompletionMappingComparison
