import OriginalFixedObjectDaggerCotensorRepresentation

/-!
# Constants and evaluation on the original fixed-object cotensor

For every simplicial parameter K, constants and evaluation at a global point
are actual fixed-object enriched functors. They retain all original identities,
compositions and daggers. The same arrows restrict to strict groupoids without
any model-structure hypothesis.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
universe u

namespace DaggerOriginalFixedObjectCotensorPoints

noncomputable section

/-- Evaluate the native internal Hom at the same global point in every degree. -/
def pointEvaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) (X : SSet.{u}) :
    (ihom K).obj X ⟶ X where
  app n f := f.app n (𝟙 n) (a.app n PUnit.unit)
  naturality n m i := by
    funext f
    have h := congrFun (f.naturality i (𝟙 n)) (a.app n PUnit.unit)
    have ha := congrFun (a.naturality i) PUnit.unit
    change a.app m PUnit.unit = K.map i (a.app n PUnit.unit) at ha
    change f.app m (𝟙 n ≫ i) (K.map i (a.app n PUnit.unit)) =
      X.map i (f.app n (𝟙 n) (a.app n PUnit.unit)) at h
    change f.app m (i ≫ 𝟙 m) (a.app m PUnit.unit) =
      X.map i (f.app n (𝟙 n) (a.app n PUnit.unit))
    simpa only [Category.id_comp, Category.comp_id, ← ha] using h

/-- The native constant Hom map is currying the original projection to X. -/
def constantHom (K X : SSet.{u}) : X ⟶ (ihom K).obj X :=
  curry (CartesianMonoidalCategory.snd K X)

/-- Evaluating a native constant Hom map gives the full simplicial identity. -/
theorem constantHom_evaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) (X : SSet.{u}) :
    constantHom K X ≫ pointEvaluation a X = 𝟙 X := by
  apply NatTrans.ext
  funext n f
  change X.map (𝟙 n) f = f
  rw [X.map_id]
  rfl

/-- Internal Hom from the actual monoidal unit is identified with the whole original X. -/
theorem unitEvaluation_constantHom (X : SSet.{u}) :
    pointEvaluation (𝟙 (𝟙_ SSet.{u})) X ≫ constantHom (𝟙_ SSet.{u}) X =
      𝟙 ((ihom (𝟙_ SSet.{u})).obj X) := by
  apply NatTrans.ext
  funext n f
  apply Functor.HomObj.ext
  funext m i k
  cases k
  have h := congrFun (f.naturality i (𝟙 n)) PUnit.unit
  change f.app m (𝟙 n ≫ i) PUnit.unit = X.map i (f.app n (𝟙 n) PUnit.unit) at h
  simpa only [Category.id_comp] using h.symm

/-- Native unit evaluation is an actual isomorphism, not just a degree-zero bijection. -/
instance unitEvaluation_isIso (X : SSet.{u}) :
    IsIso (pointEvaluation (𝟙 (𝟙_ SSet.{u})) X) :=
  ⟨⟨constantHom (𝟙_ SSet.{u}) X, unitEvaluation_constantHom X,
    constantHom_evaluation (𝟙 (𝟙_ SSet.{u})) X⟩⟩

/-- Every global point is a native simplicial monomorphism. -/
instance globalPoint_mono {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) : Mono a := by
  apply (NatTrans.mono_iff_mono_app a).2
  intro n
  apply (CategoryTheory.mono_iff_injective (a.app n)).2
  intro p q _
  exact @Subsingleton.elim PUnit.{u + 1} _ p q

/-- Evaluation commutes with every simplicial map on the original Hom object. -/
theorem pointEvaluation_natural {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ihom K).map f ≫ pointEvaluation a Y = pointEvaluation a X ≫ f := by
  apply NatTrans.ext
  funext n g
  rfl

/-- Evaluation commutes with arbitrary restriction of the simplicial parameter. -/
theorem pointEvaluation_parameter {K L : SSet.{u}} (i : K ⟶ L)
    (a : 𝟙_ SSet.{u} ⟶ K) (X : SSet.{u}) :
    (MonoidalClosed.pre i).app X ≫ pointEvaluation a X = pointEvaluation (a ≫ i) X := by
  apply NatTrans.ext
  funext n g
  rfl

/-- The constant functor is the currying of the actual degreewise identity family. -/
def constant (K : SSet.{u}) {O : Type u} (C : FixedSimplicialCategory O) :
    C ⟶ cotensor K C :=
  DaggerOriginalFixedObjectCotensorRepresentation.familyToCotensor
    (Functor.HomObj.id (F := DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj C) K)

/-- A constant arrow at any parameter is the original arrow under the same operator. -/
theorem constant_app (K : SSet.{u}) {O : Type u} (C : FixedSimplicialCategory O) (x y : O)
    (n m : SimplexCategoryᵒᵖ) (i : n ⟶ m) (f : (C.enriched.Hom x y).obj n) (k : K.obj m) :
    (((constant K C).map x y).app n f).app m i k = (C.enriched.Hom x y).map i f := rfl

/-- The original constant functor uses exactly the native constant Hom map. -/
theorem constant_map (K : SSet.{u}) {O : Type u} (C : FixedSimplicialCategory O) (x y : O) :
    (constant K C).map x y = constantHom K (C.enriched.Hom x y) := rfl

/-- Point evaluation preserves the full original fixed-object enrichment. -/
def evaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u}
    (C : FixedSimplicialCategory O) : cotensor K C ⟶ C where
  map x y := pointEvaluation a (C.enriched.Hom x y)
  map_id x := by
    apply NatTrans.ext
    funext n p
    cases p
    exact cotensor_point_id K C x n n (𝟙 n) (a.app n PUnit.unit)
  map_comp x y z := by
    apply NatTrans.ext
    funext n f
    exact cotensor_point_comp K C x y z n n (𝟙 n) f.1 f.2 (a.app n PUnit.unit)

/-- Constants followed by point evaluation recover the entire original functor. -/
theorem constant_evaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u}
    (C : FixedSimplicialCategory O) : constant K C ≫ evaluation a C = 𝟙 C := by
  apply fixedHom_ext
  intro x y
  apply NatTrans.ext
  funext n f
  change (C.enriched.Hom x y).map (𝟙 n) f = f
  rw [(C.enriched.Hom x y).map_id]
  rfl

/-- Point evaluation is natural for every original fixed-object functor. -/
theorem evaluation_natural {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u}
    {C D : FixedSimplicialCategory O} (F : C ⟶ D) :
    cotensorMap K F ≫ evaluation a D = evaluation a C ≫ F := by
  apply fixedHom_ext
  intro x y
  apply NatTrans.ext
  funext n f
  rfl

/-- Constants are natural for every original fixed-object functor. -/
theorem constant_natural (K : SSet.{u}) {O : Type u} {C D : FixedSimplicialCategory O}
    (F : C ⟶ D) : F ≫ constant K D = constant K C ≫ cotensorMap K F := by
  apply fixedHom_ext
  intro x y
  apply NatTrans.ext
  funext n f
  apply Functor.HomObj.ext
  funext m i k
  exact (congrFun ((F.map x y).naturality i) f).symm

/-- Restricting a parameter and evaluating is evaluation at the induced global point. -/
theorem evaluation_parameter {K L : SSet.{u}} (i : K ⟶ L)
    (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u} (C : FixedSimplicialCategory O) :
    cotensorPre i C ≫ evaluation a C = evaluation (a ≫ i) C := by
  apply fixedHom_ext
  intro x y
  apply NatTrans.ext
  funext n f
  rfl

/-- The constant original dagger functor is the same full identity family. -/
def daggerConstant (K : SSet.{u}) {O : Type u} (C : FixedDaggerCategory O) :
    C ⟶ daggerCotensor K C :=
  DaggerOriginalFixedObjectDaggerCotensorRepresentation.familyToCotensor
    (Functor.HomObj.id
      (F := DaggerOriginalFixedObjectDaggerSimplicialEnrichment.degreewiseObj C) K)

/-- Dagger constants retain exactly the ordinary constant Hom maps. -/
theorem daggerConstant_underlying (K : SSet.{u}) {O : Type u} (C : FixedDaggerCategory O) :
    (daggerConstant K C).underlying = constant K C.underlying := rfl

/-- Point evaluation also preserves the transported original dagger. -/
def daggerEvaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u}
    (C : FixedDaggerCategory O) : daggerCotensor K C ⟶ C where
  underlying := evaluation a C.underlying
  map_dagger x y := by
    apply NatTrans.ext
    funext n f
    rfl

/-- The entire original dagger identity is recovered by evaluating constants. -/
theorem daggerConstant_evaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u}
    (C : FixedDaggerCategory O) : daggerConstant K C ≫ daggerEvaluation a C = 𝟙 C := by
  apply fixedDaggerHom_ext
  exact constant_evaluation a C.underlying

/-- Constants are natural for every original dagger functor. -/
theorem daggerConstant_natural (K : SSet.{u}) {O : Type u} {C D : FixedDaggerCategory O}
    (F : C ⟶ D) : F ≫ daggerConstant K D = daggerConstant K C ≫ daggerCotensorMap K F := by
  apply fixedDaggerHom_ext
  exact constant_natural K F.underlying

/-- Evaluation is natural for every original dagger functor. -/
theorem daggerEvaluation_natural {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u}
    {C D : FixedDaggerCategory O} (F : C ⟶ D) :
    daggerCotensorMap K F ≫ daggerEvaluation a D = daggerEvaluation a C ≫ F := by
  apply fixedDaggerHom_ext
  exact evaluation_natural a F.underlying

/-- Dagger evaluation commutes with every original parameter restriction. -/
theorem daggerEvaluation_parameter {K L : SSet.{u}} (i : K ⟶ L)
    (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u} (C : FixedDaggerCategory O) :
    daggerCotensorPre i C ≫ daggerEvaluation a C = daggerEvaluation (a ≫ i) C := by
  apply fixedDaggerHom_ext
  exact evaluation_parameter i a C.underlying

/-- Constants on the original strict groupoids use the same original enriched arrows. -/
def strictConstant (K : SSet.{u}) {O : Type u} (C : FixedStrictGroupoids O) :
    C ⟶ strictCotensor K C := ObjectProperty.homMk (constant K C.obj)

/-- Evaluation on strict groupoids uses the same original point-evaluation Hom maps. -/
def strictEvaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u}
    (C : FixedStrictGroupoids O) : strictCotensor K C ⟶ C :=
  ObjectProperty.homMk (evaluation a C.obj)

/-- The split identity holds in the actual fixed-object strict groupoid category. -/
theorem strictConstant_evaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u}
    (C : FixedStrictGroupoids O) : strictConstant K C ≫ strictEvaluation a C = 𝟙 C :=
  ObjectProperty.hom_ext _ (constant_evaluation a C.obj)

/-- Dagger constants on strict groupoids retain the original transported dagger. -/
def strictDaggerConstant (K : SSet.{u}) {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    C ⟶ strictDaggerCotensor K C := ObjectProperty.homMk (daggerConstant K C.obj)

/-- Dagger point evaluation is an actual arrow of the same fixed-object strict category. -/
def strictDaggerEvaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u}
    (C : FixedStrictDaggerGroupoids O) : strictDaggerCotensor K C ⟶ C :=
  ObjectProperty.homMk (daggerEvaluation a C.obj)

/-- The full split identity also holds for the original strict dagger groupoids. -/
theorem strictDaggerConstant_evaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) {O : Type u}
    (C : FixedStrictDaggerGroupoids O) :
    strictDaggerConstant K C ≫ strictDaggerEvaluation a C = 𝟙 C :=
  ObjectProperty.hom_ext _ (daggerConstant_evaluation a C.obj)

end

end DaggerOriginalFixedObjectCotensorPoints
