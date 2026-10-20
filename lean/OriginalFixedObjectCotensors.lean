import OriginalFixedObjectGroupoidCompletionAdjunction
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Internal Hom on the original fixed object categories

Reuse the chosen-product internal-Hom construction from the previously verified
fixed-category cotensor. Transport the original enrichment on exactly O and map
its original dagger by the same internal-Hom functor. Both variances retain the
original Hom maps. Strictness and cotensor representation are separate proofs.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed DaggerModels
open Functor.LaxMonoidal
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
universe u

namespace DaggerOriginalFixedObjectCotensors

noncomputable section

/-- Use Mathlib's actual finite-product-preserving right adjoint and braided structure. -/
def ihomBraided (K : SSet.{u}) : (ihom K).Braided := by
  letI : PreservesLimitsOfSize.{0, 0} (ihom K) :=
    (ihom.adjunction K).rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits (ihom K) :=
    PreservesLimitsOfSize.preservesFiniteLimits (ihom K)
  exact Functor.Braided.ofChosenFiniteProducts (ihom K)

attribute [local instance] ihomBraided

/-- Transport all original enriched category laws, retaining precisely O. -/
def cotensor (K : SSet.{u}) {O : Type u} (C : FixedSimplicialCategory O) :
    FixedSimplicialCategory O := by
  letI := C.enriched
  exact ⟨inferInstanceAs (EnrichedCategory SSet.{u} (TransportEnrichment (ihom K) O))⟩

/-- The original internal-Hom mapping object, with exactly the same endpoints. -/
theorem cotensor_hom (K : SSet.{u}) {O : Type u} (C : FixedSimplicialCategory O) (x y : O) :
    (cotensor K C).enriched.Hom x y = (ihom K).obj (C.enriched.Hom x y) := rfl

/-- The identity is the actual chosen-product internal-Hom identity. -/
theorem cotensor_id (K : SSet.{u}) {O : Type u} (C : FixedSimplicialCategory O) (x : O) :
    (cotensor K C).enriched.id x = ε (ihom K) ≫ (ihom K).map (C.enriched.id x) := rfl

/-- Composition uses the actual chosen-product comparison and original composition. -/
theorem cotensor_comp (K : SSet.{u}) {O : Type u} (C : FixedSimplicialCategory O) (x y z : O) :
    (cotensor K C).enriched.comp x y z =
      μ (ihom K) _ _ ≫ (ihom K).map (C.enriched.comp x y z) := rfl

/-- Map the exact fixed-object Hom functor with the native internal-Hom functor. -/
def cotensorMap (K : SSet.{u}) {O : Type u} {C D : FixedSimplicialCategory O} (F : C ⟶ D) :
    cotensor K C ⟶ cotensor K D where
  map x y := (ihom K).map (F.map x y)
  map_id x := by
    change (ε (ihom K) ≫ (ihom K).map (C.enriched.id x)) ≫
      (ihom K).map (F.map x x) = ε (ihom K) ≫ (ihom K).map (D.enriched.id x)
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, F.map_id x]
  map_comp x y z := by
    change (μ (ihom K) _ _ ≫ (ihom K).map (C.enriched.comp x y z)) ≫
      (ihom K).map (F.map x z) = ((ihom K).map (F.map x y) ⊗ₘ (ihom K).map (F.map y z)) ≫
        μ (ihom K) _ _ ≫ (ihom K).map (D.enriched.comp x y z)
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, F.map_comp x y z,
      CategoryTheory.Functor.map_comp,
      Functor.LaxMonoidal.μ_natural_assoc]

/-- The actual internal-Hom covariant functor retains all fixed-object arrows. -/
def cotensorFunctor (O : Type u) (K : SSet.{u}) :
    FixedSimplicialCategory O ⥤ FixedSimplicialCategory O where
  obj := cotensor K
  map := cotensorMap K
  map_id C := by
    apply fixedHom_ext
    intro x y
    exact (ihom K).map_id _
  map_comp F G := by
    apply fixedHom_ext
    intro x y
    exact (ihom K).map_comp (F.map x y) (G.map x y)

/-- Contravariance uses the native internal-Hom parameter restriction. -/
def cotensorPre {K L : SSet.{u}} (i : K ⟶ L) {O : Type u} (C : FixedSimplicialCategory O) :
    cotensor L C ⟶ cotensor K C where
  map x y := (MonoidalClosed.pre i).app (C.enriched.Hom x y)
  map_id x := by
    change (ε (ihom L) ≫ (ihom L).map _) ≫ (MonoidalClosed.pre i).app _ = _
    rw [Category.assoc, (MonoidalClosed.pre i).naturality,
      ← Category.assoc, NatTrans.IsMonoidal.unit]
    rfl
  map_comp x y z := by
    change (μ (ihom L) _ _ ≫ (ihom L).map _) ≫ (MonoidalClosed.pre i).app _ = _
    rw [Category.assoc, (MonoidalClosed.pre i).naturality,
      ← Category.assoc, NatTrans.IsMonoidal.tensor]
    rfl

/-- Original dagger is mapped by exactly the same internal-Hom functor. -/
def cotensorDaggerStructure (K : SSet.{u}) {O : Type u} (C : FixedDaggerCategory O) :
    @DaggerSimplicialStructure O (cotensor K C.underlying).enriched := by
  letI := (cotensor K C.underlying).enriched
  refine
    { dagger := fun x y ↦ (ihom K).map (C.dagger.dagger x y)
      dagger_involutive := ?_
      dagger_id := ?_
      dagger_comp := ?_ }
  · intro x y
    change (ihom K).map _ ≫ (ihom K).map _ = _
    rw [← CategoryTheory.Functor.map_comp, C.dagger.dagger_involutive,
      CategoryTheory.Functor.map_id]
    rfl
  · intro x
    change (ε (ihom K) ≫ (ihom K).map _) ≫ (ihom K).map _ = _
    rw [Category.assoc, ← Functor.map_comp, C.dagger.dagger_id]
    rfl
  · intro x y z
    change (μ (ihom K) _ _ ≫ (ihom K).map _) ≫ (ihom K).map _ =
      ((ihom K).map _ ⊗ₘ (ihom K).map _) ≫ (β_ _ _).hom ≫
        μ (ihom K) _ _ ≫ (ihom K).map _
    rw [Category.assoc, ← Functor.map_comp, C.dagger.dagger_comp,
      Functor.map_comp, Functor.map_comp]
    rw [← Functor.LaxMonoidal.μ_natural_assoc, Functor.LaxBraided.braided_assoc]

/-- The same fixed-object cotensor with its actual transported dagger. -/
def daggerCotensor (K : SSet.{u}) {O : Type u} (C : FixedDaggerCategory O) :
    FixedDaggerCategory O := ⟨cotensor K C.underlying, cotensorDaggerStructure K C⟩

/-- All original dagger functors remain dagger functors after internal Hom. -/
def daggerCotensorMap (K : SSet.{u}) {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) :
    daggerCotensor K C ⟶ daggerCotensor K D where
  underlying := cotensorMap K F.underlying
  map_dagger x y := by
    change (ihom K).map _ ≫ (ihom K).map _ = (ihom K).map _ ≫ (ihom K).map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (ihom K).map (F.map_dagger x y)

/-- Parameter restriction preserves exactly the original transported dagger. -/
def daggerCotensorPre {K L : SSet.{u}} (i : K ⟶ L) {O : Type u} (C : FixedDaggerCategory O) :
    daggerCotensor L C ⟶ daggerCotensor K C where
  underlying := cotensorPre i C.underlying
  map_dagger x y := by
    change (MonoidalClosed.pre i).app _ ≫ (ihom K).map _ =
      (ihom L).map _ ≫ (MonoidalClosed.pre i).app _
    exact ((MonoidalClosed.pre i).naturality (C.dagger.dagger x y)).symm

/-- The complete dagger covariant functor has the exact ordinary internal-Hom maps. -/
def daggerCotensorFunctor (O : Type u) (K : SSet.{u}) :
    FixedDaggerCategory O ⥤ FixedDaggerCategory O where
  obj := daggerCotensor K
  map := daggerCotensorMap K
  map_id C := fixedDaggerHom_ext ((cotensorFunctor O K).map_id C.underlying)
  map_comp F G := fixedDaggerHom_ext ((cotensorFunctor O K).map_comp F.underlying G.underlying)

/-- Native parameter identity gives the exact fixed-object identity. -/
theorem cotensorPre_id {O : Type u} (K : SSet.{u}) (C : FixedSimplicialCategory O) :
    cotensorPre (𝟙 K) C = 𝟙 (cotensor K C) := by
  apply fixedHom_ext
  intro x y
  change (MonoidalClosed.pre (𝟙 K)).app (C.enriched.Hom x y) = 𝟙 _
  rw [MonoidalClosed.pre_id]
  rfl

/-- Native parameter composition gives the exact contravariant fixed-object composite. -/
theorem cotensorPre_comp {O : Type u} {K L M : SSet.{u}} (i : K ⟶ L) (j : L ⟶ M)
    (C : FixedSimplicialCategory O) :
    cotensorPre (i ≫ j) C = cotensorPre j C ≫ cotensorPre i C := by
  apply fixedHom_ext
  intro x y
  change (MonoidalClosed.pre (i ≫ j)).app _ = _ ≫ _
  rw [MonoidalClosed.pre_map]
  rfl

/-- The actual original Hom maps satisfy the full mixed naturality square. -/
theorem cotensorPre_map {O : Type u} {K L : SSet.{u}} (i : K ⟶ L)
    {C D : FixedSimplicialCategory O} (F : C ⟶ D) :
    cotensorMap L F ≫ cotensorPre i D = cotensorPre i C ≫ cotensorMap K F := by
  apply fixedHom_ext
  intro x y
  exact ((MonoidalClosed.pre i).naturality (F.map x y))

/-- The full original dagger naturality follows from the same ordinary Hom square. -/
theorem daggerCotensorPre_map {O : Type u} {K L : SSet.{u}} (i : K ⟶ L)
    {C D : FixedDaggerCategory O} (F : C ⟶ D) :
    daggerCotensorMap L F ≫ daggerCotensorPre i D =
      daggerCotensorPre i C ≫ daggerCotensorMap K F :=
  fixedDaggerHom_ext (cotensorPre_map i F.underlying)

/-- The same ordinary bifunctor, with both original variances and exact Hom data. -/
def cotensorBifunctor (O : Type u) :
    SSet.{u}ᵒᵖ ⥤ FixedSimplicialCategory O ⥤ FixedSimplicialCategory O where
  obj K := cotensorFunctor O K.unop
  map i := { app C := cotensorPre i.unop C, naturality _ _ F := cotensorPre_map i.unop F }
  map_id K := by ext C; exact cotensorPre_id K.unop C
  map_comp i j := by ext C; exact cotensorPre_comp j.unop i.unop C

/-- The same dagger bifunctor, on the exact fixed-object dagger category. -/
def daggerCotensorBifunctor (O : Type u) :
    SSet.{u}ᵒᵖ ⥤ FixedDaggerCategory O ⥤ FixedDaggerCategory O where
  obj K := daggerCotensorFunctor O K.unop
  map i := { app C := daggerCotensorPre i.unop C,
             naturality _ _ F := daggerCotensorPre_map i.unop F }
  map_id K := by ext C; exact fixedDaggerHom_ext (cotensorPre_id K.unop C.underlying)
  map_comp i j := by
    ext C
    exact fixedDaggerHom_ext (cotensorPre_comp j.unop i.unop C.underlying)

end

end DaggerOriginalFixedObjectCotensors
