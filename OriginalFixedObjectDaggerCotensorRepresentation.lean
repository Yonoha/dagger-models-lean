import OriginalFixedObjectCotensorRepresentation
import OriginalFixedObjectDaggerSimplicialEnrichment

/-!
# Exact representation of the original fixed-object dagger cotensor

Use the ordinary internal-Hom equivalence on every original Hom simplicial set.
The same full parameter families preserve the original dagger in all degrees.
Both inverse constructions retain all maps and the same fixed object type O.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectDegreeCategories DaggerOriginalFixedObjectDaggerDegreeCategories
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectDaggerSimplicialEnrichment
universe u

namespace DaggerOriginalFixedObjectDaggerCotensorRepresentation

noncomputable section

/-- Forget the dagger in the full parameter family, retaining all degree Hom functions. -/
def underlyingFamily {O : Type u} {C D : FixedDaggerCategory O} {K : SSet.{u}}
    (F : Functor.HomObj (degreewiseObj C) (degreewiseObj D) K) :
    Functor.HomObj
      (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj C.underlying)
      (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj D.underlying) K where
  app n k := (F.app n k).underlying
  naturality i k := congrArg DegreeDaggerHom.underlying (F.naturality i k)

/-- Curry the same full family and prove preservation of the original dagger. -/
def familyToCotensor {O : Type u} {C D : FixedDaggerCategory O} {K : SSet.{u}}
    (F : Functor.HomObj (degreewiseObj C) (degreewiseObj D) K) :
    C ⟶ daggerCotensor K D where
  underlying := DaggerOriginalFixedObjectCotensorRepresentation.familyToCotensor
    (underlyingFamily F)
  map_dagger x y := by
    apply NatTrans.ext
    funext n f
    apply Functor.HomObj.ext
    funext m i k
    change (D.dagger.dagger x y).app m
      ((F.app m k).underlying.map x y ((C.underlying.enriched.Hom x y).map i f)) =
        (F.app m k).underlying.map y x
          ((C.underlying.enriched.Hom y x).map i ((C.dagger.dagger x y).app n f))
    have h := (congrFun ((C.dagger.dagger x y).naturality i) f).symm
    change (C.underlying.enriched.Hom y x).map i ((C.dagger.dagger x y).app n f) =
      (C.dagger.dagger x y).app m ((C.underlying.enriched.Hom x y).map i f) at h
    rw [h]
    exact ((F.app m k).map_dagger x y _).symm

/-- Uncurry the original dagger functor into the full parameter family. -/
def familyOfCotensor {O : Type u} {C D : FixedDaggerCategory O} {K : SSet.{u}}
    (F : C ⟶ daggerCotensor K D) :
    Functor.HomObj (degreewiseObj C) (degreewiseObj D) K where
  app n k :=
    { underlying :=
        (DaggerOriginalFixedObjectCotensorRepresentation.familyOfCotensor F.underlying).app n k
      map_dagger x y f := by
        have h := congrFun (NatTrans.congr_app (F.map_dagger x y) n) f
        have hp := congrFun (Functor.HomObj.congr_app h n (𝟙 n)) k
        exact hp.symm }
  naturality i k := degreeDaggerHom_ext
    ((DaggerOriginalFixedObjectCotensorRepresentation.familyOfCotensor F.underlying).naturality
      i k)

/-- The full original dagger functor is recovered, including its exact underlying Hom maps. -/
theorem familyToCotensor_familyOfCotensor {O : Type u} {C D : FixedDaggerCategory O}
    {K : SSet.{u}} (F : C ⟶ daggerCotensor K D) :
    familyToCotensor (familyOfCotensor F) = F := by
  apply fixedDaggerHom_ext
  exact DaggerOriginalFixedObjectCotensorRepresentation.familyToCotensor_familyOfCotensor
    F.underlying

/-- The entire degreewise dagger family is recovered at every parameter simplex. -/
theorem familyOfCotensor_familyToCotensor {O : Type u} {C D : FixedDaggerCategory O}
    {K : SSet.{u}} (F : Functor.HomObj (degreewiseObj C) (degreewiseObj D) K) :
    familyOfCotensor (familyToCotensor F) = F := by
  apply Functor.HomObj.ext
  funext n k
  apply degreeDaggerHom_ext
  apply degreeHom_ext
  intro x y f
  change (F.app n k).underlying.map x y
    ((C.underlying.enriched.Hom x y).map (𝟙 n) f) = (F.app n k).underlying.map x y f
  rw [(C.underlying.enriched.Hom x y).map_id]
  rfl

/-- The full dagger parameter families correspond to actual dagger cotensor functors. -/
def familyEquiv {O : Type u} (C D : FixedDaggerCategory O) (K : SSet.{u}) :
    Functor.HomObj (degreewiseObj C) (degreewiseObj D) K ≃ (C ⟶ daggerCotensor K D) where
  toFun := familyToCotensor
  invFun := familyOfCotensor
  left_inv := familyOfCotensor_familyToCotensor
  right_inv := familyToCotensor_familyOfCotensor

/-- The actual dagger cotensor represents Mathlib's full original dagger mapping object. -/
def cotensorHomEquiv {O : Type u} (C D : FixedDaggerCategory O) (K : SSet.{u}) :
    (K ⟶ mapping C D) ≃ (C ⟶ daggerCotensor K D) :=
  (parameterEquiv C D K).trans (familyEquiv C D K)

/-- Parameter restriction preserves the whole original dagger cotensor correspondence. -/
theorem familyToCotensor_parameter {O : Type u} {C D : FixedDaggerCategory O}
    {K L : SSet.{u}} (i : K ⟶ L)
    (F : Functor.HomObj (degreewiseObj C) (degreewiseObj D) L) :
    familyToCotensor (Functor.HomObj.map i F) =
      familyToCotensor F ≫ daggerCotensorPre i D := by
  apply fixedDaggerHom_ext
  exact DaggerOriginalFixedObjectCotensorRepresentation.familyToCotensor_parameter i
    (underlyingFamily F)

/-- The exact full dagger representing equivalence is natural in every parameter map. -/
theorem cotensorHomEquiv_parameter {O : Type u} (C D : FixedDaggerCategory O)
    {K L : SSet.{u}} (i : K ⟶ L) (F : L ⟶ mapping C D) :
    cotensorHomEquiv C D K (i ≫ F) =
      cotensorHomEquiv C D L F ≫ daggerCotensorPre i D := by
  change familyToCotensor (parameterEquiv C D K (i ≫ F)) = _
  rw [parameterEquiv_parameter]
  exact familyToCotensor_parameter i _

end

end DaggerOriginalFixedObjectDaggerCotensorRepresentation
