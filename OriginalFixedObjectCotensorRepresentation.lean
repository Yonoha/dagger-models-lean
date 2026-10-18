import OriginalFixedObjectSimplicialEnrichment

/-!
# Exact representation of the original fixed-object cotensor

Full K-parameter families of the original degree functors are equivalent to
original enriched functors into the actual internal-Hom cotensor. Use the
native K-first internal-Hom adjunction, every original degree and every operator.
The full ordinary-Hom correspondence is derived from Mathlib's mapping object.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDegreeCategories
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalFixedObjectSimplicialEnrichment
universe u

namespace DaggerOriginalFixedObjectCotensorRepresentation

noncomputable section

/-- The native internal-Hom adjunction retains the K-first parameter order. -/
theorem curry_app {K X Y : SSet.{u}} (F : K ⊗ X ⟶ Y) (n m : SimplexCategoryᵒᵖ)
    (i : n ⟶ m) (x : X.obj n) (k : K.obj m) :
    ((curry F).app n x).app m i k = F.app m (k, X.map i x) := rfl

/-- Native uncurrying evaluates the same degree and the literal identity operator. -/
theorem uncurry_app {K X Y : SSet.{u}} (F : X ⟶ (ihom K).obj Y) (n : SimplexCategoryᵒᵖ)
    (x : X.obj n) (k : K.obj n) :
    (uncurry F).app n (k, x) = (F.app n x).app n (𝟙 n) k := rfl

/-- A full original parameter family gives the actual K-first original Hom map. -/
def familyHom {O : Type u} {C D : FixedSimplicialCategory O} {K : SSet.{u}}
    (F : Functor.HomObj (degreewiseObj C) (degreewiseObj D) K) (x y : O) :
    K ⊗ C.enriched.Hom x y ⟶ D.enriched.Hom x y where
  app n z := (F.app n z.1).map x y z.2
  naturality _ _ i := by
    funext z
    exact congrArg (fun h ↦ h.map x y z.2) (F.naturality i z.1)

/-- Curry every original Hom function, with its full fixed-object identity and composition. -/
def familyToCotensor {O : Type u} {C D : FixedSimplicialCategory O} {K : SSet.{u}}
    (F : Functor.HomObj (degreewiseObj C) (degreewiseObj D) K) : C ⟶ cotensor K D where
  map x y := curry (familyHom F x y)
  map_id x := by
    apply NatTrans.ext
    funext n p
    cases p
    apply Functor.HomObj.ext
    funext m i k
    change (F.app m k).map x x
      ((C.enriched.Hom x x).map i ((C.enriched.id x).app n PUnit.unit)) =
        (((cotensor K D).enriched.id x).app n PUnit.unit).app m i k
    rw [cotensor_point_id]
    have h := (congrFun ((C.enriched.id x).naturality i) PUnit.unit).symm
    change (C.enriched.Hom x x).map i ((C.enriched.id x).app n PUnit.unit) =
      (C.enriched.id x).app m PUnit.unit at h
    rw [h]
    exact (F.app m k).map_id x
  map_comp x y z := by
    apply NatTrans.ext
    funext n f
    apply Functor.HomObj.ext
    funext m i k
    change (F.app m k).map x z
      ((C.enriched.Hom x z).map i ((C.enriched.comp x y z).app n f)) =
        (((cotensor K D).enriched.comp x y z).app n
          ((curry (familyHom F x y)).app n f.1,
            (curry (familyHom F y z)).app n f.2)).app m i k
    rw [cotensor_point_comp]
    have h := (congrFun ((C.enriched.comp x y z).naturality i) f).symm
    change (C.enriched.Hom x z).map i ((C.enriched.comp x y z).app n f) =
      (C.enriched.comp x y z).app m
        ((C.enriched.Hom x y).map i f.1, (C.enriched.Hom y z).map i f.2) at h
    rw [h]
    exact (F.app m k).map_comp x y z
      ((C.enriched.Hom x y).map i f.1) ((C.enriched.Hom y z).map i f.2)

/-- Uncurry the full original cotensor functor into its actual parameter family. -/
def familyOfCotensor {O : Type u} {C D : FixedSimplicialCategory O} {K : SSet.{u}}
    (F : C ⟶ cotensor K D) : Functor.HomObj (degreewiseObj C) (degreewiseObj D) K where
  app n k :=
    { map x y f := (uncurry (F.map x y)).app n (k, f)
      map_id x := by
        have h := congrFun (NatTrans.congr_app (F.map_id x) n) PUnit.unit
        have hp := congrFun (Functor.HomObj.congr_app h n (𝟙 n)) k
        change ((F.map x x).app n ((C.enriched.id x).app n PUnit.unit)).app n (𝟙 n) k =
          (((cotensor K D).enriched.id x).app n PUnit.unit).app n (𝟙 n) k at hp
        rw [cotensor_point_id] at hp
        exact hp
      map_comp x y z f g := by
        have h := congrFun (NatTrans.congr_app (F.map_comp x y z) n) (f, g)
        have hp := congrFun (Functor.HomObj.congr_app h n (𝟙 n)) k
        change ((F.map x z).app n ((C.enriched.comp x y z).app n (f, g))).app n (𝟙 n) k =
          (((cotensor K D).enriched.comp x y z).app n
            ((F.map x y).app n f, (F.map y z).app n g)).app n (𝟙 n) k at hp
        rw [cotensor_point_comp] at hp
        exact hp }
  naturality i k := degreeHom_ext (fun x y f ↦
    congrFun ((uncurry (F.map x y)).naturality i) (k, f))

/-- Both directions recover the entire original cotensor functor. -/
theorem familyToCotensor_familyOfCotensor {O : Type u} {C D : FixedSimplicialCategory O}
    {K : SSet.{u}} (F : C ⟶ cotensor K D) :
    familyToCotensor (familyOfCotensor F) = F := by
  apply fixedHom_ext
  intro x y
  change curry (uncurry (F.map x y)) = F.map x y
  exact curry_uncurry _

/-- Both directions recover the full parameter family, including every original Hom function. -/
theorem familyOfCotensor_familyToCotensor {O : Type u} {C D : FixedSimplicialCategory O}
    {K : SSet.{u}} (F : Functor.HomObj (degreewiseObj C) (degreewiseObj D) K) :
    familyOfCotensor (familyToCotensor F) = F := by
  apply Functor.HomObj.ext
  funext n k
  apply degreeHom_ext
  intro x y f
  change (F.app n k).map x y ((C.enriched.Hom x y).map (𝟙 n) f) = (F.app n k).map x y f
  rw [(C.enriched.Hom x y).map_id]
  rfl

/-- The exact full equivalence of original parameter families and cotensor functors. -/
def familyEquiv {O : Type u} (C D : FixedSimplicialCategory O) (K : SSet.{u}) :
    Functor.HomObj (degreewiseObj C) (degreewiseObj D) K ≃ (C ⟶ cotensor K D) where
  toFun := familyToCotensor
  invFun := familyOfCotensor
  left_inv := familyOfCotensor_familyToCotensor
  right_inv := familyToCotensor_familyOfCotensor

/-- The original internal-Hom object represents the full Mathlib simplicial mapping object. -/
def cotensorHomEquiv {O : Type u} (C D : FixedSimplicialCategory O) (K : SSet.{u}) :
    (K ⟶ mapping C D) ≃ (C ⟶ cotensor K D) :=
  (parameterEquiv C D K).trans (familyEquiv C D K)

/-- Every parameter restriction commutes with currying of the full original family. -/
theorem familyToCotensor_parameter {O : Type u} {C D : FixedSimplicialCategory O}
    {K L : SSet.{u}} (i : K ⟶ L)
    (F : Functor.HomObj (degreewiseObj C) (degreewiseObj D) L) :
    familyToCotensor (Functor.HomObj.map i F) = familyToCotensor F ≫ cotensorPre i D := by
  apply fixedHom_ext
  intro x y
  change curry (familyHom (Functor.HomObj.map i F) x y) =
    curry (familyHom F x y) ≫ (MonoidalClosed.pre i).app (D.enriched.Hom x y)
  rw [curry_pre_app]
  congr 1

/-- The entire representing equivalence is natural in every actual parameter map. -/
theorem cotensorHomEquiv_parameter {O : Type u} (C D : FixedSimplicialCategory O)
    {K L : SSet.{u}} (i : K ⟶ L) (F : L ⟶ mapping C D) :
    cotensorHomEquiv C D K (i ≫ F) = cotensorHomEquiv C D L F ≫ cotensorPre i D := by
  change familyToCotensor (parameterEquiv C D K (i ≫ F)) = _
  rw [parameterEquiv_parameter]
  exact familyToCotensor_parameter i _

end

end DaggerOriginalFixedObjectCotensorRepresentation
