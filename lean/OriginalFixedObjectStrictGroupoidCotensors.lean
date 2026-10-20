import OriginalFixedObjectCotensors

/-!
# Cotensors retain original strict groupoids

The original inverse maps are natural under every simplicial operator. Internal
Hom carries those maps to the inverse of each parameterized arrow. Native finite
product preservation gives the exact pointwise composition and cancellation.
No fibrancy, nonemptiness or model structure is assumed.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial DaggerModels
open Functor.LaxMonoidal
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectCotensors
universe u

namespace DaggerOriginalFixedObjectStrictGroupoidCotensors

noncomputable section

attribute [local instance] DaggerOriginalFixedObjectCotensors.ihomBraided

/-- Inversion on the exact original Hom, natural for every original simplicial operator. -/
def originalInverseHom (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (x y : C.Obj) :
    C.enriched.Hom x y ⟶ C.enriched.Hom y x where
  app n f := @inv (degreeObjects C n) (degreeCategory C n) x y f (hC n x y f)
  naturality {n m} i := by
    ext f
    letI : IsIso (C := degreeObjects C n) f := hC n x y f
    exact ((degreeMap C i).map_inv f).symm

/-- Native product comparison pairs the full internal-Hom families pointwise. -/
theorem ihom_mu_apply (K X Y : SSet.{u}) (n m : SimplexCategoryᵒᵖ) (i : n ⟶ m)
    (f : ((ihom K).obj X).obj n) (g : ((ihom K).obj Y).obj n) (k : K.obj m) :
    ((μ (ihom K) X Y).app n (f, g)).app m i k = (f.app m i k, g.app m i k) := by
  apply Prod.ext
  · exact congrFun (Functor.HomObj.congr_app
      (congrFun (NatTrans.congr_app (Functor.Monoidal.μ_fst (ihom K) X Y) n) (f, g)) m i) k
  · exact congrFun (Functor.HomObj.congr_app
      (congrFun (NatTrans.congr_app (Functor.Monoidal.μ_snd (ihom K) X Y) n) (f, g)) m i) k

/-- The transported degree identity is the original identity at each parameter value. -/
theorem cotensor_point_id (K : SSet.{u}) {O : Type u} (C : FixedSimplicialCategory O)
    (x : O) (n m : SimplexCategoryᵒᵖ) (i : n ⟶ m) (k : K.obj m) :
    (((cotensor K C).enriched.id x).app n PUnit.unit).app m i k =
      (C.enriched.id x).app m PUnit.unit := by
  letI : Subsingleton ((𝟙_ SSet.{u}).obj m) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  change (C.enriched.id x).app m _ = (C.enriched.id x).app m PUnit.unit
  exact congrArg ((C.enriched.id x).app m) (Subsingleton.elim _ _)

/-- The transported degree composition retains the same parameter for both factors. -/
theorem cotensor_point_comp (K : SSet.{u}) {O : Type u} (C : FixedSimplicialCategory O)
    (x y z : O) (n m : SimplexCategoryᵒᵖ) (i : n ⟶ m)
    (f : ((cotensor K C).enriched.Hom x y).obj n)
    (g : ((cotensor K C).enriched.Hom y z).obj n) (k : K.obj m) :
    (((cotensor K C).enriched.comp x y z).app n (f, g)).app m i k =
      (C.enriched.comp x y z).app m (f.app m i k, g.app m i k) := by
  change (C.enriched.comp x y z).app m
    (((μ (ihom K) _ _).app n (f, g)).app m i k) = _
  rw [ihom_mu_apply]

/-- Every arrow in every original cotensor degree has its actual pointwise inverse. -/
theorem cotensor_strict (K : SSet.{u}) {O : Type u} (C : FixedStrictGroupoids O) :
    IsStrictFixed (cotensor K C.obj) := by
  intro n x y f
  let g := ((ihom K).map (originalInverseHom (original O C.obj) C.property x y)).app n f
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply Functor.HomObj.ext
    funext m i k
    change (((cotensor K C.obj).enriched.comp x y x).app n (f, g)).app m i k =
      (((cotensor K C.obj).enriched.id x).app n PUnit.unit).app m i k
    rw [cotensor_point_comp, cotensor_point_id]
    exact @IsIso.hom_inv_id (degreeObjects (original O C.obj) m)
      (degreeCategory (original O C.obj) m) x y (f.app m i k)
      (C.property m x y (f.app m i k))
  · apply Functor.HomObj.ext
    funext m i k
    change (((cotensor K C.obj).enriched.comp y x y).app n (g, f)).app m i k =
      (((cotensor K C.obj).enriched.id y).app n PUnit.unit).app m i k
    rw [cotensor_point_comp, cotensor_point_id]
    exact @IsIso.inv_hom_id (degreeObjects (original O C.obj) m)
      (degreeCategory (original O C.obj) m) x y (f.app m i k)
      (C.property m x y (f.app m i k))

/-- The actual internal-Hom object remains a strict groupoid on exactly O. -/
def strictCotensor (K : SSet.{u}) {O : Type u} (C : FixedStrictGroupoids O) :
    FixedStrictGroupoids O := ⟨cotensor K C.obj, cotensor_strict K C⟩

/-- The same transported dagger cotensor remains a strict dagger groupoid. -/
def strictDaggerCotensor (K : SSet.{u}) {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    FixedStrictDaggerGroupoids O :=
  ⟨daggerCotensor K C.obj, cotensor_strict K ⟨C.obj.underlying, C.property⟩⟩

/-- The exact ordinary cotensor functor restricted to the original strict groupoids. -/
def strictCotensorFunctor (O : Type u) (K : SSet.{u}) :
    FixedStrictGroupoids O ⥤ FixedStrictGroupoids O where
  obj := strictCotensor K
  map F := ObjectProperty.homMk (cotensorMap K F.hom)
  map_id C := ObjectProperty.hom_ext _ ((cotensorFunctor O K).map_id C.obj)
  map_comp F G := ObjectProperty.hom_ext _ ((cotensorFunctor O K).map_comp F.hom G.hom)

/-- The same full dagger cotensor functor restricted to the original strict dagger groupoids. -/
def strictDaggerCotensorFunctor (O : Type u) (K : SSet.{u}) :
    FixedStrictDaggerGroupoids O ⥤ FixedStrictDaggerGroupoids O where
  obj := strictDaggerCotensor K
  map F := ObjectProperty.homMk (daggerCotensorMap K F.hom)
  map_id C := ObjectProperty.hom_ext _ ((daggerCotensorFunctor O K).map_id C.obj)
  map_comp F G := ObjectProperty.hom_ext _ ((daggerCotensorFunctor O K).map_comp F.hom G.hom)

/-- Strict cotensors retain both parameter and original groupoid variances. -/
def strictCotensorBifunctor (O : Type u) :
    SSet.{u}ᵒᵖ ⥤ FixedStrictGroupoids O ⥤ FixedStrictGroupoids O where
  obj K := strictCotensorFunctor O K.unop
  map i :=
    { app C := ObjectProperty.homMk (cotensorPre i.unop C.obj)
      naturality _ _ F := ObjectProperty.hom_ext _ (cotensorPre_map i.unop F.hom) }
  map_id K := by
    apply NatTrans.ext
    funext C
    exact ObjectProperty.hom_ext _ (cotensorPre_id K.unop C.obj)
  map_comp i j := by
    apply NatTrans.ext
    funext C
    exact ObjectProperty.hom_ext _ (cotensorPre_comp j.unop i.unop C.obj)

/-- The original strict dagger cotensors form the same two-variable functor. -/
def strictDaggerCotensorBifunctor (O : Type u) :
    SSet.{u}ᵒᵖ ⥤ FixedStrictDaggerGroupoids O ⥤ FixedStrictDaggerGroupoids O where
  obj K := strictDaggerCotensorFunctor O K.unop
  map i :=
    { app C := ObjectProperty.homMk (daggerCotensorPre i.unop C.obj)
      naturality _ _ F := ObjectProperty.hom_ext _ (daggerCotensorPre_map i.unop F.hom) }
  map_id K := by
    apply NatTrans.ext
    funext C
    exact ObjectProperty.hom_ext _
      (fixedDaggerHom_ext (cotensorPre_id K.unop C.obj.underlying))
  map_comp i j := by
    apply NatTrans.ext
    funext C
    exact ObjectProperty.hom_ext _
      (fixedDaggerHom_ext (cotensorPre_comp j.unop i.unop C.obj.underlying))

/-- Inclusion retains the entire ordinary cotensor diagram, not only its Hom types. -/
theorem strictCotensor_forget {O : Type u} (K : SSet.{u}) (C : FixedStrictGroupoids O) :
    (strictCotensor K C).obj = cotensor K C.obj := rfl

/-- Dagger inclusion retains the entire original dagger cotensor. -/
theorem strictDaggerCotensor_forget {O : Type u} (K : SSet.{u})
    (C : FixedStrictDaggerGroupoids O) :
    (strictDaggerCotensor K C).obj = daggerCotensor K C.obj := rfl

end

end DaggerOriginalFixedObjectStrictGroupoidCotensors
