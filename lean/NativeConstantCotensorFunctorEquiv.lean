import NativeConstantIhomEquiv

/-! Entire original constant-source cotensor functors are the SAME degree-category functors. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed DaggerModels
open DaggerActualConstantSimplicialCategory DaggerActualConstantEnrichmentFunctor
open DaggerOriginalCotensorPrecompositionWeak DaggerOriginalSimplicialDegreeCategory
open DaggerNativeDegreeCotensorYoneda DaggerNativeConstantIhomEquiv
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
universe u
namespace DaggerNativeConstantCotensorFunctorEquiv
noncomputable section
variable (A : Type u) [Category.{u} A]
local instance : EnrichedCategory SSet.{u} A := DaggerUnitaryDiscrete.ordinaryEnriched _

/-- The SAME object map and the native degree-q Yoneda value of each original Hom map. -/
def toOrdinary (C : SimplicialCat.{u, u}) (q : SimplexCategoryᵒᵖ)
    (F : constant A ⟶ originalCotensor (SSet.stdSimplex.obj q.unop) C) :
    A ⥤ degreeObjects C q where
  obj := F.obj
  map {x y} f := degreeEquiv (x ⟶ y) (C.enriched.Hom (F.obj x) (F.obj y)) q.unop
    (F.map x y) f
  map_id x := by
    rw [degreeEquiv_apply]
    have h := congrFun (NatTrans.congr_app (F.map_id x) q) PUnit.unit
    change (F.map x x).app q (𝟙 x) =
      ((cotensor (SSet.stdSimplex.obj q.unop) ⟨C.enriched⟩).enriched.id (F.obj x)).app q
        PUnit.unit at h
    change ((F.map x x).app q (𝟙 x)).app q (𝟙 q)
      (SSet.stdSimplex.objEquiv.symm (𝟙 q.unop)) =
        (C.enriched.id (F.obj x)).app q PUnit.unit
    rw [h]
    exact cotensor_point_id _ _ _ q q (𝟙 q) _
  map_comp {x y z} f g := by
    simp only [degreeEquiv_apply]
    have h := congrFun (NatTrans.congr_app (F.map_comp x y z) q) (f, g)
    change (F.map x z).app q (f ≫ g) =
      ((cotensor (SSet.stdSimplex.obj q.unop) ⟨C.enriched⟩).enriched.comp
        (F.obj x) (F.obj y) (F.obj z)).app q
          ((F.map x y).app q f, (F.map y z).app q g) at h
    change ((F.map x z).app q (f ≫ g)).app q (𝟙 q)
      (SSet.stdSimplex.objEquiv.symm (𝟙 q.unop)) =
        (C.enriched.comp (F.obj x) (F.obj y) (F.obj z)).app q
          (((F.map x y).app q f).app q (𝟙 q) (SSet.stdSimplex.objEquiv.symm (𝟙 q.unop)),
            ((F.map y z).app q g).app q (𝟙 q) (SSet.stdSimplex.objEquiv.symm (𝟙 q.unop)))
    rw [h]
    exact cotensor_point_comp _ _ _ _ _ q q (𝟙 q) _ _ _

/-- The inverse is EXACTLY the existing original degreeToCotensor comparison. -/
def fromOrdinary (C : SimplicialCat.{u, u}) (q : SimplexCategoryᵒᵖ)
    (F : A ⥤ degreeObjects C q) : constant A ⟶
      originalCotensor (SSet.stdSimplex.obj q.unop) C :=
  constantMap F ≫ degreeToCotensor C q.unop

/-- The entire original ordinary functor is recovered, with the same object function. -/
theorem from_to (C : SimplicialCat.{u, u}) (q : SimplexCategoryᵒᵖ)
    (F : A ⥤ degreeObjects C q) : toOrdinary A C q (fromOrdinary A C q F) = F := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro x y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  let e := degreeEquiv (x ⟶ y) (C.enriched.Hom (F.obj x) (F.obj y)) q.unop
  change e (e.symm (fun g ↦ F.map g)) f = F.map f
  exact congrFun (e.apply_symm_apply (fun g ↦ F.map g)) f

/-- The entire original enriched functor is recovered in every degree and at every Hom. -/
theorem to_from (C : SimplicialCat.{u, u}) (q : SimplexCategoryᵒᵖ)
    (F : constant A ⟶ originalCotensor (SSet.stdSimplex.obj q.unop) C) :
    fromOrdinary A C q (toOrdinary A C q F) = F := by
  apply EnrichedFunctor.ext SSet (F := fromOrdinary A C q (toOrdinary A C q F))
    (G := F) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  let e := degreeEquiv (x ⟶ y) (C.enriched.Hom (F.obj x) (F.obj y)) q.unop
  change e.symm (e (F.map x y)) = F.map x y
  exact e.symm_apply_apply (F.map x y)

/-- A bijection of WHOLE functors, including arbitrary original target-object functions. -/
def functorEquiv (C : SimplicialCat.{u, u}) (q : SimplexCategoryᵒᵖ) :
    (constant A ⟶ originalCotensor (SSet.stdSimplex.obj q.unop) C) ≃
      (A ⥤ degreeObjects C q) where
  toFun := toOrdinary A C q
  invFun := fromOrdinary A C q
  left_inv := to_from A C q
  right_inv := from_to A C q

end
end DaggerNativeConstantCotensorFunctorEquiv
