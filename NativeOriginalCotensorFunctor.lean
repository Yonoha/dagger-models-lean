import NativeCoherentCotensorConstants

/-! Original cotensors act on all enriched functors, including object-changing ones. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed
open DaggerModels DaggerOriginalCotensorPrecompositionWeak
open DaggerOriginalFixedObjectCotensorPoints DaggerNativeCoherentCotensorConstants
open DaggerOriginalFixedObjectCotensors
universe u
namespace DaggerNativeOriginalCotensorFunctor
noncomputable section

attribute [local instance] ihomBraided

/-- Apply the native internal Hom to each original Hom map and retain the object map. -/
def map (K : SSet.{u}) {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    originalCotensor K C ⟶ originalCotensor K D where
  obj := F.obj
  map x y := (ihom K).map (F.map x y)
  map_id x := by
    letI := C.enriched
    letI := D.enriched
    have h := F.map_id x
    change C.enriched.id x ≫ F.map x x = D.enriched.id (F.obj x) at h
    change (Functor.LaxMonoidal.ε (ihom K) ≫ (ihom K).map (C.enriched.id x)) ≫
      (ihom K).map (F.map x x) =
        Functor.LaxMonoidal.ε (ihom K) ≫ (ihom K).map (D.enriched.id (F.obj x))
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, h]
  map_comp x y z := by
    letI := C.enriched
    letI := D.enriched
    have h := F.map_comp x y z
    change C.enriched.comp x y z ≫ F.map x z =
      (F.map x y ⊗ₘ F.map y z) ≫ D.enriched.comp (F.obj x) (F.obj y) (F.obj z) at h
    change (Functor.LaxMonoidal.μ (ihom K) _ _ ≫
      (ihom K).map (C.enriched.comp x y z)) ≫ (ihom K).map (F.map x z) =
        ((ihom K).map (F.map x y) ⊗ₘ (ihom K).map (F.map y z)) ≫
          Functor.LaxMonoidal.μ (ihom K) _ _ ≫
            (ihom K).map (D.enriched.comp (F.obj x) (F.obj y) (F.obj z))
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, h,
      CategoryTheory.Functor.map_comp, Functor.LaxMonoidal.μ_natural_assoc]

theorem map_id (K : SSet.{u}) (C : SimplicialCat.{u, u}) : map K (𝟙 C) = 𝟙 _ := by
  letI := (originalCotensor K C).enriched
  apply EnrichedFunctor.ext SSet (F := map K (𝟙 C))
    (G := 𝟙 (originalCotensor K C)) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact (ihom K).map_id _

theorem map_comp (K : SSet.{u}) {C D E : SimplicialCat.{u, u}}
    (F : C ⟶ D) (G : D ⟶ E) : map K (F ≫ G) = map K F ≫ map K G := by
  apply EnrichedFunctor.ext SSet (F := map K (F ≫ G))
    (G := map K F ≫ map K G) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact (ihom K).map_comp (F.map x y) (G.map (F.obj x) (F.obj y))

/-- Restriction commutes with every original functor and its full object map. -/
theorem restriction_natural {K L : SSet.{u}} (i : K ⟶ L)
    {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    map L F ≫ restrictionFunctor i D = restrictionFunctor i C ≫ map K F := by
  apply EnrichedFunctor.ext SSet (F := map L F ≫ restrictionFunctor i D)
    (G := restrictionFunctor i C ≫ map K F) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact (MonoidalClosed.pre i).naturality (F.map x y)

/-- Constants commute with all original enriched functors. -/
theorem constant_natural (K : SSet.{u}) {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    constantFunctor K C ≫ map K F = F ≫ constantFunctor K D := by
  apply EnrichedFunctor.ext SSet (F := constantFunctor K C ≫ map K F)
    (G := F ≫ constantFunctor K D) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext n f
  apply Functor.HomObj.ext
  funext m i k
  exact congrFun ((F.map x y).naturality i) f

end
end DaggerNativeOriginalCotensorFunctor
