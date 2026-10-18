import ActualSimplicialIsomorphismComponentPart
import NativeEnrichedHomSubcomplexFactor

/-! All original enriched functors act on the same all-isomorphism components. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerActualConstantSimplicialCategory
open DaggerActualPiZeroConstantHomEquivalence DaggerActualSimplicialIsomorphismComponentPart
universe u
namespace DaggerActualSimplicialIsomorphismComponentMaps
noncomputable section

local instance (C : SimplicialCat.{u, u}) :
    EnrichedCategory SSet.{u} (constant (componentObjects C)).Obj :=
  (constant (componentObjects C)).enriched

theorem mem_iff_vertex (C : SimplicialCat.{u, u}) (x y : componentObjects C)
    (q : SimplexCategoryᵒᵖ) (s : (C.enriched.Hom x y).obj q) (φ : ⦋0⦌ ⟶ q.unop) :
    s ∈ (homSubcomplex C x y).obj q ↔
      (C.enriched.Hom x y).map φ.op s ∈ (homSubcomplex C x y).obj (op ⦋0⦌) := by
  have ht := congrFun (((projection C).map x y).naturality φ.op) s
  change ((projection C).map x y).app (op ⦋0⦌) ((C.enriched.Hom x y).map φ.op s) =
    ((projection C).map x y).app q s at ht
  change IsIso (((projection C).map x y).app q s) ↔ IsIso _
  rw [ht]

theorem projection_hom_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : componentObjects C) :
    F.map x y ≫ (projection D).map (F.obj x) (F.obj y) =
      (projection C).map x y ≫ DaggerUnitaryDiscrete.constMap
        (fun a : (x : componentObjects C) ⟶ (y : componentObjects C) ↦
          (componentFunctor F).map a) := by
  apply constant_ext
  intro v
  change ((projection D).map (F.obj x) (F.obj y)).app (op ⦋0⦌)
      ((F.map x y).app (op ⦋0⦌) v) =
    (componentFunctor F).map (((projection C).map x y).app (op ⦋0⦌) v)
  rw [projection_vertex, projection_vertex]
  rfl

theorem projection_map_apply {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : componentObjects C)
    (q : SimplexCategoryᵒᵖ) (s : (C.enriched.Hom x y).obj q) :
    ((projection D).map (F.obj x) (F.obj y)).app q ((F.map x y).app q s) =
      (componentFunctor F).map (((projection C).map x y).app q s) :=
  congrFun (NatTrans.congr_app (projection_hom_natural F x y) q) s

theorem map_mem {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : componentObjects C)
    (q : SimplexCategoryᵒᵖ) (s : (homSubcomplex C x y : SSet.{u}).obj q) :
    (F.map x y).app q s.val ∈ (homSubcomplex D (F.obj x) (F.obj y)).obj q := by
  change IsIso (((projection D).map (F.obj x) (F.obj y)).app q ((F.map x y).app q s.val))
  rw [projection_map_apply]
  have : IsIso (((projection C).map x y).app q s.val) := s.property
  infer_instance

def map {C D : SimplicialCat.{u, u}} (F : C ⟶ D) : part C ⟶ part D :=
  DaggerNativeEnrichedHomSubcomplexFactor.factor (inclusion C ≫ F) (homSubcomplex D)
    (id_mem D) (comp_mem D) (map_mem F)

theorem inclusion_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    map F ≫ inclusion D = inclusion C ≫ F :=
  DaggerNativeEnrichedHomSubcomplexFactor.factor_comp_inclusion _ _ _ _ _

theorem map_val {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : componentObjects C)
    (q : SimplexCategoryᵒᵖ) (s : (homSubcomplex C x y : SSet.{u}).obj q) :
    ((map F).map x y |>.app q s).val = (F.map x y).app q s.val :=
  rfl

theorem map_id (C : SimplicialCat.{u, u}) : map (𝟙 C) = 𝟙 (part C) := by
  letI := (part C).enriched
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

theorem map_comp {C D E : SimplicialCat.{u, u}} (F : C ⟶ D) (G : D ⟶ E) :
    map (F ≫ G) = map F ≫ map G := by
  letI := (part C).enriched
  letI := (part E).enriched
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

end
end DaggerActualSimplicialIsomorphismComponentMaps
