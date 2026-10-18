import OriginalSimplicialCategoryWholeBarGeometricStrictFibre
import OriginalSimplicialCategoryWholeBarFibreFunctor

/-!
# Exact geometric strict-fibre naturality of every original enriched functor

The geometric fibre map is the restriction of the actual realized whole-bar
map. The homeomorphism intertwines it with all original Hom maps and the
original endpoint reindexing of the full coproduct.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial DaggerModels Topology
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFunctor
open DaggerOriginalSimplicialCategoryBarFibreFunctor
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
open DaggerOriginalSimplicialCategoryWholeBarGeometricStrictFibre
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarGeometricFibreNaturality
noncomputable section

/-- Every original enriched functor sends the realized original source point to its image. -/
theorem realizedSourceVertex_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    SSet.toTop.map (diagonalNerveFunctor.map F) (realizedSourceVertex C x) =
      realizedSourceVertex D (F.obj x) := by
  have h := congrArg (fun g ↦ SSet.toTop.map g) (sourceVertexMap_natural F x)
  dsimp only at h
  rw [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h (default : SSet.toTop.obj (Δ[0] : SSet.{u}))

/-- Restrict the actual realized whole-bar map to the actual geometric point fibre. -/
def geometricWholeBarFibreMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    TopCat.of (geometricWholeBarFibre C x) ⟶ TopCat.of (geometricWholeBarFibre D (F.obj x)) :=
  TopCat.ofHom
    { toFun := fun a ↦ ⟨SSet.toTop.map (barMap F) a.val, by
        have h := congrArg (fun g ↦ SSet.toTop.map g) (barProjection_natural F)
        dsimp only at h
        rw [Functor.map_comp, Functor.map_comp] at h
        calc
          _ = SSet.toTop.map (diagonalNerveFunctor.map F)
              (SSet.toTop.map (barProjection C) a.val) := ConcreteCategory.congr_hom h a.val
          _ = SSet.toTop.map (diagonalNerveFunctor.map F) (realizedSourceVertex C x) :=
            congrArg (SSet.toTop.map (diagonalNerveFunctor.map F)) a.property
          _ = realizedSourceVertex D (F.obj x) := realizedSourceVertex_natural F x⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (SSet.toTop.map (barMap F)).hom.continuous.comp continuous_subtype_val }

/-- All original Hom maps commute with the actual geometric fibre homeomorphisms. -/
theorem wholeBarHomGeometricFibreHomeomorph_natural {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (x : C.Obj) (a : SSet.toTop.obj (originalHomSum C x)) :
    geometricWholeBarFibreMap F x (wholeBarHomGeometricFibreHomeomorph C x a) =
      wholeBarHomGeometricFibreHomeomorph D (F.obj x)
        (SSet.toTop.map (originalHomSumMap F x) a) := by
  apply Subtype.ext
  change SSet.toTop.map (barMap F) (wholeBarHomGeometricFibreHomeomorph C x a).val = _
  rw [wholeBarHomGeometricFibreHomeomorph_val, wholeBarHomGeometricFibreHomeomorph_val]
  have h := congrArg (fun g ↦ SSet.toTop.map g) (wholeBarHomInclusion_natural F x)
  dsimp only at h
  rw [Functor.map_comp, Functor.map_comp] at h
  exact (ConcreteCategory.congr_hom h a).symm

end
end DaggerOriginalSimplicialCategoryWholeBarGeometricFibreNaturality
