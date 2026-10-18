import OriginalSimplicialCategoryWholeBarFibrePullback

/-!
# Whole original Hom-fibre naturality for every original enriched functor

The source and every endpoint are sent by the original object map. The Hom
coproduct map uses the original Hom maps and native coproduct reindexing.
The whole strict-fibre map restricts the actual original whole bar map.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFunctor
open DaggerOriginalSimplicialCategoryBarFibre
open DaggerOriginalSimplicialCategoryBarHomInclusion
open DaggerOriginalSimplicialCategoryBarFibreFunctor
open DaggerOriginalSimplicialCategoryWholeBarFibreDegree
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
noncomputable section

/-- The original enriched functor acts on every original Hom and endpoint of the coproduct. -/
def originalHomSumMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    originalHomSum C x ⟶ originalHomSum D (F.obj x) :=
  Limits.Sigma.map' F.obj (F.map x)

/-- Restrict the actual whole original bar map to its actual whole original strict fibre. -/
def wholeBarFibreMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    (wholeBarFibre C x).toSSet ⟶ (wholeBarFibre D (F.obj x)).toSSet where
  app n a := ⟨(barMap F).app n a.val, by
    change (barProjection D).app n ((barMap F).app n a.val) =
      constantSourceSimplex D (F.obj x) n
    calc
      _ = (diagonalNerveFunctor.map F).app n ((barProjection C).app n a.val) :=
        congrFun (NatTrans.congr_app (barProjection_natural F) n) a.val
      _ = (diagonalNerveFunctor.map F).app n (constantSourceSimplex C x n) :=
        congrArg (fun b ↦ (diagonalNerveFunctor.map F).app n b) a.property
      _ = constantSourceSimplex D (F.obj x) n := constantSourceSimplex_natural F x n⟩
  naturality _ _ i := by
    funext a
    apply Subtype.ext
    exact congrFun ((barMap F).naturality i) a.val

/-- The restricted map retains the whole original bar map after inclusion. -/
theorem wholeBarFibreMap_ι {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    wholeBarFibreMap F x ≫ (wholeBarFibre D (F.obj x)).ι =
      (wholeBarFibre C x).ι ≫ barMap F := by
  apply NatTrans.ext
  funext n
  rfl

/-- The whole Hom inclusion is natural with the original Hom maps at all original endpoints. -/
theorem wholeBarHomInclusion_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (x : C.Obj) :
    originalHomSumMap F x ≫ wholeBarHomInclusion D (F.obj x) =
      wholeBarHomInclusion C x ≫ barMap F := by
  apply Sigma.hom_ext
  intro y
  change Sigma.ι (fun y ↦ C.enriched.Hom x y) y ≫
      (Limits.Sigma.map' F.obj (F.map x) ≫
        Sigma.desc (fun z ↦ barHomInclusion D (F.obj x) z ≫ barInclusion D z)) =
    Sigma.ι (fun y ↦ C.enriched.Hom x y) y ≫
      (Sigma.desc (fun y ↦ barHomInclusion C x y ≫ barInclusion C y) ≫ barMap F)
  rw [← Category.assoc, Sigma.ι_comp_map', Category.assoc, Sigma.ι_desc,
    ← Category.assoc, barHomInclusion_natural, Category.assoc,
    ← barInclusion_map, ← Category.assoc, ← Category.assoc, Sigma.ι_desc]

/-- The entire Hom-coproduct fibre isomorphism is natural for every original functor. -/
theorem wholeBarHomFibreIso_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (x : C.Obj) :
    originalHomSumMap F x ≫ (wholeBarHomFibreIso D (F.obj x)).hom =
      (wholeBarHomFibreIso C x).hom ≫ wholeBarFibreMap F x := by
  apply (cancel_mono (wholeBarFibre D (F.obj x)).ι).mp
  rw [Category.assoc, wholeBarHomFibreIso_hom_ι, Category.assoc, wholeBarFibreMap_ι,
    ← Category.assoc, wholeBarHomFibreIso_hom_ι]
  exact wholeBarHomInclusion_natural F x

end
end DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
