import OriginalSimplicialCategoryBarPullback

/-!
# Naturality of the full original DK80 Hom-fibre identification

All original enriched functors act on the original source vertices, Hom
inclusions and strict fibres. The strict-fibre isomorphism is natural for the
whole original enriched functor, with both original endpoint objects sent by
its original object map and every Hom simplex sent by its original Hom map.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFunctor
open DaggerOriginalSimplicialCategoryBarHomInclusion
open DaggerOriginalSimplicialCategoryBarFibre
universe u
namespace DaggerOriginalSimplicialCategoryBarFibreFunctor
noncomputable section

/-- Every original enriched functor keeps the corresponding original constant source chain. -/
theorem constantSourceSimplex_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (x : C.Obj) (n : SimplexCategoryᵒᵖ) :
    (diagonalNerveFunctor.map F).app n (constantSourceSimplex C x n) =
      constantSourceSimplex D (F.obj x) n := by
  refine Functor.hext
    (F := (diagonalNerveFunctor.map F).app n (constantSourceSimplex C x n))
    (G := constantSourceSimplex D (F.obj x) n) (fun _ ↦ rfl) ?_
  intro k l f
  exact heq_of_eq ((degreeFunctor F n).map_id x)

/-- Naturality of the original vertex map retains the whole original object map. -/
theorem sourceVertexMap_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    sourceVertexMap C x ≫ diagonalNerveFunctor.map F = sourceVertexMap D (F.obj x) := by
  apply NatTrans.ext
  funext n
  funext a
  exact constantSourceSimplex_natural F x n

/-- The Hom inclusion is natural on every original simplex and original endpoint pair. -/
theorem barHomInclusion_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : C.Obj) :
    F.map x y ≫ barHomInclusion D (F.obj x) (F.obj y) =
      barHomInclusion C x y ≫ barComponentMap F y := by
  apply NatTrans.ext
  funext n
  funext a
  refine Functor.hext
    (F := (barHomInclusion D (F.obj x) (F.obj y)).app n ((F.map x y).app n a))
    (G := (barComponentMap F y).app n ((barHomInclusion C x y).app n a))
    (fun _ ↦ rfl) ?_
  intro k l f
  exact heq_of_eq ((overDegreeFunctor F y n).map_id
    (Over.mk (T := degreeObjects C n) (X := y) (Y := x) a)).symm

/-- Restrict the full original bar map to the full original strict Hom fibre. -/
def barFibreMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : C.Obj) :
    (barFibre C x y).toSSet ⟶ (barFibre D (F.obj x) (F.obj y)).toSSet where
  app n a := ⟨(barComponentMap F y).app n a.val, by
    change (barComponentProjection D (F.obj y)).app n ((barComponentMap F y).app n a.val) =
      constantSourceSimplex D (F.obj x) n
    calc
      _ = (diagonalNerveFunctor.map F).app n ((barComponentProjection C y).app n a.val) :=
        congrFun (NatTrans.congr_app (barComponentProjection_natural F y) n) a.val
      _ = (diagonalNerveFunctor.map F).app n (constantSourceSimplex C x n) :=
        congrArg (fun b ↦ (diagonalNerveFunctor.map F).app n b) a.property
      _ = constantSourceSimplex D (F.obj x) n := constantSourceSimplex_natural F x n⟩
  naturality n m i := by
    funext a
    apply Subtype.ext
    exact congrFun ((barComponentMap F y).naturality i) a.val

/-- The restricted fibre map retains the whole original bar map under inclusion. -/
theorem barFibreMap_ι {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : C.Obj) :
    barFibreMap F x y ≫ (barFibre D (F.obj x) (F.obj y)).ι =
      (barFibre C x y).ι ≫ barComponentMap F y := by
  apply NatTrans.ext
  funext n
  rfl

/-- The whole strict-fibre isomorphism is natural for the unchanged original Hom map. -/
theorem barFibreIso_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : C.Obj) :
    F.map x y ≫ (barFibreIso D (F.obj x) (F.obj y)).hom =
      (barFibreIso C x y).hom ≫ barFibreMap F x y := by
  apply NatTrans.ext
  funext n
  funext a
  apply Subtype.ext
  exact congrFun (NatTrans.congr_app (barHomInclusion_natural F x y) n) a

end
end DaggerOriginalSimplicialCategoryBarFibreFunctor
