import OriginalSimplicialCategoryBarConstruction

/-!
# Full original enriched-functor naturality of the DK80 bar

Every original enriched functor acts on each degreewise over category, including
the final arrow and all commuting triangles. Its action commutes with all original
simplicial operators and with the original bar projection. The whole bar map
includes every endpoint component, with the endpoint sent by the original object map.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarConstruction
universe u
namespace DaggerOriginalSimplicialCategoryBarFunctor
noncomputable section

/-- The full original degree functor acts on arrows ending in the original endpoint. -/
def overDegreeFunctor {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (y : C.Obj)
    (n : SimplexCategoryᵒᵖ) : overObjects C y n ⥤ overObjects D (F.obj y) n :=
  Over.post (degreeFunctor F n)

/-- The endpoint component map commutes with every original simplicial operator. -/
theorem overDegreeFunctor_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (y : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    overDegreeMap C y i ⋙ overDegreeFunctor F y m =
      overDegreeFunctor F y n ⋙ overDegreeMap D (F.obj y) i := by
  have hobj : ∀ a, (overDegreeMap C y i ⋙ overDegreeFunctor F y m).obj a =
      (overDegreeFunctor F y n ⋙ overDegreeMap D (F.obj y) i).obj a := by
    intro a
    apply Comma.ext
      (x := (overDegreeMap C y i ⋙ overDegreeFunctor F y m).obj a)
      (y := (overDegreeFunctor F y n ⋙ overDegreeMap D (F.obj y) i).obj a) rfl rfl
    exact heq_of_eq (congrFun ((F.map a.left y).naturality i) a.hom)
  refine Functor.hext hobj ?_
  intro a b f
  apply overHom_heq (hobj a) (hobj b)
  exact heq_of_eq (congrFun ((F.map a.left b.left).naturality i) f.left)

/-- All degreewise over functors form the actual category-valued diagram map. -/
def overCategoryMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (y : C.Obj) :
    overCategoryDiagram C y ⟶ overCategoryDiagram D (F.obj y) where
  app n := (overDegreeFunctor F y n).toCatHom
  naturality n m i := by
    change (overDegreeMap C y i ⋙ overDegreeFunctor F y m).toCatHom =
      (overDegreeFunctor F y n ⋙ overDegreeMap D (F.obj y) i).toCatHom
    exact congrArg Functor.toCatHom (overDegreeFunctor_natural F y i)

/-- Forgetting the final arrow retains the original whole degree functor. -/
theorem overCategoryProjection_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (y : C.Obj) :
    overCategoryMap F y ≫ overCategoryProjection D (F.obj y) =
      overCategoryProjection C y ≫ degreeCategoryMap F := by
  apply NatTrans.ext
  funext n
  rfl

/-- The actual bar component map induced by the whole original enriched functor. -/
def barComponentMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (y : C.Obj) :
    barComponent C y ⟶ barComponent D (F.obj y) :=
  nerveDiagonal.map (overCategoryMap F y)

/-- The full component map is the native nerve of the original over functor. -/
theorem barComponentMap_apply {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (a : (barComponent C y).obj n) :
    (barComponentMap F y).app n a = (nerveMap (overDegreeFunctor F y n)).app n a := rfl

/-- Original component bar projection naturality keeps the original nerve map. -/
theorem barComponentProjection_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (y : C.Obj) :
    barComponentMap F y ≫ barComponentProjection D (F.obj y) =
      barComponentProjection C y ≫ diagonalNerveFunctor.map F := by
  change nerveDiagonal.map (overCategoryMap F y) ≫
    nerveDiagonal.map (overCategoryProjection D (F.obj y)) =
      nerveDiagonal.map (overCategoryProjection C y) ≫ nerveDiagonal.map (degreeCategoryMap F)
  simp only [← Functor.map_comp]
  exact congrArg (fun f ↦ nerveDiagonal.map f) (overCategoryProjection_natural F y)

/-- The whole original bar map, with every endpoint sent by the original object map. -/
def barMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) : bar C ⟶ bar D :=
  Sigma.desc (fun y ↦ barComponentMap F y ≫ barInclusion D (F.obj y))

/-- Every endpoint component of the whole bar map is the original component map. -/
theorem barInclusion_map {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (y : C.Obj) :
    barInclusion C y ≫ barMap F = barComponentMap F y ≫ barInclusion D (F.obj y) := by
  exact Sigma.ι_desc (fun y ↦ barComponentMap F y ≫ barInclusion D (F.obj y)) y

/-- The original whole bar projection is natural for all original enriched functors. -/
theorem barProjection_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    barMap F ≫ barProjection D = barProjection C ≫ diagonalNerveFunctor.map F := by
  apply Sigma.hom_ext
  intro y
  change barInclusion C y ≫ (barMap F ≫ barProjection D) =
    barInclusion C y ≫ (barProjection C ≫ diagonalNerveFunctor.map F)
  rw [← Category.assoc, barInclusion_map, Category.assoc, barInclusion_projection,
    ← Category.assoc, barInclusion_projection]
  exact barComponentProjection_natural F y

end
end DaggerOriginalSimplicialCategoryBarFunctor
