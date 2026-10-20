import OriginalSimplicialCategoryDiagonalNerve

/-!
# The original degreewise over categories in the DK80 bar construction

Fix an original object Y. The degree-n category is the ordinary over category
of Y in the original degree-n category of C. Every operator is the native
pushforward along the original degree functor. The forgetful functors give a
natural projection to the unchanged original degree-category diagram.
No realization, quasifibration, or weak-equivalence assertion is assumed.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryDiagonalNerve
universe u
namespace DaggerOriginalSimplicialCategoryOverDiagram
noncomputable section

/-- Native over morphisms agree heterogeneously when endpoints and left maps agree. -/
theorem overHom_heq {T : Type u} [Category.{u} T] {y : T}
    {a b c d : Over y} (ha : a = c) (hb : b = d) (f : a ⟶ b) (g : c ⟶ d)
    (h : HEq f.left g.left) : HEq f g := by
  cases ha
  cases hb
  exact heq_of_eq (CostructuredArrow.ext f g (eq_of_heq h))

/-- The original degreewise category of arrows to the chosen original object. -/
def overObjects (C : SimplicialCat.{u, u}) (y : C.Obj) (n : SimplexCategoryᵒᵖ) : Type u :=
  @Over (degreeObjects C n) (degreeCategory C n) y

/-- Retain the native over-category structure for the original degree category. -/
instance overCategory (C : SimplicialCat.{u, u}) (y : C.Obj) (n : SimplexCategoryᵒᵖ) :
    Category.{u} (overObjects C y n) :=
  inferInstanceAs (Category (@Over (degreeObjects C n) (degreeCategory C n) y))

/-- The same original operator acts on arrows and commuting triangles. -/
def overDegreeMap (C : SimplicialCat.{u, u}) (y : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) : overObjects C y n ⥤ overObjects C y m :=
  Over.post (degreeMap C i)

/-- Identity operators act as the identity on the entire original over category. -/
theorem overDegreeMap_id (C : SimplicialCat.{u, u}) (y : C.Obj)
    (n : SimplexCategoryᵒᵖ) : overDegreeMap C y (𝟙 n) = 𝟭 (overObjects C y n) := by
  have hobj : ∀ a, (overDegreeMap C y (𝟙 n)).obj a = a := by
    intro a
    apply Comma.ext (x := (overDegreeMap C y (𝟙 n)).obj a) (y := a)
      rfl (Subsingleton.elim _ _)
    exact heq_of_eq (congrFun ((C.enriched.Hom a.left y).map_id n) a.hom)
  refine Functor.hext hobj ?_
  intro a b f
  apply overHom_heq (hobj a) (hobj b)
  exact heq_of_eq (congrFun ((C.enriched.Hom a.left b.left).map_id n) f.left)

/-- Composite operators give the composite of the original over functors. -/
theorem overDegreeMap_comp (C : SimplicialCat.{u, u}) (y : C.Obj)
    {n m k : SimplexCategoryᵒᵖ} (i : n ⟶ m) (j : m ⟶ k) :
    overDegreeMap C y (i ≫ j) = overDegreeMap C y i ⋙ overDegreeMap C y j := by
  have hobj : ∀ a, (overDegreeMap C y (i ≫ j)).obj a =
      (overDegreeMap C y i ⋙ overDegreeMap C y j).obj a := by
    intro a
    apply Comma.ext (x := (overDegreeMap C y (i ≫ j)).obj a)
      (y := (overDegreeMap C y i ⋙ overDegreeMap C y j).obj a) rfl rfl
    exact heq_of_eq (congrFun ((C.enriched.Hom a.left y).map_comp i j) a.hom)
  refine Functor.hext hobj ?_
  intro a b f
  apply overHom_heq (hobj a) (hobj b)
  exact heq_of_eq (congrFun ((C.enriched.Hom a.left b.left).map_comp i j) f.left)

/-- The actual over categories form the simplicial category-valued diagram. -/
def overCategoryDiagram (C : SimplicialCat.{u, u}) (y : C.Obj) :
    SimplexCategoryᵒᵖ ⥤ Cat.{u, u} where
  obj n := Cat.of (overObjects C y n)
  map i := (overDegreeMap C y i).toCatHom
  map_id n := by
    rw [overDegreeMap_id]
    rfl
  map_comp i j := by
    rw [overDegreeMap_comp]
    rfl

/-- Forgetting the last arrow commutes with every original simplicial operator. -/
theorem overDegreeMap_forget (C : SimplicialCat.{u, u}) (y : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    overDegreeMap C y i ⋙ Over.forget (T := degreeObjects C m) y =
      Over.forget (T := degreeObjects C n) y ⋙ degreeMap C i := rfl

/-- The original bar projection before applying the nerve and diagonal. -/
def overCategoryProjection (C : SimplicialCat.{u, u}) (y : C.Obj) :
    overCategoryDiagram C y ⟶ degreeCategoryDiagram C where
  app n := (Over.forget (T := degreeObjects C n) y).toCatHom
  naturality n m i := by
    change (overDegreeMap C y i ⋙ Over.forget (T := degreeObjects C m) y).toCatHom =
      (Over.forget (T := degreeObjects C n) y ⋙ degreeMap C i).toCatHom
    exact congrArg Functor.toCatHom (overDegreeMap_forget C y i)

/-- The actual identity arrow is terminal in each original over category. -/
def overDegreeTerminal (C : SimplicialCat.{u, u}) (y : C.Obj) (n : SimplexCategoryᵒᵖ) :
    IsTerminal (Over.mk (T := degreeObjects C n)
      (@CategoryStruct.id (degreeObjects C n) (degreeCategory C n).toCategoryStruct y)) :=
  Over.mkIdTerminal

end
end DaggerOriginalSimplicialCategoryOverDiagram
