import NativeTotalBasedPiFunctor
import TopCatModelCategory.ModelCategorySSet

/-! Original vertices with native pi of singular realization, retaining every actual target map. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open SSet.KanComplex DaggerNativeTotalBasedPiFunctor
universe u
namespace DaggerNativeGeometricTotalPiFunctor
noncomputable section

abbrev singularRealization : SSet.{u} ⥤ SSet.{u} := SSet.toTop ⋙ TopCat.toSSet

def unitVertex (X : SSet.{u}) (x : X _⦋0⦌) : (singularRealization.obj X) _⦋0⦌ :=
  (sSetTopAdj.unit.app X).app _ x

theorem unitVertex_natural {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (singularRealization.map f).app _ (unitVertex X x) = unitVertex Y (f.app _ x) :=
  congrFun (NatTrans.congr_app (sSetTopAdj.unit_naturality f) _) x

theorem sigma_mapπ_target {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) (x : X _⦋0⦌)
    (y : Y _⦋0⦌) (h : f.app _ x = y) (s : π n X x) :
    (⟨y, mapπ f n x y h s⟩ : Σ y : Y _⦋0⦌, π n Y y) =
      ⟨f.app _ x, mapπ f n x _ rfl s⟩ := by
  subst y
  rfl

def geometricPiFunctor (n : ℕ) : SSet.{u} ⥤ Type u where
  obj X := Σ x : X _⦋0⦌, π n (singularRealization.obj X) (unitVertex X x)
  map f s := ⟨f.app _ s.1, mapπ (singularRealization.map f) n
    (unitVertex _ s.1) (unitVertex _ (f.app _ s.1)) (unitVertex_natural f s.1) s.2⟩
  map_id X := by
    funext ⟨x, s⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    change mapπ (singularRealization.map (𝟙 X)) n (unitVertex X x) (unitVertex X x) _ s = s
    simp only [CategoryTheory.Functor.map_id]
    exact mapπ_id _ _ _
  map_comp f g := by
    funext ⟨x, s⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    change mapπ (singularRealization.map (f ≫ g)) n _ _ _ s = _
    simp only [CategoryTheory.Functor.map_comp]
    exact (mapπ_mapπ (singularRealization.map f) n _ _ (unitVertex_natural f x)
      (singularRealization.map g) _ (unitVertex_natural g (f.app _ x)) s).symm

def geometricVertexProjection (n : ℕ) :
    geometricPiFunctor.{u} n ⟶ SSet.evaluation.obj (op ⦋0⦌) where
  app _ s := s.1
  naturality _ _ _ := rfl

def unitVertices : SSet.evaluation.obj (op ⦋0⦌) ⟶
    singularRealization.{u} ⋙ SSet.evaluation.obj (op ⦋0⦌) where
  app X x := unitVertex X x
  naturality X Y f := by
    funext x
    exact (unitVertex_natural f x).symm

def toSingularTotalPi (n : ℕ) :
    geometricPiFunctor.{u} n ⟶ singularRealization ⋙ totalPiFunctor n where
  app X s := ⟨unitVertex X s.1, s.2⟩
  naturality X Y f := by
    funext ⟨x, s⟩
    exact sigma_mapπ_target (singularRealization.map f) n _ _ (unitVertex_natural f x) s

theorem geometricPiFunctor_map (n : ℕ) {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X _⦋0⦌) (s : π n (singularRealization.obj X) (unitVertex X x)) :
    (geometricPiFunctor n).map f ⟨x, s⟩ = ⟨f.app _ x,
      mapπ (singularRealization.map f) n _ _ (unitVertex_natural f x) s⟩ := rfl

end
end DaggerNativeGeometricTotalPiFunctor
