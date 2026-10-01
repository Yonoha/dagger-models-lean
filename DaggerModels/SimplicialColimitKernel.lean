import DaggerModels.SimplicialColimitsFree
import DaggerModels.SimplicialOpposite
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! Generators for actual ordinary simplicial-category colimits.
Only the Type colimit of objects is used. Edges retain their original diagram
object and both endpoint labels. No dagger is introduced. -/

open CategoryTheory Limits MonoidalCategory
universe u
noncomputable section

namespace DaggerModels.SimplicialCat.ColimitKernel

variable {J : Type u} [SmallCategory J] (K : J ⥤ SimplicialCat.{u, u})

def vertices : Type u := colimit (K ⋙ objects)

def vertexι (j : J) : (K.obj j).Obj → vertices K := colimit.ι (K ⋙ objects) j

def vertexDesc (s : Cocone K) : vertices K → s.pt.Obj :=
  colimit.desc (K ⋙ objects) (objects.mapCocone s)

@[simp]
theorem vertexDesc_ι (s : Cocone K) (j : J) (x : (K.obj j).Obj) :
    vertexDesc K s (vertexι K j x) = (s.ι.app j).obj x :=
  congrFun (colimit.ι_desc (objects.mapCocone s) j) x

theorem vertexι_naturality {i j : J} (a : i ⟶ j) (x : (K.obj i).Obj) :
    vertexι K j ((K.map a).obj x) = vertexι K i x :=
  congrFun (colimit.w (K ⋙ objects) a) x

def Edge (n : SimplexCategoryᵒᵖ) : Type u :=
  Σ j : J, Σ x : (K.obj j).Obj, Σ y : (K.obj j).Obj, (x ⟶[SSet] y).obj n

def source {n : SimplexCategoryᵒᵖ} (e : Edge K n) : vertices K := vertexι K e.1 e.2.1

def target {n : SimplexCategoryᵒᵖ} (e : Edge K n) : vertices K := vertexι K e.1 e.2.2.1

def edgeHom (a b : vertices K) : SSet.{u} where
  obj n := {e : Edge K n // source K e = a ∧ target K e = b}
  map α e :=
    ⟨⟨e.val.1, e.val.2.1, e.val.2.2.1, (e.val.2.1 ⟶[SSet] e.val.2.2.1).map α e.val.2.2.2⟩,
      e.property⟩
  map_id n := by
    funext e
    apply Subtype.ext
    rcases e with ⟨⟨j, x, y, f⟩, h⟩
    change (⟨j, x, y, (x ⟶[SSet] y).map (𝟙 n) f⟩ : Edge K n) = ⟨j, x, y, f⟩
    rw [FunctorToTypes.map_id_apply]
  map_comp α β := by
    funext e
    apply Subtype.ext
    rcases e with ⟨⟨j, x, y, f⟩, h⟩
    change (⟨j, x, y, (x ⟶[SSet] y).map (α ≫ β) f⟩ : Edge K _) =
      ⟨j, x, y, (x ⟶[SSet] y).map β ((x ⟶[SSet] y).map α f)⟩
    rw [FunctorToTypes.map_comp_apply]

def graph : SimplicialGraph.{u} := ⟨vertices K, edgeHom K⟩

def edgeι (j : J) (x y : (K.obj j).Obj) :
    (x ⟶[SSet] y) ⟶ edgeHom K (vertexι K j x) (vertexι K j y) where
  app n f := ⟨⟨j, x, y, f⟩, rfl, rfl⟩

def free : SimplicialCat.{u, u} := SimplicialColimitsFree.Paths.simplicialCat (graph K)

def leg (j : J) : underlyingGraph (K.obj j) ⟶ underlyingGraph (free K) :=
  ⟨vertexι K j, fun x y ↦ edgeι K j x y ≫ SimplicialColimitsFree.Paths.inclusion (graph K) _ _⟩

def rawMap (s : Cocone K) (j : J) (x y : (K.obj j).Obj) :
    (x ⟶[SSet] y) ⟶ (vertexDesc K s (vertexι K j x) ⟶[SSet]
      vertexDesc K s (vertexι K j y)) :=
  (s.ι.app j).map x y ≫ eqToHom (by rw [vertexDesc_ι, vertexDesc_ι])

def endpointHomEquality (s : Cocone K) (a b : vertices K)
    {n : SimplexCategoryᵒᵖ} (e : (edgeHom K a b).obj n) :
    (vertexDesc K s (source K e.val) ⟶[SSet] vertexDesc K s (target K e.val)) =
      (vertexDesc K s a ⟶[SSet] vertexDesc K s b) := by
  rw [e.property.1, e.property.2]

def edgeAssignment (s : Cocone K) : graph K ⟶ underlyingGraph s.pt where
  obj := vertexDesc K s
  map a b :=
    { app := fun n e ↦
        (rawMap K s e.val.1 e.val.2.1 e.val.2.2.1 ≫
          eqToHom (endpointHomEquality K s a b e)).app n e.val.2.2.2
      naturality := by
        intro n m α
        funext e
        rcases e with ⟨⟨j, x, y, f⟩, h⟩
        exact congrFun ((rawMap K s j x y ≫
          eqToHom (endpointHomEquality K s a b ⟨⟨j, x, y, f⟩, h⟩)).naturality α) f }

theorem edgeι_edgeAssignment (s : Cocone K) (j : J) (x y : (K.obj j).Obj) :
    edgeι K j x y ≫ (edgeAssignment K s).map _ _ = rawMap K s j x y := by
  ext n f
  simp only [SSet.comp_app]
  change (rawMap K s j x y ≫ eqToHom (by rfl)).app n f = (rawMap K s j x y).app n f
  simp only [eqToHom_refl, Category.comp_id]

def freeLift (s : Cocone K) : free K ⟶ s.pt :=
  SimplicialColimitsFree.lift (edgeAssignment K s)

theorem leg_freeLift (s : Cocone K) (j : J) :
    leg K j ≫ graphForget.map (freeLift K s) = graphForget.map (s.ι.app j) := by
  apply SimplicialGraph.Map.ext' (fun x ↦ vertexDesc_ι K s j x)
  intro x y
  change (edgeι K j x y ≫ SimplicialColimitsFree.Paths.inclusion (graph K) _ _) ≫
    (freeLift K s).map _ _ ≫ _ = _
  rw [Category.assoc, ← Category.assoc (SimplicialColimitsFree.Paths.inclusion _ _ _)]
  dsimp only [freeLift, SimplicialColimitsFree.lift]
  rw [SimplicialColimitsFree.Extension.inclusion_extend]
  rw [← Category.assoc, edgeι_edgeAssignment]
  simp [rawMap, Category.assoc]
  rfl


/-- Intersect the hom kernels of all actual ordinary cocones (an index in Type u+1). -/
def rel (n : SimplexCategoryᵒᵖ) (X Y : (free K).Obj)
    (f g : (X ⟶[SSet.{u}] Y).obj n) : Prop :=
  ∀ s : Cocone K, ((freeLift K s).map X Y).app n f = ((freeLift K s).map X Y).app n g

theorem rel_map {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (X Y : (free K).Obj)
    {f g : (X ⟶[SSet.{u}] Y).obj n} (h : rel K n X Y f g) :
    rel K m X Y ((X ⟶[SSet] Y).map α f) ((X ⟶[SSet] Y).map α g) := by
  intro s
  exact (congrFun (((freeLift K s).map X Y).naturality α) f).trans
    ((congrArg (( (freeLift K s).obj X ⟶[SSet] (freeLift K s).obj Y).map α) (h s)).trans
      (congrFun (((freeLift K s).map X Y).naturality α) g).symm)

theorem map_cast {C D : SimplicialCat.{u, u}} (F : C ⟶ D) {x x' y y' : C.Obj}
    (hx : x = x') (hy : y = y') :
    (eqToHom (by rw [hx, hy]) : (x ⟶[SSet] y) ⟶ (x' ⟶[SSet] y')) ≫ F.map x' y' =
      F.map x y ≫ eqToHom (by rw [hx, hy]) := by
  cases hx
  cases hy
  simp

def legTransport {i j : J} (a : i ⟶ j) (x y : (K.obj i).Obj) :
    SimplicialColimitsFree.Paths.hom (graph K)
      (vertexι K j ((K.map a).obj x)) (vertexι K j ((K.map a).obj y)) ⟶
    SimplicialColimitsFree.Paths.hom (graph K) (vertexι K i x) (vertexι K i y) :=
  eqToHom (by rw [vertexι_naturality K a x, vertexι_naturality K a y])

/-- Diagram edges agree after transporting their two actual colimit endpoints. -/
theorem rel_naturality {i j : J} (a : i ⟶ j) (n : SimplexCategoryᵒᵖ)
    (x y : (K.obj i).Obj) (f : (x ⟶[SSet] y).obj n) :
    rel K n (vertexι K i x) (vertexι K i y)
      (((K.map a).map x y ≫ (leg K j).map _ _ ≫
        legTransport K a x y).app n f)
      (((leg K i).map x y).app n f) := by
  intro s
  have h : graphForget.map (K.map a) ≫ leg K j ≫ graphForget.map (freeLift K s) =
      leg K i ≫ graphForget.map (freeLift K s) := by
    rw [leg_freeLift, leg_freeLift, ← Functor.map_comp, s.w a]
  have hm := SimplicialGraph.Map.congr_map h x y
  change (((K.map a).map x y ≫ (leg K j).map _ _ ≫
      legTransport K a x y) ≫
        (freeLift K s).map _ _).app n f =
      ((leg K i).map x y ≫ (freeLift K s).map _ _).app n f
  dsimp only [legTransport]
  rw [Category.assoc, Category.assoc,
    map_cast (freeLift K s) (vertexι_naturality K a x) (vertexι_naturality K a y)]
  exact congrFun (NatTrans.congr_app hm n) f

/-- The image of an original identity is identified with the free identity. -/
theorem rel_id (j : J) (n : SimplexCategoryᵒᵖ) (X : (K.obj j).Obj) :
    rel K n ((leg K j).obj X) ((leg K j).obj X)
      (((leg K j).map X X).app n ((eId SSet X).app n PUnit.unit))
      ((eId SSet (C := (free K).Obj) ((leg K j).obj X)).app n PUnit.unit) := by
  intro s
  have h : ∀ X : (K.obj j).Obj,
      (((leg K j ≫ graphForget.map (freeLift K s)).map X X).app n
        ((eId SSet X).app n PUnit.unit)) =
      (eId SSet (C := s.pt.Obj)
        ((leg K j ≫ graphForget.map (freeLift K s)).obj X)).app n PUnit.unit := by
    rw [leg_freeLift]
    intro X
    exact congrArg (fun a ↦ a.app n PUnit.unit) ((s.ι.app j).map_id X)
  exact (h X).trans
    (congrArg (fun a ↦ a.app n PUnit.unit) ((freeLift K s).map_id ((leg K j).obj X))).symm

/-- The image of an original composite agrees with composition of its two images. -/
theorem rel_comp (j : J) (n : SimplexCategoryᵒᵖ) (X Y Z : (K.obj j).Obj)
    (f : (X ⟶[SSet.{u}] Y).obj n) (g : (Y ⟶[SSet.{u}] Z).obj n) :
    rel K n ((leg K j).obj X) ((leg K j).obj Z)
      (((leg K j).map X Z).app n ((eComp SSet X Y Z).app n (f, g)))
      ((eComp SSet (C := (free K).Obj)
        ((leg K j).obj X) ((leg K j).obj Y) ((leg K j).obj Z)).app n
        (((leg K j).map X Y).app n f, ((leg K j).map Y Z).app n g)) := by
  intro s
  have h : ∀ (X Y Z : (K.obj j).Obj)
      (f : (X ⟶[SSet.{u}] Y).obj n) (g : (Y ⟶[SSet.{u}] Z).obj n),
      ((leg K j ≫ graphForget.map (freeLift K s)).map X Z).app n
        ((eComp SSet X Y Z).app n (f, g)) =
      (eComp SSet (C := s.pt.Obj) ((leg K j ≫ graphForget.map (freeLift K s)).obj X)
        ((leg K j ≫ graphForget.map (freeLift K s)).obj Y)
        ((leg K j ≫ graphForget.map (freeLift K s)).obj Z)).app n
        (((leg K j ≫ graphForget.map (freeLift K s)).map X Y).app n f,
          ((leg K j ≫ graphForget.map (freeLift K s)).map Y Z).app n g) := by
    rw [leg_freeLift]
    intro X Y Z f g
    exact congrArg (fun a ↦ a.app n (f, g)) ((s.ι.app j).map_comp X Y Z)
  exact (h X Y Z f g).trans (congrArg
    (fun a ↦ a.app n (((leg K j).map X Y).app n f, ((leg K j).map Y Z).app n g))
    ((freeLift K s).map_comp ((leg K j).obj X) ((leg K j).obj Y) ((leg K j).obj Z))).symm


end DaggerModels.SimplicialCat.ColimitKernel
