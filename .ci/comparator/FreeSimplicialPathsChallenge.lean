import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.Combinatorics.Quiver.Symmetric
/-! Part I `bg.lem.presentable`: actual finite words and their ordinary simplicial dagger.
Proof placeholders specify obligations; the data definitions are fixed explicitly. -/
set_option warningAsError false
open CategoryTheory MonoidalCategory BraidedCategory
universe u v
namespace DaggerModels
noncomputable instance sSetBraidedCategory : BraidedCategory SSet.{v} :=
  .ofCartesianMonoidalCategory
structure DaggerSimplicialGraph where
  Obj : Type u
  Hom : Obj → Obj → SSet.{u}
  dagger : ∀ x y, Hom x y ⟶ Hom y x
  dagger_involutive : ∀ x y, dagger x y ≫ dagger y x = 𝟙 (Hom x y)
namespace DaggerSimplicialGraph
@[simp] theorem dagger_app_involutive (G : DaggerSimplicialGraph.{u}) (x y : G.Obj)
    (n : SimplexCategoryᵒᵖ) (e : (G.Hom x y).obj n) :
    (G.dagger y x).app n ((G.dagger x y).app n e) = e := by
  have h := congrArg (fun f : G.Hom x y ⟶ G.Hom x y ↦ f.app n e)
    (G.dagger_involutive x y)
  exact h
end DaggerSimplicialGraph
namespace FreeSimplicialPaths
def At (G : DaggerSimplicialGraph.{u}) (_n : SimplexCategoryᵒᵖ) : Type u := G.Obj
def quiverAt (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) : Quiver G.Obj where
  Hom x y := (G.Hom x y).obj n
instance (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) : Quiver (At G n) :=
  quiverAt G n
instance (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :
    Quiver.HasInvolutiveReverse (At G n) where
  reverse' := fun {x y} e ↦ (G.dagger x y).app n e
  inv' := fun {x y} e ↦ G.dagger_app_involutive x y n e
abbrev Path (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) (x y : G.Obj) : Type u :=
  @Quiver.Path (At G n) (quiverAt G n) x y
def operator (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    At G m ⥤q At G n where
  obj := id
  map := fun {x y} e ↦ (G.Hom x y).map f e
def map (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    {x y : G.Obj} (p : Path G m x y) : Path G n x y := (operator G f).mapPath p
@[simp] theorem map_cons (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) {x y z : G.Obj} (p : Path G m x y) (e : (G.Hom y z).obj m) :
    map G f (p.cons e) = (map G f p).cons ((G.Hom y z).map f e) := by sorry
@[simp] theorem map_id (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y : G.Obj} (p : Path G n x y) : map G (𝟙 n) p = p := by sorry
@[simp] theorem map_comp (G : DaggerSimplicialGraph.{u}) {l m n : SimplexCategoryᵒᵖ}
    (f : l ⟶ m) (g : m ⟶ n) {x y : G.Obj} (p : Path G l x y) :
    map G (f ≫ g) p = map G g (map G f p) := by sorry
@[simp] theorem map_pathComp (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) {x y z : G.Obj} (p : Path G m x y) (q : Path G m y z) :
    map G f (p.comp q) = (map G f p).comp (map G f q) := by sorry

def hom (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) : SSet.{u} where
  obj n := Path G n x y
  map f := map G f
  map_id n := by funext p; exact map_id G n p
  map_comp f g := by funext p; exact map_comp G f g p
def inclusion (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) : G.Hom x y ⟶ hom G x y where
  app n e := @Quiver.Hom.toPath (At G n) (quiverAt G n) x y e
  naturality _ _ _ := rfl
def id (G : DaggerSimplicialGraph.{u}) (x : G.Obj) : 𝟙_ SSet.{u} ⟶ hom G x x where
  app _ _ := Quiver.Path.nil
  naturality _ _ _ := rfl
def comp (G : DaggerSimplicialGraph.{u}) (x y z : G.Obj) :
    hom G x y ⊗ hom G y z ⟶ hom G x z where
  app _ p := p.1.comp p.2
  naturality m n f := by
    funext p
    exact (map_pathComp G f p.1 p.2).symm

def reverse (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y : G.Obj} (p : Path G n x y) : Path G n y x := p.reverse
@[simp] theorem reverse_comp (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y z : G.Obj} (p : Path G n x y) (q : Path G n y z) :
    reverse G n (p.comp q) = (reverse G n q).comp (reverse G n p) := by sorry
@[simp] theorem reverse_involutive (G : DaggerSimplicialGraph.{u})
    (n : SimplexCategoryᵒᵖ) {x y : G.Obj} (p : Path G n x y) :
    reverse G n (reverse G n p) = p := by sorry
@[simp] theorem map_reverse (G : DaggerSimplicialGraph.{u})
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) {x y : G.Obj} (p : Path G m x y) :
    map G f (reverse G m p) = reverse G n (map G f p) := by sorry

def dagger (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) : hom G x y ⟶ hom G y x where
  app n := reverse G n
  naturality m n f := by
    funext p
    exact (map_reverse G f p).symm
@[simp] theorem dagger_involutive (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    dagger G x y ≫ dagger G y x = 𝟙 (hom G x y) := by sorry
@[simp] theorem inclusion_dagger (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    inclusion G x y ≫ dagger G x y = G.dagger x y ≫ inclusion G y x := by sorry
@[simp] theorem id_dagger (G : DaggerSimplicialGraph.{u}) (x : G.Obj) :
    id G x ≫ dagger G x x = id G x := by sorry
theorem comp_dagger (G : DaggerSimplicialGraph.{u}) (x y z : G.Obj) :
    comp G x y z ≫ dagger G x z =
      (dagger G x y ⊗ₘ dagger G y z) ≫
        (β_ (hom G y x) (hom G z y)).hom ≫ comp G z y x := by sorry
end FreeSimplicialPaths
end DaggerModels
