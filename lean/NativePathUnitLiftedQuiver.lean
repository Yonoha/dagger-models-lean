import NativeFreePathCompletionQuiverBridge
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! The full lifted quiver retains the actual unit-comma objects and generator triangles. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeFreePathCompletionQuiverBridge
universe u
namespace DaggerNativePathUnitLiftedQuiver
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V] (d : Quiver.FreeGroupoid V)

structure Vertex where
  right : V
  hom : d ⟶ (pathUnit V).obj (show Paths V from right)

instance vertexQuiver : Quiver.{u + 1} (Vertex V d) where
  Hom x y := {e : x.right ⟶ y.right // x.hom ≫ (pathUnit V).map e.toPath = y.hom}

def projection : Vertex V d ⥤q V where
  obj x := x.right
  map e := e.val

def commaVertex (x : Vertex V d) : StructuredArrow d (pathUnit V) :=
  StructuredArrow.mk x.hom

def vertexOfComma (x : StructuredArrow d (pathUnit V)) : Vertex V d := ⟨x.right, x.hom⟩

theorem vertex_comma (x : Vertex V d) : vertexOfComma V d (commaVertex V d x) = x := rfl

theorem comma_vertex (x : StructuredArrow d (pathUnit V)) :
    commaVertex V d (vertexOfComma V d x) = x := rfl

def commaGenerators : Vertex V d ⥤q StructuredArrow d (pathUnit V) where
  obj := commaVertex V d
  map e := StructuredArrow.homMk e.val.toPath e.property

def commaFunctor : Paths (Vertex V d) ⥤ StructuredArrow d (pathUnit V) :=
  Paths.lift (commaGenerators V d)

def forgetPaths : Paths (Vertex V d) ⥤ Paths V :=
  Paths.lift (projection V d ⋙q Paths.of V)

theorem commaFunctor_projection :
    commaFunctor V d ⋙ StructuredArrow.proj d (pathUnit V) = forgetPaths V d := by
  refine Paths.ext_functor (F := commaFunctor V d ⋙ StructuredArrow.proj d (pathUnit V))
    (G := forgetPaths V d) rfl ?_
  intro a b e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  simp only [commaFunctor, forgetPaths, CategoryTheory.Functor.comp_map,
    Paths.lift_toPath]
  rfl

theorem forgetPaths_map {x y : Vertex V d} (p : Quiver.Path x y) :
    (forgetPaths V d).map p = (projection V d).mapPath p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change ((forgetPaths V d).map p).cons e.val = _
    rw [ih]
    rfl

theorem commaFunctor_map_right {x y : Vertex V d} (p : Quiver.Path x y) :
    ((commaFunctor V d).map p).right = (projection V d).mapPath p := by
  have h := CategoryTheory.Functor.congr_hom (commaFunctor_projection V d) p
  have h' : ((commaFunctor V d).map p).right = (forgetPaths V d).map p := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h
  exact h'.trans (forgetPaths_map V d p)

end
end DaggerNativePathUnitLiftedQuiver
