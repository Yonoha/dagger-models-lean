import NativePathUnitLiftedQuiver
import Mathlib.Combinatorics.Quiver.Covering

/-! The exact comma-generator graph is a native covering of the original quiver. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeFreePathCompletionQuiverBridge DaggerNativePathUnitLiftedQuiver
universe u
namespace DaggerNativePathUnitQuiverCovering
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V] (d : Quiver.FreeGroupoid V)

def starEquiv (x : Vertex V d) : Quiver.Star x ≃ Quiver.Star x.right where
  toFun := (projection V d).star x
  invFun
    | ⟨y, e⟩ => ⟨⟨y, x.hom ≫ (pathUnit V).map e.toPath⟩, ⟨e, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨y, h⟩, ⟨e, he⟩⟩
    change x.right ⟶ y at e
    change x.hom ≫ (pathUnit V).map e.toPath = h at he
    subst h
    rfl
  right_inv := by rintro ⟨y, e⟩; rfl

def predecessor (x : Vertex V d) {y : V} (e : y ⟶ x.right) : Vertex V d :=
  ⟨y, x.hom ≫ Groupoid.inv ((pathUnit V).map e.toPath)⟩

theorem predecessor_triangle (x : Vertex V d) {y : V} (e : y ⟶ x.right) :
    (predecessor V d x e).hom ≫ (pathUnit V).map e.toPath = x.hom := by
  simp only [predecessor, Category.assoc, Groupoid.inv_comp, Category.comp_id]

def costarEquiv (x : Vertex V d) : Quiver.Costar x ≃ Quiver.Costar x.right where
  toFun := (projection V d).costar x
  invFun
    | ⟨y, e⟩ => ⟨predecessor V d x e, ⟨e, predecessor_triangle V d x e⟩⟩
  left_inv := by
    rintro ⟨⟨y, h⟩, ⟨e, he⟩⟩
    change y ⟶ x.right at e
    change h ≫ (pathUnit V).map e.toPath = x.hom at he
    have hh : x.hom ≫ Groupoid.inv ((pathUnit V).map e.toPath) = h := by
      rw [← he, Category.assoc, Groupoid.comp_inv, Category.comp_id]
    subst h
    rfl
  right_inv := by rintro ⟨y, e⟩; rfl

theorem projection_isCovering : (projection V d).IsCovering :=
  ⟨fun x ↦ (starEquiv V d x).bijective, fun x ↦ (costarEquiv V d x).bijective⟩

theorem projection_pathStar_bijective (x : Vertex V d) :
    Function.Bijective ((projection V d).pathStar x) :=
  (projection_isCovering V d).pathStar_bijective x

end
end DaggerNativePathUnitQuiverCovering
