import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! Part I `dj.not.adjunctions`: the exact gluing, adjunction unit, and swap equations. -/
set_option warningAsError false
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
universe u
namespace DaggerModels

structure DaggerSSet where
  toSSet : SSet.{u}
  dagger : toSSet ⟶ toSSet.op
  involutive (n : ℕ) (x : toSSet _⦋n⦌) :
    SSet.opObjEquiv (dagger.app (op ⦋n⦌)
      (SSet.opObjEquiv (dagger.app (op ⦋n⦌) x))) = x
  fixedVertices (x : toSSet _⦋0⦌) : SSet.opObjEquiv (dagger.app (op ⦋0⦌) x) = x
namespace DaggerSSet
structure Hom (X Y : DaggerSSet.{u}) where
  hom : X.toSSet ⟶ Y.toSSet
  comm : hom ≫ Y.dagger = X.dagger ≫ SSet.opFunctor.map hom
@[ext] theorem Hom.ext {X Y : DaggerSSet.{u}} {f g : Hom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl
instance : Category DaggerSSet.{u} where
  Hom := Hom
  id X := ⟨𝟙 X.toSSet, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm,
      Category.assoc, Functor.map_comp]⟩
  id_comp f := by apply Hom.ext; simp
  comp_id f := by apply Hom.ext; simp
  assoc f g h := by apply Hom.ext; simp [Category.assoc]
def forget : DaggerSSet.{u} ⥤ SSet.{u} where
  obj X := X.toSSet
  map f := f.hom
end DaggerSSet

namespace SSetVertices
def obj (A : SSet.{u}) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (A.obj (op ⦋0⦌))
def inclusion (A : SSet.{u}) : obj A ⟶ A where
  app n x := A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x
  naturality {n m} f := by
    funext x
    change A.map (SimplexCategory.const m.unop ⦋0⦌ 0).op x =
      A.map f.unop.op (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x)
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [SimplexCategory.eq_const_to_zero (f.unop ≫ SimplexCategory.const n.unop ⦋0⦌ 0)]
def opInclusion (A : SSet.{u}) : obj A ⟶ A.op where
  app n x := SSet.opObjEquiv.symm
    (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x)
  naturality {n m} f := by
    funext x
    change A.map (SimplexCategory.const m.unop ⦋0⦌ 0).op x =
      A.map (SimplexCategory.rev.map f.unop).op
        (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x)
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [SimplexCategory.eq_const_to_zero
      (SimplexCategory.rev.map f.unop ≫ SimplexCategory.const n.unop ⦋0⦌ 0)]
    rfl
end SSetVertices

theorem freeDagger_pushout (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget.{u}) :
    ∃ r : SSet.opFunctor ⟶ F ⋙ DaggerSSet.forget, ∀ A,
      IsPushout (SSetVertices.inclusion A) (SSetVertices.opInclusion A)
        (adj.unit.app A) (r.app A) ∧
      (adj.unit.app A ≫ (F.obj A).dagger =
        (SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map (r.app A)) ∧
      (r.app A ≫ (F.obj A).dagger = SSet.opFunctor.map (adj.unit.app A)) := by sorry

theorem freeDagger_skeleton_pushout (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget.{u}) :
    ∃ r : SSet.opFunctor ⟶ F ⋙ DaggerSSet.forget, ∀ A,
      ∃ e : SSetVertices.obj A ≅ (A.skeleton 1).toSSet,
        e.hom ≫ (A.skeleton 1).ι = SSetVertices.inclusion A ∧
        IsPushout (A.skeleton 1).ι (e.inv ≫ SSetVertices.opInclusion A)
          (adj.unit.app A) (r.app A) ∧
        (adj.unit.app A ≫ (F.obj A).dagger =
          (SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map (r.app A)) ∧
        (r.app A ≫ (F.obj A).dagger = SSet.opFunctor.map (adj.unit.app A)) := by sorry

end DaggerModels
