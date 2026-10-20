import RectangularInverseWitnessData
import NativeIhomHoObjects

/-! All original simplicial operators and ordinary-map vertices respect rectangular squares. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerRectangularInverseWitnessData DaggerNativeIhomHoObjects
open DaggerNativeWalkingRetractionMappingEquivalence
universe u
namespace DaggerRectangularCellOperators

theorem restrict_square {A B A' B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    {n m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    {s : ((ihom A).obj B).obj (op ⦋n⦌)} {t : ((ihom A').obj B').obj (op ⦋n⦌)}
    (h : Square a b s t) :
    Square a b (((ihom A).obj B).map α.op s) (((ihom A').obj B').map α.op t) := by
  change ((ihom A).map b).app (op ⦋m⦌) (((ihom A).obj B).map α.op s) =
    ((MonoidalClosed.pre a).app B').app (op ⦋m⦌) (((ihom A').obj B').map α.op t)
  calc
    ((ihom A).map b).app (op ⦋m⦌) (((ihom A).obj B).map α.op s) =
        ((ihom A).obj B').map α.op (((ihom A).map b).app (op ⦋n⦌) s) :=
      congrFun (((ihom A).map b).naturality α.op) s
    _ = ((ihom A).obj B').map α.op (((MonoidalClosed.pre a).app B').app (op ⦋n⦌) t) :=
      congrArg (fun x ↦ ((ihom A).obj B').map α.op x) h
    _ = ((MonoidalClosed.pre a).app B').app (op ⦋m⦌) (((ihom A').obj B').map α.op t) :=
      (congrFun (((MonoidalClosed.pre a).app B').naturality α.op) t).symm

def vertex {A B : SSet.{u}} (f : A ⟶ B) : ((ihom A).obj B).obj (op ⦋0⦌) :=
  SSet.hoFunctor.obj.equiv _ (homObject f)

theorem vertex_square_iff {A B A' B' : SSet.{u}} (a : A ⟶ A') (b : B ⟶ B')
    (f : A ⟶ B) (g : A' ⟶ B') : Square a b (vertex f) (vertex g) ↔ f ≫ b = a ≫ g := by
  have he : homObject (f ≫ b) = homObject (a ≫ g) ↔ f ≫ b = a ≫ g :=
    (homObjectEquiv A B').injective.eq_iff
  rw [← he]
  constructor
  · intro h
    apply (SSet.hoFunctor.obj.equiv _).injective
    rw [← post_obj f b, ← pre_obj a g, postHoFunctor, preHoFunctor, ho_map_obj, ho_map_obj]
    exact h
  · intro h
    have hv := congrArg (SSet.hoFunctor.obj.equiv ((ihom A).obj B')) h
    rw [← post_obj f b, ← pre_obj a g, postHoFunctor, preHoFunctor,
      ho_map_obj, ho_map_obj] at hv
    exact hv

end DaggerRectangularCellOperators
