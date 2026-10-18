import NativeHoOppositeIso
import NativeCatEquivalenceWeakProperties

/-!
# Native homotopy-category equivalences under simplicial opposite

Use the actual natural comparison and Mathlib's equivalence op/unop operations.
Cancellation is applied to the exact naturality square, retaining the original maps.
-/
set_option autoImplicit false
open CategoryTheory
universe v u
namespace DaggerNativeHoOppositeEquivalence

/-- Native ordinary functor equivalence is unchanged by categorical opposite. -/
theorem catEquivalence_op_iff {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : F.IsEquivalence ↔ F.op.IsEquivalence := by
  constructor
  · intro h
    letI : F.IsEquivalence := h
    infer_instance
  · intro h
    letI : F.op.IsEquivalence := h
    exact show F.op.asEquivalence.unop.functor.IsEquivalence by infer_instance

/-- The native homotopy-category equivalence test is invariant under actual simplicial opposite. -/
theorem ho_op_isEquivalence_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    (SSet.hoFunctor.map (SSet.opFunctor.map f)).toFunctor.IsEquivalence ↔
      (SSet.hoFunctor.map f).toFunctor.IsEquivalence := by
  let eX := DaggerNativeHoOppositeIso.hoOppositeIso.app X
  let eY := DaggerNativeHoOppositeIso.hoOppositeIso.app Y
  let F := (SSet.hoFunctor.map f).toFunctor
  let G := (SSet.hoFunctor.map (SSet.opFunctor.map f)).toFunctor
  letI : eX.hom.toFunctor.IsEquivalence :=
    show (Cat.equivOfIso eX).functor.IsEquivalence by infer_instance
  letI : eY.hom.toFunctor.IsEquivalence :=
    show (Cat.equivOfIso eY).functor.IsEquivalence by infer_instance
  have hn : G ⋙ eY.hom.toFunctor = eX.hom.toFunctor ⋙ F.op :=
    congrArg (fun k ↦ k.toFunctor)
      (DaggerNativeHoOppositeIso.hoOppositeIso.hom.naturality f)
  constructor
  · intro h
    letI : G.IsEquivalence := h
    letI : (eX.hom.toFunctor ⋙ F.op).IsEquivalence := by
      rw [← hn]
      infer_instance
    have hop : F.op.IsEquivalence :=
      CategoryTheory.Functor.isEquivalence_of_comp_left eX.hom.toFunctor F.op
    exact (catEquivalence_op_iff F).2 hop
  · intro h
    letI : F.IsEquivalence := h
    letI : F.op.IsEquivalence := (catEquivalence_op_iff F).1 h
    letI : (G ⋙ eY.hom.toFunctor).IsEquivalence := by
      rw [hn]
      infer_instance
    exact CategoryTheory.Functor.isEquivalence_of_comp_right G eY.hom.toFunctor

end DaggerNativeHoOppositeEquivalence
