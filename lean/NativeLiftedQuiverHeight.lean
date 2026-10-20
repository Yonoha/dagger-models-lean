import NativePathUnitQuiverCovering
import NativeReducedPathEdgeExtension

/-! The native lifted graph has an exact root height and every original edge changes it by one. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeFreePathCompletionQuiverBridge DaggerNativePathUnitLiftedQuiver
open DaggerNativeFreeGroupoidWordLabels DaggerNativeFreeGroupoidNormalPath
open DaggerNativeReducedPathEdgeExtension
universe u
namespace DaggerNativeLiftedQuiverHeight
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V] (a : V)

def root : Vertex V ((pathUnit V).obj (show Paths V from a)) := ⟨a, 𝟙 _⟩

def height (x : Vertex V ((pathUnit V).obj (show Paths V from a))) : ℕ :=
  norm V (a := (show Quiver.Symmetrify V from a))
    (b := (show Quiver.Symmetrify V from x.right)) x.hom

theorem height_root : height V a (root V a) = 0 :=
  norm_id V (show Quiver.Symmetrify V from a)

theorem path_unit_generator {x y : V} (e : x ⟶ y) :
    (pathUnit V).map e.toPath = (quotientMap V).map e.toPosPath := by
  exact Paths.lift_toPath _ _

theorem height_edge {x y : Vertex V ((pathUnit V).obj (show Paths V from a))} (e : x ⟶ y) :
    height V a y = height V a x + 1 ∨ height V a y + 1 = height V a x := by
  have h := norm_comp_edge_changes_by_one V
    (a := (show Quiver.Symmetrify V from a))
    (b := (show Quiver.Symmetrify V from x.right))
    (c := (show Quiver.Symmetrify V from y.right)) x.hom e.val.toPos
  have he := e.property
  rw [path_unit_generator] at he
  rw [he] at h
  exact h

theorem edge_ne_self (x : Vertex V ((pathUnit V).obj (show Paths V from a))) : IsEmpty (x ⟶ x) :=
  ⟨fun e ↦ by have h := height_edge V a e; omega⟩

theorem height_zero_iff (x : Vertex V ((pathUnit V).obj (show Paths V from a))) :
    height V a x = 0 ↔ x = root V a := by
  constructor
  · intro hx
    rcases x with ⟨b, f⟩
    let p := normalPath V (a := (show Quiver.Symmetrify V from a))
      (b := (show Quiver.Symmetrify V from b)) f
    have hl : p.length = 0 := hx
    have hab : a = b := Quiver.Path.eq_of_length_zero (V := Quiver.Symmetrify V) p hl
    subst b
    have hp : p = Quiver.Path.nil :=
      Quiver.Path.eq_nil_of_length_zero (V := Quiver.Symmetrify V) p hl
    have hf := quotient_normalPath V f
    change (quotientMap V).map p = f at hf
    rw [hp] at hf
    change 𝟙 _ = f at hf
    subst f
    rfl
  · rintro rfl
    exact height_root V a

end
end DaggerNativeLiftedQuiverHeight
