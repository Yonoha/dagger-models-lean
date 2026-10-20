import NativeGeneratorSpineSimplices
import NativeRootedQuiverPairingData

/-! Every non-root vertex is paired with its actual directed parent edge. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeGeneratorSpineSimplices DaggerNativeRootedQuiverPairingData
universe u
namespace DaggerNativeRootedSpineCells
noncomputable section

variable {W : Type u} [Quiver.{u + 1} W] (D : Data W)

def upper (x : D.Cell) : (spine W) _⦋1⦌ :=
  match D.parent x with
  | ⟨_, Sum.inl e⟩ => edge W e
  | ⟨_, Sum.inr e⟩ => edge W e

def index (x : D.Cell) : Fin 2 :=
  match D.parent x with
  | ⟨_, Sum.inl _⟩ => 1
  | ⟨_, Sum.inr _⟩ => 0

theorem delta_upper (x : D.Cell) : (spine W).δ (index D x) (upper D x) = vertex W x.val := by
  rcases hp : D.parent x with ⟨y, e | e⟩ <;>
    simp only [index, upper, hp, delta_one_edge, delta_zero_edge]

theorem upper_nonDegenerate (x : D.Cell) : upper D x ∈ (spine W).nonDegenerate 1 := by
  rcases hp : D.parent x with ⟨y, e | e⟩ <;>
    simpa only [upper, hp] using edge_nonDegenerate W e

def highVertex (s : (spine W) _⦋1⦌) : W :=
  if D.height s.val.left < D.height s.val.right then s.val.right else s.val.left

theorem high_upper (x : D.Cell) : highVertex D (upper D x) = x.val := by
  have hh := D.parent_height x
  rcases hp : D.parent x with ⟨y, e | e⟩
  · rw [hp] at hh
    change D.height y + 1 = D.height x.val at hh
    simp only [upper, hp, highVertex]
    change (if D.height x.val < D.height y then y else x.val) = x.val
    rw [if_neg (by omega)]
  · rw [hp] at hh
    change D.height y + 1 = D.height x.val at hh
    simp only [upper, hp, highVertex]
    change (if D.height y < D.height x.val then x.val else y) = x.val
    rw [if_pos (by omega)]

theorem upper_injective : Function.Injective (upper D) := by
  intro x y he
  apply Subtype.ext
  exact (high_upper D x).symm.trans ((congrArg (highVertex D) he).trans (high_upper D y))

theorem edge_covered {x y : W} (e : x ⟶ y) : ∃ s : D.Cell, upper D s = edge W e := by
  rcases D.edge_height e with hh | hh
  · let s : D.Cell := ⟨y, D.edge_target_not_root e hh⟩
    have hp : D.parent s = ⟨x, Sum.inr e⟩ := D.parent_eq s _ hh.symm
    exact ⟨s, by simp only [upper, hp]⟩
  · let s : D.Cell := ⟨x, D.edge_source_not_root e hh⟩
    have hp : D.parent s = ⟨y, Sum.inl e⟩ := D.parent_eq s _ hh
    exact ⟨s, by simp only [upper, hp]⟩

end
end DaggerNativeRootedSpineCells
