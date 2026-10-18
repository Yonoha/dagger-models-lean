import NativeWalkingBlockRoundTrips
import NativeWalkingBlockInnerIndices

/-! The full original relative nondegenerate-cell space and its computed two-class partition. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingSimplexWords
open DaggerNativeWalkingWordBlocks DaggerNativeWalkingBlockInnerIndices
universe u
namespace DaggerNativeWalkingRelativeCells
noncomputable section

def ambient (n : ℕ) : SSet.{u} := Δ[n + 1] ⊗ J.{u}

def relative (n : ℕ) : (ambient.{u} n).Subcomplex :=
  (SSet.boundary (n + 1)).unionProd DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}

def Cell (n d : ℕ) :=
  {x : (ambient.{u} n) _⦋d⦌ // x ∈ (ambient.{u} n).nonDegenerate d ∧ x ∉ (relative n).obj _}

def toN {n d : ℕ} (x : Cell.{u} n d) : (relative.{u} n).N :=
  SSet.Subcomplex.N.mk x.val x.property.1 x.property.2

def cellEquiv (n : ℕ) : (relative.{u} n).N ≃ Σ d, Cell.{u} n d where
  toFun x := ⟨x.dim, x.simplex, x.nonDegenerate, x.notMem⟩
  invFun x := toN x.2
  left_inv x := by
    obtain ⟨d, x, hx, hr, rfl⟩ := x.mk_surjective
    rfl
  right_inv x := by cases x; rfl

theorem projection_surjective {n d : ℕ} (x : Cell.{u} n d) :
    Function.Surjective (fun k ↦ ((coordinates x.val).val k).1) :=
  ((notMem_relative_iff x.val).mp x.property.2).1

theorem true_exists {n d : ℕ} (x : Cell.{u} n d) :
    ∃ k, ((coordinates x.val).val k).2 = true :=
  ((notMem_relative_iff x.val).mp x.property.2).2

def level {n d : ℕ} (x : Cell.{u} n d) : Fin (n + 2) :=
  active (coordinates x.val) (true_exists x)

def endTag {n d : ℕ} (x : Cell.{u} n d) : Bool :=
  if level x < Fin.last (n + 1) then
    ((coordinates x.val).val (lastActive (coordinates x.val) (true_exists x))).2
  else ((coordinates x.val).val (firstActive (coordinates x.val) (true_exists x))).2

def LowerCell (n d : ℕ) := {x : Cell.{u} n (d + 1) // endTag x = true}
def UpperCell (n d : ℕ) := {x : Cell.{u} n (d + 2) // endTag x = false}

theorem dim_bound {n d : ℕ} (x : Cell.{u} n d) : n + 1 ≤ d := by
  have hh := Fintype.card_le_of_surjective _ (projection_surjective x)
  simp only [Fintype.card_fin] at hh
  omega

theorem not_terminal_level {n d : ℕ} (x : Cell.{u} n d)
    (hx : ¬level x < Fin.last (n + 1)) : level x = Fin.last (n + 1) :=
  le_antisymm (Fin.le_last _) (le_of_not_gt hx)

theorem initial_level_pos {n d : ℕ} (x : Cell.{u} n d)
    (hx : ¬level x < Fin.last (n + 1)) : 0 < level x := by
  rw [not_terminal_level x hx]
  change 0 < n + 1
  omega

theorem upper_dim_bound {n d : ℕ} (x : Cell.{u} n d) (ht : endTag x = false) : 2 ≤ d := by
  by_cases hx : level x < Fin.last (n + 1)
  · have hb : ((coordinates x.val).val
        (lastActive (coordinates x.val) (true_exists x))).2 = false := by
      simpa only [endTag, if_pos hx] using ht
    have hi := terminal_deletion (coordinates x.val) (true_exists x)
      (projection_surjective x) hx hb
    have h0 := Fin.pos_iff_ne_zero.mpr hi.1
    have hl := Fin.lt_last_iff_ne_last.mpr hi.2
    change 0 < (lastActive (coordinates x.val) (true_exists x)).val at h0
    change (lastActive (coordinates x.val) (true_exists x)).val < d at hl
    omega
  · have hb : ((coordinates x.val).val
        (firstActive (coordinates x.val) (true_exists x))).2 = false := by
      simpa only [endTag, if_neg hx] using ht
    have hi := initial_deletion (coordinates x.val) (true_exists x)
      (projection_surjective x) (initial_level_pos x hx) hb
    have h0 := Fin.pos_iff_ne_zero.mpr hi.1
    have hl := Fin.lt_last_iff_ne_last.mpr hi.2
    change 0 < (firstActive (coordinates x.val) (true_exists x)).val at h0
    change (firstActive (coordinates x.val) (true_exists x)).val < d at hl
    omega

end
end DaggerNativeWalkingRelativeCells
