import NativeWalkingRelativeCells

/-! The four verified block branches on actual relative nondegenerate cells. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordBlocks
open DaggerNativeWalkingBlockLowerExtensions DaggerNativeWalkingBlockUpperDeletions
open DaggerNativeWalkingBlockInsertedBoundary DaggerNativeWalkingMarkedWordOperators
open DaggerNativeWalkingRelativeCells
universe u
namespace DaggerNativeWalkingRelativeCellBranches
noncomputable section

def lastTag {n d : ℕ} (x : Cell.{u} n d) : Bool :=
  ((coordinates x.val).val (lastActive (coordinates x.val) (true_exists x))).2

def firstTag {n d : ℕ} (x : Cell.{u} n d) : Bool :=
  ((coordinates x.val).val (firstActive (coordinates x.val) (true_exists x))).2

def upTerminal {n d : ℕ} (x : Cell.{u} n (d + 1))
    (ha : level x < Fin.last (n + 1)) (ht : lastTag x = true) : Cell.{u} n (d + 2) :=
  ⟨terminalUpper x.val (true_exists x) (projection_surjective x) ha,
    terminalUpper_nonDegenerate x.val (true_exists x) (projection_surjective x) ha ht x.property.1,
    terminalUpper_relative x.val (true_exists x) (projection_surjective x) ha x.property.2⟩

theorem upTerminal_level {n d : ℕ} (x : Cell.{u} n (d + 1))
    (ha : level x < Fin.last (n + 1)) (ht : lastTag x = true) :
    level (upTerminal x ha ht) = level x :=
  (terminalUpper_boundary x.val (true_exists x) (projection_surjective x) ha
    (true_exists (upTerminal x ha ht))).1

theorem upTerminal_tag {n d : ℕ} (x : Cell.{u} n (d + 1))
    (ha : level x < Fin.last (n + 1)) (ht : lastTag x = true) :
    endTag (upTerminal x ha ht) = false := by
  have hb := terminalUpper_boundary x.val (true_exists x) (projection_surjective x) ha
    (true_exists (upTerminal x ha ht))
  have hh : level (upTerminal x ha ht) < Fin.last (n + 1) :=
    (upTerminal_level x ha ht).trans_lt ha
  simpa only [endTag, if_pos hh] using hb.2.2

def upInitial {n d : ℕ} (x : Cell.{u} n (d + 1))
    (ha : ¬level x < Fin.last (n + 1)) (ht : firstTag x = true) : Cell.{u} n (d + 2) :=
  ⟨initialUpper x.val (true_exists x) (projection_surjective x) (initial_level_pos x ha),
    initialUpper_nonDegenerate x.val (true_exists x) (projection_surjective x)
      (initial_level_pos x ha) ht x.property.1,
    initialUpper_relative x.val (true_exists x) (projection_surjective x)
      (initial_level_pos x ha) x.property.2⟩

theorem upInitial_level {n d : ℕ} (x : Cell.{u} n (d + 1))
    (ha : ¬level x < Fin.last (n + 1)) (ht : firstTag x = true) :
    level (upInitial x ha ht) = level x :=
  (initialUpper_boundary x.val (true_exists x) (projection_surjective x) (initial_level_pos x ha)
    (true_exists (upInitial x ha ht))).1

theorem upInitial_tag {n d : ℕ} (x : Cell.{u} n (d + 1))
    (ha : ¬level x < Fin.last (n + 1)) (ht : firstTag x = true) :
    endTag (upInitial x ha ht) = false := by
  have hb := initialUpper_boundary x.val (true_exists x) (projection_surjective x)
    (initial_level_pos x ha) (true_exists (upInitial x ha ht))
  have hh : ¬level (upInitial x ha ht) < Fin.last (n + 1) := by
    rw [upInitial_level]
    exact ha
  simpa only [endTag, if_neg hh] using hb.2.2

def downTerminal {n d : ℕ} (x : Cell.{u} n (d + 2))
    (ha : level x < Fin.last (n + 1)) (ht : lastTag x = false) : Cell.{u} n (d + 1) :=
  ⟨terminalLower x.val (true_exists x),
    terminalLower_nonDegenerate x.val (true_exists x) (projection_surjective x) ha ht x.property.1,
    terminalLower_relative x.val (true_exists x) (projection_surjective x) ht⟩

theorem downTerminal_level {n d : ℕ} (x : Cell.{u} n (d + 2))
    (ha : level x < Fin.last (n + 1)) (ht : lastTag x = false) :
    level (downTerminal x ha ht) = level x :=
  active_delete_false (coordinates x.val) (true_exists x) _ ht
    (true_exists (downTerminal x ha ht))

theorem downTerminal_tag {n d : ℕ} (x : Cell.{u} n (d + 2))
    (ha : level x < Fin.last (n + 1)) (ht : lastTag x = false) :
    endTag (downTerminal x ha ht) = true := by
  have hb := terminalLower_boundary x.val (true_exists x) x.property.1 ht
    (true_exists (downTerminal x ha ht))
  have hh : level (downTerminal x ha ht) < Fin.last (n + 1) :=
    (downTerminal_level x ha ht).trans_lt ha
  simpa only [endTag, if_pos hh] using hb.2

def downInitial {n d : ℕ} (x : Cell.{u} n (d + 2))
    (ha : ¬level x < Fin.last (n + 1)) (ht : firstTag x = false) : Cell.{u} n (d + 1) :=
  ⟨initialLower x.val (true_exists x),
    initialLower_nonDegenerate x.val (true_exists x) (projection_surjective x)
      (initial_level_pos x ha) ht x.property.1,
    initialLower_relative x.val (true_exists x) (projection_surjective x) ht⟩

theorem downInitial_level {n d : ℕ} (x : Cell.{u} n (d + 2))
    (ha : ¬level x < Fin.last (n + 1)) (ht : firstTag x = false) :
    level (downInitial x ha ht) = level x :=
  active_delete_false (coordinates x.val) (true_exists x) _ ht
    (true_exists (downInitial x ha ht))

theorem downInitial_tag {n d : ℕ} (x : Cell.{u} n (d + 2))
    (ha : ¬level x < Fin.last (n + 1)) (ht : firstTag x = false) :
    endTag (downInitial x ha ht) = true := by
  have hb := initialLower_boundary x.val (true_exists x) x.property.1 ht
    (true_exists (downInitial x ha ht))
  have hh : ¬level (downInitial x ha ht) < Fin.last (n + 1) := by
    rw [downInitial_level]
    exact ha
  simpa only [endTag, if_neg hh] using hb.2

end
end DaggerNativeWalkingRelativeCellBranches
