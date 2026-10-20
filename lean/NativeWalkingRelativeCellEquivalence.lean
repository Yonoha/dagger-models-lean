import NativeWalkingRelativeCellBranches

/-! One exact equivalence between the two full relative cell classes in every degree. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerNativeWalkingRelativeCells DaggerNativeWalkingRelativeCellBranches
open DaggerNativeWalkingBlockRoundTrips
universe u
namespace DaggerNativeWalkingRelativeCellEquivalence
noncomputable section

def upper {n d : ℕ} (x : LowerCell.{u} n d) : UpperCell.{u} n d :=
  if ha : level x.val < Fin.last (n + 1) then
    let ht : lastTag x.val = true := by simpa only [endTag, if_pos ha] using x.property
    ⟨upTerminal x.val ha ht, upTerminal_tag x.val ha ht⟩
  else
    let ht : firstTag x.val = true := by simpa only [endTag, if_neg ha] using x.property
    ⟨upInitial x.val ha ht, upInitial_tag x.val ha ht⟩

def lower {n d : ℕ} (x : UpperCell.{u} n d) : LowerCell.{u} n d :=
  if ha : level x.val < Fin.last (n + 1) then
    let ht : lastTag x.val = false := by simpa only [endTag, if_pos ha] using x.property
    ⟨downTerminal x.val ha ht, downTerminal_tag x.val ha ht⟩
  else
    let ht : firstTag x.val = false := by simpa only [endTag, if_neg ha] using x.property
    ⟨downInitial x.val ha ht, downInitial_tag x.val ha ht⟩

theorem upper_level {n d : ℕ} (x : LowerCell.{u} n d) : level (upper x).val = level x.val := by
  unfold upper
  split_ifs with ha
  · exact upTerminal_level x.val ha
      (by simpa only [endTag, if_pos ha] using x.property)
  · exact upInitial_level x.val ha
      (by simpa only [endTag, if_neg ha] using x.property)

theorem lower_level {n d : ℕ} (x : UpperCell.{u} n d) : level (lower x).val = level x.val := by
  unfold lower
  split_ifs with ha
  · exact downTerminal_level x.val ha
      (by simpa only [endTag, if_pos ha] using x.property)
  · exact downInitial_level x.val ha
      (by simpa only [endTag, if_neg ha] using x.property)

theorem upper_val_terminal {n d : ℕ} (x : LowerCell.{u} n d)
    (ha : level x.val < Fin.last (n + 1)) (ht : lastTag x.val = true) :
    (upper x).val = upTerminal x.val ha ht := by simp only [upper, dif_pos ha]

theorem upper_val_initial {n d : ℕ} (x : LowerCell.{u} n d)
    (ha : ¬level x.val < Fin.last (n + 1)) (ht : firstTag x.val = true) :
    (upper x).val = upInitial x.val ha ht := by simp only [upper, dif_neg ha]

theorem lower_val_terminal {n d : ℕ} (x : UpperCell.{u} n d)
    (ha : level x.val < Fin.last (n + 1)) (ht : lastTag x.val = false) :
    (lower x).val = downTerminal x.val ha ht := by simp only [lower, dif_pos ha]

theorem lower_val_initial {n d : ℕ} (x : UpperCell.{u} n d)
    (ha : ¬level x.val < Fin.last (n + 1)) (ht : firstTag x.val = false) :
    (lower x).val = downInitial x.val ha ht := by simp only [lower, dif_neg ha]

theorem lower_upper {n d : ℕ} (x : LowerCell.{u} n d) : lower (upper x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  by_cases ha : level x.val < Fin.last (n + 1)
  · have han : level (upper x).val < Fin.last (n + 1) := (upper_level x).trans_lt ha
    simp only [lower, upper, dif_pos ha, upTerminal_level]
    exact terminalLower_terminalUpper x.val.val (true_exists x.val)
      (projection_surjective x.val) ha _
  · have han : ¬level (upper x).val < Fin.last (n + 1) := by rw [upper_level]; exact ha
    simp only [lower, upper, dif_neg ha, upInitial_level]
    exact initialLower_initialUpper x.val.val (true_exists x.val)
      (projection_surjective x.val) (initial_level_pos x.val ha) _

theorem upper_lower {n d : ℕ} (x : UpperCell.{u} n d) : upper (lower x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  by_cases ha : level x.val < Fin.last (n + 1)
  · have han : level (lower x).val < Fin.last (n + 1) := (lower_level x).trans_lt ha
    have ht : lastTag x.val = false := by simpa only [endTag, if_pos ha] using x.property
    simp only [upper, lower, dif_pos ha, downTerminal_level]
    exact terminalUpper_terminalLower x.val.val (true_exists x.val) x.val.property.1 ht
      _ _ ((downTerminal_level x.val ha ht).trans_lt ha)
  · have han : ¬level (lower x).val < Fin.last (n + 1) := by rw [lower_level]; exact ha
    have ht : firstTag x.val = false := by simpa only [endTag, if_neg ha] using x.property
    simp only [upper, lower, dif_neg ha, downInitial_level]
    exact initialUpper_initialLower x.val.val (true_exists x.val) x.val.property.1 ht
      _ _ (initial_level_pos (downInitial x.val ha ht) (by rw [downInitial_level]; exact ha))

def cellEquivalence (n d : ℕ) : LowerCell.{u} n d ≃ UpperCell.{u} n d where
  toFun := upper
  invFun := lower
  left_inv := lower_upper
  right_inv := upper_lower

end
end DaggerNativeWalkingRelativeCellEquivalence
