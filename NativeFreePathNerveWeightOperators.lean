import NativeFreePathNerveWeight

/-! Exact native face and degeneracy weights for the free-category generator-spine matching. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeFreePathNerveWeight
universe u
namespace DaggerNativeFreePathNerveWeightOperators
noncomputable section

variable {V : Type u} [Quiver.{u + 1} V]

theorem segment_length_congr {n : ℕ} (c : ComposableArrows (Paths V) n)
    {i j i' j' : Fin (n + 1)} (f : i ⟶ j) (g : i' ⟶ j') (hi : i = i') (hj : j = j') :
    (c.map f).length = (c.map g).length := by
  subst i'
  subst j'
  exact congrArg (fun h : i ⟶ j ↦ (c.map h).length) (Subsingleton.elim f g)

theorem weight_whisker_eq_of_endpoints {m n : ℕ} (c : ComposableArrows (Paths V) n)
    (φ : Fin (m + 1) ⥤ Fin (n + 1)) (h₀ : φ.obj 0 = 0)
    (h₁ : φ.obj (Fin.last m) = Fin.last n) : weight (φ ⋙ c) = weight c :=
  segment_length_congr c (φ.map (homOfLE (Fin.zero_le (Fin.last m))))
    (homOfLE (Fin.zero_le (Fin.last n))) h₀ h₁

theorem weight_precomp {n : ℕ} (c : ComposableArrows (Paths V) n) {X : Paths V}
    (f : X ⟶ c.left) : weight (c.precomp f) = f.length + weight c := by
  cases n with
  | zero =>
    change f.length = f.length + (c.map (𝟙 (0 : Fin 1))).length
    rw [c.map_id]
    rfl
  | succ n =>
    change (f.comp (totalPath c)).length = f.length + (totalPath c).length
    exact Quiver.Path.length_comp f _

theorem weight_delta_zero {n : ℕ} (c : ComposableArrows (Paths V) (n + 1)) :
    weight c = (c.map' 0 1).length + weight ((nerve (Paths V)).δ 0 c) := by
  obtain ⟨c, X, f, rfl⟩ := ComposableArrows.precomp_surjective c
  change weight (c.precomp f) = f.length + weight c
  exact weight_precomp c f

theorem weight_delta_zero_lt {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (h : 0 < (c.map' 0 1).length) : weight ((nerve (Paths V)).δ 0 c) < weight c := by
  have he := weight_delta_zero c
  omega

theorem weight_delta_inner {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (i : Fin (n + 2)) (h₀ : i ≠ 0) (h₁ : i ≠ Fin.last (n + 1)) :
    weight ((nerve (Paths V)).δ i c) = weight c := by
  apply weight_whisker_eq_of_endpoints
  · change i.succAbove (0 : Fin (n + 1)) = 0
    have hi : (0 : Fin (n + 1)).castSucc < i := by
      simpa using (Fin.pos_iff_ne_zero.mpr h₀)
    simpa using Fin.succAbove_of_castSucc_lt i (0 : Fin (n + 1)) hi
  · change i.succAbove (Fin.last n) = Fin.last (n + 1)
    have hi : i.val ≠ n + 1 := by
      intro he
      exact h₁ (Fin.ext he)
    have hl : i ≤ (Fin.last n).castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last]
      omega
    simpa using Fin.succAbove_of_le_castSucc i (Fin.last n) hl

end
end DaggerNativeFreePathNerveWeightOperators
