import NativeStdSimplexMidpoint
import NativeRealEdgewiseSymmetry
import OriginalTopologicalSimplexReversal

/-! The literal palindromic simplex parameter e(t) = (reverse(t), t) / 2.
The topology, ordinal-sum inclusions, affine maps and midpoint are Mathlib's.
-/
set_option autoImplicit false
open CategoryTheory AugmentedSimplexCategory
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseSymmetry
open DaggerOriginalTopologicalSimplexReversal DaggerNativeStdSimplexMidpoint
namespace DaggerNativeRealEdgewiseParameters
noncomputable section

def leftPart (n : SimplexCategory) (t : stdSimplex ℝ (Fin (n.len + 1))) :
    stdSimplex ℝ (Fin ((epsilon.obj n).len + 1)) :=
  stdSimplex.map (inl' n n).toOrderHom (reverse n.len t)

def rightPart (n : SimplexCategory) (t : stdSimplex ℝ (Fin (n.len + 1))) :
    stdSimplex ℝ (Fin ((epsilon.obj n).len + 1)) :=
  stdSimplex.map (inr' n n).toOrderHom t

def parameter (n : SimplexCategory) (t : stdSimplex ℝ (Fin (n.len + 1))) :
    stdSimplex ℝ (Fin ((epsilon.obj n).len + 1)) :=
  halfAverage (leftPart n t) (rightPart n t)

theorem leftPart_natural {n m : SimplexCategory} (f : n ⟶ m)
    (t : stdSimplex ℝ (Fin (n.len + 1))) :
    stdSimplex.map (epsilon.map f).toOrderHom (leftPart n t) =
      leftPart m (stdSimplex.map f.toOrderHom t) := by
  unfold leftPart reverse
  simp only [stdSimplex.map_comp_apply]
  congr 1
  funext i
  change (epsilon.map f).toOrderHom ((inl' n n).toOrderHom i.rev) =
    (inl' m m).toOrderHom (f.toOrderHom i).rev
  rw [epsilon_map_left, SimplexCategory.rev_map_apply, Fin.rev_rev]
  rfl

theorem rightPart_natural {n m : SimplexCategory} (f : n ⟶ m)
    (t : stdSimplex ℝ (Fin (n.len + 1))) :
    stdSimplex.map (epsilon.map f).toOrderHom (rightPart n t) =
      rightPart m (stdSimplex.map f.toOrderHom t) := by
  unfold rightPart
  simp only [stdSimplex.map_comp_apply]
  congr 1
  funext i
  exact epsilon_map_right f i

theorem reverse_leftPart (n : SimplexCategory) (t : stdSimplex ℝ (Fin (n.len + 1))) :
    reverse (epsilon.obj n).len (leftPart n t) = rightPart n t := by
  simp only [leftPart, rightPart, reverse, stdSimplex.map_comp_apply]
  congr 1
  funext i
  change ((inl' n n).toOrderHom i.rev).rev = (inr' n n).toOrderHom i
  rw [rev_inl, Fin.rev_rev]

theorem reverse_rightPart (n : SimplexCategory) (t : stdSimplex ℝ (Fin (n.len + 1))) :
    reverse (epsilon.obj n).len (rightPart n t) = leftPart n t := by
  simp only [leftPart, rightPart, reverse, stdSimplex.map_comp_apply]
  congr 1
  funext i
  exact rev_inr n i

theorem parameter_natural {n m : SimplexCategory} (f : n ⟶ m)
    (t : stdSimplex ℝ (Fin (n.len + 1))) :
    stdSimplex.map (epsilon.map f).toOrderHom (parameter n t) =
      parameter m (stdSimplex.map f.toOrderHom t) := by
  unfold parameter
  rw [map_halfAverage, leftPart_natural, rightPart_natural]

theorem reverse_parameter (n : SimplexCategory) (t : stdSimplex ℝ (Fin (n.len + 1))) :
    reverse (epsilon.obj n).len (parameter n t) = parameter n t := by
  change stdSimplex.map Fin.rev (halfAverage (leftPart n t) (rightPart n t)) = _
  rw [map_halfAverage]
  change halfAverage (reverse (epsilon.obj n).len (leftPart n t))
    (reverse (epsilon.obj n).len (rightPart n t)) = _
  rw [reverse_leftPart, reverse_rightPart]
  exact halfAverage_comm _ _

theorem continuous_parameter (n : SimplexCategory) : Continuous (parameter n) := by
  have hl : Continuous (leftPart n) :=
    (stdSimplex.continuous_map (inl' n n).toOrderHom).comp
      (stdSimplex.continuous_map Fin.rev)
  have hr : Continuous (rightPart n) := stdSimplex.continuous_map (inr' n n).toOrderHom
  have hp : Continuous (fun t ↦ (leftPart n t, rightPart n t)) := hl.prodMk hr
  change Continuous (fun t ↦ halfAverage (leftPart n t) (rightPart n t))
  exact Continuous.comp (f := fun t ↦ (leftPart n t, rightPart n t))
    (g := fun p ↦ halfAverage p.1 p.2) continuous_halfAverage hp

end
end DaggerNativeRealEdgewiseParameters
