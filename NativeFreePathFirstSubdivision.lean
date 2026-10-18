import NativePathFirstSplit
import NativeFreePathNerveWeightOperators
import NativeNerveFrontSubdivision

/-! First-edge subdivision keeps the original native inner face, endpoints and whole path weight. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativePathFirstSplit DaggerNativeFreePathNerveWeight
open DaggerNativeFreePathNerveWeightOperators DaggerNativeNerveFrontSubdivision
universe u
namespace DaggerNativeFreePathFirstSubdivision
noncomputable section

variable {V : Type u} [Quiver.{u + 1} V]

def splitSimplex {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) : ComposableArrows (Paths V) (n + 2) :=
  (c.δ₀.precomp s.rest).precomp s.first.toPath

theorem delta_one_split {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) :
    (nerve (Paths V)).δ (1 : Fin (n + 3)) (splitSimplex c s) = c := by
  rw [splitSimplex, delta_one_precomp_precomp]
  change c.δ₀.precomp (s.first.toPath.comp s.rest) = c
  rw [s.spec]
  exact reconstruct c

theorem split_first_length {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) :
    ((splitSimplex c s).map' 0 1).length = 1 := rfl

theorem split_second_length {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) :
    ((splitSimplex c s).map' 1 2).length = s.rest.length := rfl

theorem split_vertex_zero {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) : (splitSimplex c s).obj 0 = c.obj 0 := rfl

theorem split_vertex_last {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) :
    (splitSimplex c s).obj (Fin.last (n + 2)) = c.obj (Fin.last (n + 1)) := rfl

theorem split_weight {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) : weight (splitSimplex c s) = weight c := by
  have h := weight_delta_inner (splitSimplex c s) (1 : Fin (n + 3)) (by
    intro he
    have hi := congrArg Fin.val he
    simp only [Fin.val_one, Fin.val_zero] at hi
    omega) (by
    intro he
    have hi := congrArg Fin.val he
    simp only [Fin.val_one, Fin.val_last] at hi
    omega)
  rw [delta_one_split] at h
  exact h.symm

theorem split_zero_weight_lt {n : ℕ} (c : ComposableArrows (Paths V) (n + 1))
    (s : FirstSplit (V := V) (c.map' 0 1)) :
    weight ((nerve (Paths V)).δ 0 (splitSimplex c s)) < weight c := by
  rw [← split_weight c s]
  apply weight_delta_zero_lt
  rw [split_first_length]
  decide

end
end DaggerNativeFreePathFirstSubdivision
