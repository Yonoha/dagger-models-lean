import NativeFreePathInnerFaceNondegeneracy
import NativeFreePathFirstSubdivision

/-! Subdivision inverts the first inner face when the first native path is a generator. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativePathFirstSplit DaggerNativeFreePathFirstSubdivision
open DaggerNativeNerveFrontSubdivision
universe u
namespace DaggerNativeFreePathSubdivisionInverse
noncomputable section

variable {V : Type u} [Quiver.{u + 1} V]

theorem path_eq_generator_of_length_one {a b : V} (p : Quiver.Path a b)
    (hp : p.length = 1) : ∃ e : a ⟶ b, e.toPath = p := by
  cases p with
  | nil => simp at hp
  | cons q e =>
    cases q with
    | nil => exact ⟨e, rfl⟩
    | cons q' e' => simp at hp

theorem split_delta_one {n : ℕ} (d : ComposableArrows (Paths V) (n + 2))
    (hf : (d.map' 0 1).length = 1)
    (s : FirstSplit (V := V) ((show ComposableArrows (Paths V) (n + 1) from
      (nerve (Paths V)).δ (1 : Fin (n + 3)) d).map' 0 1)) :
    splitSimplex ((nerve (Paths V)).δ (1 : Fin (n + 3)) d) s = d := by
  obtain ⟨c, X, f, rfl⟩ := ComposableArrows.precomp_surjective d
  obtain ⟨b, Y, g, rfl⟩ := ComposableArrows.precomp_surjective c
  change f.length = 1 at hf
  obtain ⟨e, rfl⟩ := path_eq_generator_of_length_one f hf
  revert s
  rw [delta_one_precomp_precomp]
  intro s
  change FirstSplit (V := V) (e.toPath.comp g) at s
  have hs : s = ⟨Y, e, g, rfl⟩ := Subsingleton.elim _ _
  rw [hs]
  rfl

end
end DaggerNativeFreePathSubdivisionInverse
