import NativeRealOrdinaryCotensorComparison
import Mathlib.CategoryTheory.Groupoid

/-! Extend an ORIGINAL groupoid chain to all ordered pairs of its original vertices. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
universe u
namespace DaggerNativeGroupoidChainExtension
noncomputable section
variable {C : Type u} [Groupoid.{u} C]

/-- The arrow determined by the original chain, in either direction. -/
def bridge {n : ℕ} (F : Fin (n + 1) ⥤ C) (i j : Fin (n + 1)) : F.obj i ⟶ F.obj j :=
  inv (F.map (homOfLE (Fin.zero_le i))) ≫ F.map (homOfLE (Fin.zero_le j))

theorem bridge_id {n : ℕ} (F : Fin (n + 1) ⥤ C) (i : Fin (n + 1)) :
    bridge F i i = 𝟙 _ := by simp [bridge]

theorem bridge_comp {n : ℕ} (F : Fin (n + 1) ⥤ C) (i j k : Fin (n + 1)) :
    bridge F i j ≫ bridge F j k = bridge F i k := by
  simp [bridge, Category.assoc]

/-- On every existing ordered pair this is exactly the ORIGINAL chain arrow. -/
theorem bridge_hom {n : ℕ} (F : Fin (n + 1) ⥤ C) {i j : Fin (n + 1)} (f : i ⟶ j) :
    bridge F i j = F.map f := by
  have h : homOfLE (Fin.zero_le i) ≫ f = homOfLE (Fin.zero_le j) := Subsingleton.elim _ _
  unfold bridge
  rw [← h, F.map_comp]
  simp

theorem bridge_reverse {n : ℕ} (F : Fin (n + 1) ⥤ C) (i j : Fin (n + 1)) :
    bridge F i j = inv (bridge F j i) := by
  simp [bridge, IsIso.inv_comp]

/-- Reindexing an original chain preserves every arrow, even when its zero vertex changes. -/
theorem bridge_precomp {n m : ℕ} (H : Fin (m + 1) ⥤ Fin (n + 1))
    (F : Fin (n + 1) ⥤ C) (i j : Fin (m + 1)) :
    bridge (H ⋙ F) i j = bridge F (H.obj i) (H.obj j) := by
  rcases le_total i j with hij | hji
  · rw [bridge_hom (H ⋙ F) (homOfLE hij), bridge_hom F (H.map (homOfLE hij))]
    rfl
  · rw [bridge_reverse (H ⋙ F) i j, bridge_reverse F (H.obj i) (H.obj j)]
    rw [bridge_hom (H ⋙ F) (homOfLE hji), bridge_hom F (H.map (homOfLE hji))]
    rfl

/-- Any vertex function now specifies a genuine chain by ORIGINAL groupoid arrows. -/
def ofVertices {n m : ℕ} (F : Fin (n + 1) ⥤ C)
    (v : Fin (m + 1) → Fin (n + 1)) : Fin (m + 1) ⥤ C where
  obj i := F.obj (v i)
  map {i j} _ := bridge F (v i) (v j)
  map_id i := bridge_id F (v i)
  map_comp {i j k} _ _ := (bridge_comp F (v i) (v j) (v k)).symm

/-- Domain reindexing retains precisely the same vertex function. -/
theorem ofVertices_precomp {n m k : ℕ} (F : Fin (n + 1) ⥤ C)
    (v : Fin (m + 1) → Fin (n + 1)) (H : Fin (k + 1) ⥤ Fin (m + 1)) :
    H ⋙ ofVertices F v = ofVertices F (v ∘ H.obj) := rfl

/-- Reindex the original chain before extending it, with no choice of a new base vertex. -/
theorem ofVertices_chain_precomp {n m k : ℕ} (F : Fin (n + 1) ⥤ C)
    (H : Fin (m + 1) ⥤ Fin (n + 1)) (v : Fin (k + 1) → Fin (m + 1)) :
    ofVertices (H ⋙ F) v = ofVertices F (H.obj ∘ v) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using
    bridge_precomp H F (v i) (v j)

end
end DaggerNativeGroupoidChainExtension
