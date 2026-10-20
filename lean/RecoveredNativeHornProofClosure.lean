import TopCatModelCategory.SSet.Horn

/-! Restore the SAME two horn lemmas referenced by saved native proof bodies.
Their statements are copied from TopCatModelCategory at the fixed upstream revision.
Proofs use the CURRENT existing native horn colimit and extensionality API.
No accepted artifact is overwritten and no extra axiom is introduced.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
universe u
namespace SSet.horn
noncomputable section
variable {n : ℕ}

private theorem recovered_exists_desc' (i : Fin (n + 1)) {X : SSet.{u}}
    (f : ∀ (j : ({i}ᶜ : Set _)), (stdSimplex.face {j.1}ᶜ : SSet) ⟶ X)
    (hf : ∀ (j k : ({i}ᶜ : Set _)) (_ : j.1 < k.1),
      Subcomplex.homOfLE (show stdSimplex.face {j.1, k.1}ᶜ ≤ _ by
        simp [stdSimplex.face_le_face_iff]) ≫ f j =
      Subcomplex.homOfLE (show stdSimplex.face {j.1, k.1}ᶜ ≤ _ by
        simp [stdSimplex.face_le_face_iff]) ≫ f k) :
    ∃ (φ : (Λ[n, i] : SSet) ⟶ X),
      ∀ j, faceι i j.1 (by simpa only [Finset.mem_compl, Finset.mem_singleton] using j.2) ≫
        φ = f j :=
  ⟨(isColimit i).desc (Multicofork.ofπ _ _ f (fun s ↦ hf _ _ s.2)),
    fun j ↦ (isColimit i).fac _ (.right j)⟩

open stdSimplex in
lemma exists_desc {i : Fin (n + 3)} {X : SSet.{u}}
    (f : ({i}ᶜ : Set _) → ((Δ[n + 1] : SSet) ⟶ X))
    (hf : ∀ (j k : ({i}ᶜ : Set _)) (hjk : j.1 < k.1),
      stdSimplex.δ (k.1.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
        stdSimplex.δ (j.1.castPred (Fin.ne_last_of_lt hjk)) ≫ f k) :
    ∃ (φ : (Λ[n + 2, i] : SSet) ⟶ X), ∀ j, ι i j.1 j.2 ≫ φ = f j := by
  obtain ⟨φ, hφ⟩ := recovered_exists_desc' (i := i)
    (f := fun j ↦ (faceSingletonComplIso j.1).inv ≫ f j) (fun j k hjk ↦ by
      dsimp
      rw [homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_pred_assoc _ _ hjk,
        homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_castPred_assoc _ _ hjk,
        hf _ _ hjk])
  exact ⟨φ, fun j ↦ by
    rw [← cancel_epi (faceSingletonComplIso j.1).inv, ← hφ,
      faceSingletonComplIso_inv_ι_assoc]⟩

lemma hom_ext' {i : Fin (n + 2)} {X : SSet.{u}} {f g : (Λ[n + 1, i] : SSet) ⟶ X}
    (h : ∀ (j : Fin (n + 2)) (hij : j ≠ i), horn.ι i j hij ≫ f = horn.ι i j hij ≫ g) :
    f = g := by
  apply SSet.horn.hom_ext f g
  intro j hj
  exact congrArg (fun k : (Δ[n] : SSet.{u}) ⟶ X ↦
    k.app (op ⦋n⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) (h j hj)

end
end SSet.horn
