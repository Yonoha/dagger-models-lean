import RigidificationCofExtension
import RigidificationCofSimplexRestriction

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A : SC.{u}}
variable (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (ell : extremeHom.{u} n ⟶ (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))))
    (hl : (extremeBoundary n).ι ≫ ell = boundaryMap a)

include hl in
theorem completeMap_extreme_restrict
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (hi : (0 : Fin (n + 2)) ∈ s) (hj : Fin.last (n + 1) ∈ s) :
    homFromFace s 0 (Fin.last (n + 1)) hi hj ≫ ell =
      faceMap a s hs hp 0 (Fin.last (n + 1)) hi hj := by
  have hex : ∃ k : Fin (n + 2), k ∉ s := by
    by_contra h
    apply hp
    exact Finset.eq_univ_of_forall (fun k => not_not.mp (fun hk => h ⟨k, hk⟩))
  obtain ⟨k, hk⟩ := hex
  have hk0 : k ≠ 0 := fun e => hk (e ▸ hi)
  have hkn : k ≠ Fin.last (n + 1) := fun e => hk (e ▸ hj)
  let v : interior n := ⟨k, ⟨lt_of_le_of_ne (Fin.zero_le k) (Ne.symm hk0),
    lt_of_le_of_ne (Fin.le_last k) hkn⟩⟩
  have hst : s ⊆ missingFace k := by
    intro x hx
    apply (mem_missingFace k x).mpr
    intro e
    exact hk (e ▸ hx)
  have hSO : pathsInFace.{u} s 0 (Fin.last (n + 1)) ≤ extremeOmitted n v := by
    intro q γ h t hx
    exact hk (h t (ULift.up k) hx)
  have hO : SSet.Subcomplex.homOfLE (omitted_le_extremeBoundary.{u} n v) ≫
      boundaryMap a = omittedEvaluation a v := boundaryMap_restrict a (Sum.inl v)
  have heval : SSet.Subcomplex.homOfLE hSO ≫ omittedEvaluation a v =
      faceEvaluation a s hs hp 0 (Fin.last (n + 1)) hi hj := by
    unfold omittedEvaluation
    rw [← Category.assoc, SSet.Subcomplex.homOfLE_comp]
    have h := evaluation_from_common a s (missingFace k) hs ⟨0, missingFace_zero v⟩ hp
      (missingFace_proper k) hst hi hj le_rfl (pathsInFace_mono hst 0 (Fin.last (n + 1)))
    simpa only [SSet.Subcomplex.homOfLE_refl, Category.id_comp] using h
  have hfull : (pathsInFace.{u} s 0 (Fin.last (n + 1))).ι ≫ ell =
      faceEvaluation a s hs hp 0 (Fin.last (n + 1)) hi hj := by
    calc
      _ = SSet.Subcomplex.homOfLE hSO ≫
          SSet.Subcomplex.homOfLE (omitted_le_extremeBoundary n v) ≫
            (extremeBoundary n).ι ≫ ell := by
        rw [← Category.assoc, ← Category.assoc, SSet.Subcomplex.homOfLE_comp,
          SSet.Subcomplex.homOfLE_ι]
      _ = SSet.Subcomplex.homOfLE hSO ≫ omittedEvaluation a v := by rw [hl, hO]
      _ = _ := heval
  rw [← facePathMap_ι s 0 (Fin.last (n + 1)) hi hj, Category.assoc, hfull]
  exact facePathMap_evaluation a s hs hp 0 (Fin.last (n + 1)) hi hj

include hl in
theorem completeMap_restrict
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    homFromFace s i j hi hj ≫ completeMap a ell i j = faceMap a s hs hp i j hi hj := by
  by_cases hij : i = 0 ∧ j = Fin.last (n + 1)
  · rcases hij with ⟨rfl, rfl⟩
    rw [completeMap_extreme]
    exact completeMap_extreme_restrict a ell hl s hs hp hi hj
  · rw [completeMap_proper a ell i j hij]
    exact properMap_restrict a i j hij s hs hp hi hj

include hl in
theorem extensionFunctor_on_face
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ) :
    SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom ≫
      extensionFunctor a ell hl = canonicalFaceFunctor a s hs hp := by
  change EnrichedFunctor.comp SSet
    (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom)
      (extensionFunctor a ell hl) = canonicalFaceFunctor a s hs hp
  apply EnrichedFunctor.ext SSet
    (F := EnrichedFunctor.comp SSet
      (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom)
      (extensionFunctor a ell hl)) (G := canonicalFaceFunctor a s hs hp) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change homFromFace s x.as.down.val y.as.down.val x.as.down.property y.as.down.property ≫
    completeMap a ell x.as.down.val y.as.down.val = _
  exact completeMap_restrict a ell hl s hs hp _ _ _ _

include hl in
/-- EVERY original proper ordinal simplex, with its full functor and all maps. -/
theorem extensionFunctor_on_simplex {m : SimplexCategory} (φ : m ⟶ ⦋n + 1⦌)
    (hn : ¬ Function.Surjective φ.toOrderHom) :
    T.map φ ≫ extensionFunctor a ell hl = simplex (n := ⦋n + 1⦌) a φ hn := by
  have hex : ∃ k : Fin (n + 2), ∀ i, φ.toOrderHom i ≠ k := by
    by_contra h
    apply hn
    intro k
    exact not_not.mp (fun hk => h ⟨k, fun i e => hk ⟨i, e⟩⟩)
  obtain ⟨k, hk⟩ := hex
  let s := missingFace k
  have hφ : ∀ i, φ.toOrderHom i ∈ s := fun i => (mem_missingFace k _).mpr (hk i)
  have hs : s.Nonempty := ⟨φ.toOrderHom 0, hφ 0⟩
  have hp := missingFace_proper k
  have hf : SimplicialThickening.functor φ.toOrderHom.uliftMap =
      EnrichedFunctor.comp SSet
        (SimplicialThickening.functor (faceLift s φ hφ).uliftMap)
        (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom) := by
    rw [← SimplicialThickening.functor_comp]
    rfl
  have hface := extensionFunctor_on_face a ell hl s hs hp
  change EnrichedFunctor.comp SSet
    (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom)
      (extensionFunctor a ell hl) = canonicalFaceFunctor a s hs hp at hface
  change EnrichedFunctor.comp SSet (SimplicialThickening.functor φ.toOrderHom.uliftMap)
    (extensionFunctor a ell hl) = _
  rw [hf]
  change EnrichedFunctor.comp SSet
    (SimplicialThickening.functor (faceLift s φ hφ).uliftMap)
    (EnrichedFunctor.comp SSet
      (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom)
      (extensionFunctor a ell hl)) = _
  rw [hface]
  exact (canonicalSimplex_from_face a s hs hp φ hφ hn).trans (canonicalSimplex_eq a φ hn)

include hl in
theorem extensionFunctor_on_facet (k : Fin (n + 2)) :
    T.map (SimplexCategory.δ k) ≫ extensionFunctor a ell hl = facet a k :=
  extensionFunctor_on_simplex a ell hl (SimplexCategory.δ k) (delta_not_surjective k)

end

end DaggerOrdinaryRigidificationCof.BoundaryData
