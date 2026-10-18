import OriginalInnerHornExtension

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornExtensionFaces

noncomputable section

open BoundaryData PathFacets SimplicialThickening InnerHornFaces
open InnerHornCompleteMaps InnerHornExtension

variable {n : ℕ} {A : SC.{u}} (k : interior n)
variable (D : CompatibleFaceData (n + 1) A (Admissible k))
variable (ell : extremeHom.{u} n ⟶
  (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))))
variable (hl : (extremeHorn n k).ι ≫ ell = InnerHornGlue.hornMap k D)

include hl in
/-- Admissibility supplies a missing vertex distinct from the excluded horn index. -/
theorem completeMap_extreme_restrict
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : Admissible k s)
    (hi : (0 : Fin (n + 2)) ∈ s) (hj : Fin.last (n + 1) ∈ s) :
    homFromFace s 0 (Fin.last (n + 1)) hi hj ≫ ell =
      D.faceMap s hs hp 0 (Fin.last (n + 1)) hi hj := by
  obtain ⟨r, hrk, hr⟩ := hp
  have hr0 : r ≠ 0 := fun e ↦ hr (e ▸ hi)
  have hrn : r ≠ Fin.last (n + 1) := fun e ↦ hr (e ▸ hj)
  let v : interior n := ⟨r, ⟨lt_of_le_of_ne (Fin.zero_le r) (Ne.symm hr0),
    lt_of_le_of_ne (Fin.le_last r) hrn⟩⟩
  have hvk : v ≠ k := fun e ↦ hrk (congrArg Subtype.val e)
  have hst : s ⊆ missingFace r := by
    intro x hx
    exact (mem_missingFace r x).mpr (fun e ↦ hr (e ▸ hx))
  have hSO : pathsInFace.{u} s 0 (Fin.last (n + 1)) ≤ extremeOmitted n v := by
    intro q γ h t hx
    exact hr (h t (ULift.up r) hx)
  have hO := InnerHornGlue.hornMap_omitted k D v hvk
  have heval : SSet.Subcomplex.homOfLE hSO ≫
      InnerHornFacetMaps.omittedEvaluation k D v hvk =
        D.faceEvaluation s hs ⟨r, hrk, hr⟩ 0 (Fin.last (n + 1)) hi hj := by
    unfold InnerHornFacetMaps.omittedEvaluation
    rw [← Category.assoc, SSet.Subcomplex.homOfLE_comp]
    have h := InnerHornFacetMaps.evaluation_from_common k D s (missingFace r) hs
      ⟨0, missingFace_zero v⟩ ⟨r, hrk, hr⟩
      (InnerHornFacetMaps.omittedAdmissible k v hvk) hst hi hj le_rfl
      (pathsInFace_mono hst 0 (Fin.last (n + 1)))
    simpa only [SSet.Subcomplex.homOfLE_refl, Category.id_comp] using h
  have hfull : (pathsInFace.{u} s 0 (Fin.last (n + 1))).ι ≫ ell =
      D.faceEvaluation s hs ⟨r, hrk, hr⟩ 0 (Fin.last (n + 1)) hi hj := by
    calc
      _ = SSet.Subcomplex.homOfLE hSO ≫
          SSet.Subcomplex.homOfLE (omitted_le_extremeHorn n k v hvk) ≫
            (extremeHorn n k).ι ≫ ell := by
        rw [← Category.assoc, ← Category.assoc, SSet.Subcomplex.homOfLE_comp,
          SSet.Subcomplex.homOfLE_ι]
      _ = SSet.Subcomplex.homOfLE hSO ≫
          InnerHornFacetMaps.omittedEvaluation k D v hvk := by rw [hl, hO]
      _ = _ := heval
  rw [← facePathMap_ι s 0 (Fin.last (n + 1)) hi hj, Category.assoc, hfull]
  exact D.facePathMap_evaluation s hs ⟨r, hrk, hr⟩ 0 (Fin.last (n + 1)) hi hj

include hl in
theorem completeMap_restrict
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : Admissible k s)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    homFromFace s i j hi hj ≫ InnerHornCompleteMaps.completeMap k D ell i j =
      D.faceMap s hs hp i j hi hj := by
  by_cases hij : i = 0 ∧ j = Fin.last (n + 1)
  · rcases hij with ⟨rfl, rfl⟩
    rw [InnerHornCompleteMaps.completeMap_extreme]
    exact completeMap_extreme_restrict k D ell hl s hs hp hi hj
  · rw [InnerHornCompleteMaps.completeMap_proper k D ell i j hij]
    exact InnerHornProperMaps.properMap_restrict k D i j hij s hs hp hi hj

include hl in
theorem extensionFunctor_on_face
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : Admissible k s) :
    SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom ≫
      InnerHornExtension.extensionFunctor k D ell hl = D.canonicalF s hs hp := by
  change EnrichedFunctor.comp SSet
    (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom)
      (InnerHornExtension.extensionFunctor k D ell hl) = D.canonicalF s hs hp
  apply EnrichedFunctor.ext SSet
    (F := EnrichedFunctor.comp SSet
      (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom)
      (InnerHornExtension.extensionFunctor k D ell hl))
    (G := D.canonicalF s hs hp) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change homFromFace s x.as.down.val y.as.down.val x.as.down.property y.as.down.property ≫
    InnerHornCompleteMaps.completeMap k D ell x.as.down.val y.as.down.val = _
  exact completeMap_restrict k D ell hl s hs hp _ _ _ _

end

end DaggerOrdinaryRigidificationCof.InnerHornExtensionFaces
