import RigidificationCofOver
import RigidificationCofExtremeBoundary

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ}

def pathsInFace (s : Finset (Fin (n + 1))) (i j : Fin (n + 1)) :
    (hom (ULift.up i) (ULift.up j)).Subcomplex where
  obj _ := {γ | ∀ t x, x ∈ (γ.obj t).I → x.down ∈ s}
  map α _ h t x hx := h (α.unop.toOrderHom t) x hx

def facePathMap (s : Finset (Fin (n + 1))) (i j : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) :
    (label s i hi ⟶[SSet.{u}] label s j hj) ⟶ (pathsInFace s i j).toSSet where
  app q γ := ⟨(homFromFace s i j hi hj).app q γ, by
    intro t x hx
    obtain ⟨z, _, rfl⟩ := hx
    exact z.down.property⟩
  naturality _ _ _ := rfl

theorem facePathMap_ι (s : Finset (Fin (n + 1))) (i j : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) :
    facePathMap.{u} s i j hi hj ≫ (pathsInFace s i j).ι = homFromFace s i j hi hj := rfl

def facePathInverse (s : Finset (Fin (n + 1))) (i j : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) :
    (pathsInFace s i j).toSSet ⟶ (label s i hi ⟶[SSet.{u}] label s j hj) where
  app _ γ := preimageChain (subsetEmbedding s) γ.val
  naturality _ _ _ := by
    funext γ
    apply nerve.ext_of_isThin (C := SimplicialThickening.Path
      (ULift.up ⟨i, hi⟩ : ULift.{u} s) (ULift.up ⟨j, hj⟩))
    rfl

def facePathsIso (s : Finset (Fin (n + 1))) (i j : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) :
    (label s i hi ⟶[SSet.{u}] label s j hj) ≅ (pathsInFace s i j).toSSet where
  hom := facePathMap s i j hi hj
  inv := facePathInverse s i j hi hj
  hom_inv_id := by
    apply NatTrans.ext
    funext q γ
    apply nerve.ext_of_isThin (C := SimplicialThickening.Path
      (ULift.up ⟨i, hi⟩ : ULift.{u} s) (ULift.up ⟨j, hj⟩))
    funext t
    apply SimplicialThickening.Path.ext
    ext x
    exact (subsetEmbedding s).injective.mem_set_image
  inv_hom_id := by
    apply NatTrans.ext
    funext q γ
    apply Subtype.ext
    apply nerve.ext_of_isThin
    funext t
    apply SimplicialThickening.Path.ext
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x.down, γ.property t x hx⟩⟩, hx, rfl⟩

theorem pathsInFace_mono {s t : Finset (Fin (n + 1))} (hst : s ⊆ t)
    (i j : Fin (n + 1)) : pathsInFace.{u} s i j ≤ pathsInFace t i j :=
  fun _ _ h k x hx => hst (h k x hx)

theorem facePathMap_restrict {s t : Finset (Fin (n + 1))} (hst : s ⊆ t)
    (i j : Fin (n + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    facePathMap.{u} s i j hi hj ≫ SSet.Subcomplex.homOfLE (pathsInFace_mono hst i j) =
      (faceInclusionFunctor hst).map (label s i hi) (label s j hj) ≫
        facePathMap t i j (hst hi) (hst hj) := by
  apply (cancel_mono (pathsInFace t i j).ι).mp
  rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
  rw [facePathMap_ι, Category.assoc, facePathMap_ι]
  exact (homFromFace_comp hst i j hi hj).symm

variable {A B : SC.{u}}

def faceEvaluation (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    (pathsInFace s i j).toSSet ⟶ (vertex a i ⟶[SSet.{u}] vertex a j) :=
  (facePathsIso s i j hi hj).inv ≫ faceMap a s hs hp i j hi hj

theorem facePathMap_evaluation (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    facePathMap s i j hi hj ≫ faceEvaluation a s hs hp i j hi hj =
      faceMap a s hs hp i j hi hj := by
  change (facePathsIso s i j hi hj).hom ≫ ((facePathsIso s i j hi hj).inv ≫ _) = _
  simp only [Iso.hom_inv_id_assoc]

theorem faceEvaluation_restrict (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s t : Finset (Fin (n + 2))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hps : s ≠ Finset.univ) (hpt : t ≠ Finset.univ) (hst : s ⊆ t)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    SSet.Subcomplex.homOfLE (pathsInFace_mono hst i j) ≫
      faceEvaluation a t ht hpt i j (hst hi) (hst hj) =
      faceEvaluation a s hs hps i j hi hj := by
  apply (cancel_epi (facePathsIso.{u} s i j hi hj).hom).mp
  change facePathMap s i j hi hj ≫ _ = facePathMap s i j hi hj ≫ _
  rw [← Category.assoc, facePathMap_restrict hst, Category.assoc,
    facePathMap_evaluation, facePathMap_evaluation,
    faceMap_restrict a s t hs ht hps hpt hst]

theorem faceEvaluation_proper (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s)
    (hij : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    (pathsInFace s i j).ι ≫ properMap a i j hij =
      faceEvaluation a s hs hp i j hi hj := by
  apply (cancel_epi (facePathsIso.{u} s i j hi hj).hom).mp
  change facePathMap s i j hi hj ≫ _ = facePathMap s i j hi hj ≫ _
  rw [← Category.assoc, facePathMap_ι, properMap_restrict, facePathMap_evaluation]

end

end DaggerOrdinaryRigidificationCof.BoundaryData
