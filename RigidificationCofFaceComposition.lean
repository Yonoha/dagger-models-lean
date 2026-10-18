import RigidificationCofPathFaces
import RigidificationCofDoubleCuts

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.PathFacets

open SimplicialThickening

variable {J K : Type u} [LinearOrder J] [LinearOrder K]

/-- Preimage commutes with the ACTUAL original Path union composition in every degree. -/
theorem preimageChain_compose (e : J ↪o K) (i k j : J) (q : SimplexCategoryᵒᵖ)
    (γ : (hom (e i) (e k)).obj q) (δ : (hom (e k) (e j)).obj q) :
    preimageChain e ((compose (e i) (e k) (e j)).app q (γ, δ)) =
      (compose i k j).app q (preimageChain e γ, preimageChain e δ) := by
  apply nerve.ext_of_isThin
  funext t
  apply SimplicialThickening.Path.ext
  rfl

end DaggerOrdinaryRigidificationCof.PathFacets

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A : SC.{u}}

theorem compose_mem_face (s : Finset (Fin (n + 1))) (i k j : Fin (n + 1))
    (q : SimplexCategoryᵒᵖ) (γ : (pathsInFace.{u} s i k).toSSet.obj q)
    (δ : (pathsInFace.{u} s k j).toSSet.obj q) :
    (compose (ULift.up i) (ULift.up k) (ULift.up j)).app q (γ.val, δ.val) ∈
      (pathsInFace s i j).obj q := by
  intro t x hx
  rcases hx with h | h
  · exact γ.property t x h
  · exact δ.property t x h

/-- Full proper-face composition, including the extreme endpoints within THAT proper face. -/
theorem faceEvaluation_comp (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (i k j : Fin (n + 2)) (hi : i ∈ s) (hk : k ∈ s) (hj : j ∈ s)
    (q : SimplexCategoryᵒᵖ) (γ : (pathsInFace.{u} s i k).toSSet.obj q)
    (δ : (pathsInFace.{u} s k j).toSSet.obj q) :
    (faceEvaluation a s hs hp i j hi hj).app q
        ⟨(compose (ULift.up i) (ULift.up k) (ULift.up j)).app q (γ.val, δ.val),
          compose_mem_face s i k j q γ δ⟩ =
      elementComp q ((faceEvaluation a s hs hp i k hi hk).app q γ)
        ((faceEvaluation a s hs hp k j hk hj).app q δ) := by
  change ((canonicalFaceFunctor a s hs hp).map (label s i hi) (label s j hj)).app q
    (preimageChain (subsetEmbedding s)
      ((compose (ULift.up i) (ULift.up k) (ULift.up j)).app q (γ.val, δ.val))) = _
  have hc : preimageChain (subsetEmbedding s)
      ((compose (ULift.up i) (ULift.up k) (ULift.up j)).app q (γ.val, δ.val)) =
      (compose (ULift.up ⟨i, hi⟩ : ULift.{u} s) (ULift.up ⟨k, hk⟩)
        (ULift.up ⟨j, hj⟩)).app q
          (preimageChain (subsetEmbedding s) γ.val, preimageChain (subsetEmbedding s) δ.val) :=
    preimageChain_compose (subsetEmbedding s)
      (ULift.up ⟨i, hi⟩) (ULift.up ⟨k, hk⟩) (ULift.up ⟨j, hj⟩) q γ.val δ.val
  rw [hc]
  exact congrFun (congrArg (fun f => f.app q)
    ((canonicalFaceFunctor a s hs hp).map_comp (label s i hi) (label s k hk)
      (label s j hj))) (preimageChain (subsetEmbedding s) γ.val,
        preimageChain (subsetEmbedding s) δ.val)

end

end DaggerOrdinaryRigidificationCof.BoundaryData
