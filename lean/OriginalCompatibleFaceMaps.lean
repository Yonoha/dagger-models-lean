import OriginalCompatibleFaceData
import RigidificationCofFaceComposition

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.CompatibleFaceData

noncomputable section

open BoundaryData PathFacets SimplicialThickening

variable {d : ℕ} {A : SC.{u}} {P : Finset (Fin (d + 1)) → Prop}
variable (D : CompatibleFaceData d A P)

private theorem map_heq {X Y : Type u} [EnrichedCategory SSet.{u} X]
    [EnrichedCategory SSet.{u} Y] {F G : EnrichedFunctor SSet.{u} X Y}
    (h : F = G) (x y : X) : HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

/-- The original full Hom map of one canonically named admitted face. -/
def faceMap (s : Finset (Fin (d + 1))) (hs : s.Nonempty) (hp : P s)
    (i j : Fin (d + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    (label s i hi ⟶[SSet.{u}] label s j hj) ⟶
      (D.obj i ⟶[SSet.{u}] D.obj j) :=
  (D.canonicalF s hs hp).map (label s i hi) (label s j hj)

/-- Face Hom maps restrict as full simplicial maps, including all operators. -/
theorem faceMap_restrict
    (s t : Finset (Fin (d + 1))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hps : P s) (hpt : P t) (hst : s ⊆ t)
    (i j : Fin (d + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    (faceInclusionFunctor.{u} hst).map (label s i hi) (label s j hj) ≫
      D.faceMap t ht hpt i j (hst hi) (hst hj) =
        D.faceMap s hs hps i j hi hj := by
  exact eq_of_heq (map_heq (D.canonicalF_restrict s t hs ht hps hpt hst)
    (label s i hi) (label s j hj))

/-- The same map evaluated on chains in the original Path subcomplex. -/
def faceEvaluation (s : Finset (Fin (d + 1))) (hs : s.Nonempty) (hp : P s)
    (i j : Fin (d + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    (pathsInFace s i j).toSSet ⟶ (D.obj i ⟶[SSet.{u}] D.obj j) :=
  (facePathsIso s i j hi hj).inv ≫ D.faceMap s hs hp i j hi hj

theorem facePathMap_evaluation
    (s : Finset (Fin (d + 1))) (hs : s.Nonempty) (hp : P s)
    (i j : Fin (d + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    facePathMap s i j hi hj ≫ D.faceEvaluation s hs hp i j hi hj =
      D.faceMap s hs hp i j hi hj := by
  change (facePathsIso s i j hi hj).hom ≫
    ((facePathsIso s i j hi hj).inv ≫ _) = _
  simp only [Iso.hom_inv_id_assoc]

/-- Evaluation agrees after restricting to any smaller admitted face. -/
theorem faceEvaluation_restrict
    (s t : Finset (Fin (d + 1))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hps : P s) (hpt : P t) (hst : s ⊆ t)
    (i j : Fin (d + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    SSet.Subcomplex.homOfLE (pathsInFace_mono hst i j) ≫
      D.faceEvaluation t ht hpt i j (hst hi) (hst hj) =
        D.faceEvaluation s hs hps i j hi hj := by
  apply (cancel_epi (facePathsIso.{u} s i j hi hj).hom).mp
  change facePathMap s i j hi hj ≫ _ = facePathMap s i j hi hj ≫ _
  rw [← Category.assoc, facePathMap_restrict hst, Category.assoc,
    D.facePathMap_evaluation, D.facePathMap_evaluation,
    D.faceMap_restrict s t hs ht hps hpt hst]

/-- Composition agrees on every simplex of the actual original Path face. -/
theorem faceEvaluation_comp
    (s : Finset (Fin (d + 1))) (hs : s.Nonempty) (hp : P s)
    (i k j : Fin (d + 1)) (hi : i ∈ s) (hk : k ∈ s) (hj : j ∈ s)
    (q : SimplexCategoryᵒᵖ) (γ : (pathsInFace.{u} s i k).toSSet.obj q)
    (δ : (pathsInFace.{u} s k j).toSSet.obj q) :
    (D.faceEvaluation s hs hp i j hi hj).app q
        ⟨(compose (ULift.up i) (ULift.up k) (ULift.up j)).app q (γ.val, δ.val),
          compose_mem_face s i k j q γ δ⟩ =
      elementComp q ((D.faceEvaluation s hs hp i k hi hk).app q γ)
        ((D.faceEvaluation s hs hp k j hk hj).app q δ) := by
  change ((D.canonicalF s hs hp).map (label s i hi) (label s j hj)).app q
    (preimageChain (subsetEmbedding s)
      ((compose (ULift.up i) (ULift.up k) (ULift.up j)).app q (γ.val, δ.val))) = _
  have hc : preimageChain (subsetEmbedding s)
      ((compose (ULift.up i) (ULift.up k) (ULift.up j)).app q (γ.val, δ.val)) =
      (compose (ULift.up ⟨i, hi⟩ : ULift.{u} s) (ULift.up ⟨k, hk⟩)
        (ULift.up ⟨j, hj⟩)).app q
          (preimageChain (subsetEmbedding s) γ.val,
            preimageChain (subsetEmbedding s) δ.val) :=
    preimageChain_compose (subsetEmbedding s)
      (ULift.up ⟨i, hi⟩) (ULift.up ⟨k, hk⟩) (ULift.up ⟨j, hj⟩) q γ.val δ.val
  rw [hc]
  exact congrFun (congrArg (fun f ↦ f.app q)
    ((D.canonicalF s hs hp).map_comp (label s i hi) (label s k hk)
      (label s j hj))) (preimageChain (subsetEmbedding s) γ.val,
        preimageChain (subsetEmbedding s) δ.val)

end

end DaggerOrdinaryRigidificationCof.CompatibleFaceData
