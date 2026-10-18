import OriginalInnerHornProperMaps
import RigidificationCofCutOverlap
import RigidificationCofOmittedEvaluation

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornFacetMaps

noncomputable section

open BoundaryData PathFacets SimplicialThickening InnerHornFaces
open InnerHornProperMaps

variable {n : ℕ} {A : SC.{u}}
variable (k : interior n)
variable (D : CompatibleFaceData (n + 1) A (Admissible k))

/-- The full Path-face evaluation restricts the original proper Hom map. -/
theorem faceEvaluation_proper
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hps : Admissible k s)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s)
    (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    (pathsInFace s i j).ι ≫ InnerHornProperMaps.properMap k D i j hp =
      D.faceEvaluation s hs hps i j hi hj := by
  apply (cancel_epi (facePathsIso.{u} s i j hi hj).hom).mp
  change facePathMap s i j hi hj ≫ _ = facePathMap s i j hi hj ≫ _
  rw [← Category.assoc, facePathMap_ι,
    InnerHornProperMaps.properMap_restrict, D.facePathMap_evaluation]

/-- Evaluate a cut with the two original proper-interval Hom maps. -/
def cutEvaluation (l : interior n) :
    (extremeCut.{u} n l).toSSet ⟶
      (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))) :=
  (cutIso (ULift.up 0) (ULift.up l.val) (ULift.up (Fin.last (n + 1)))).inv ≫
    (InnerHornProperMaps.properMap k D 0 l.val (leftProper l) ⊗ₘ
      InnerHornProperMaps.properMap k D l.val (Fin.last (n + 1)) (rightProper l)) ≫
        eComp SSet (D.obj 0) (D.obj l.val) (D.obj (Fin.last (n + 1)))

theorem cutMap_evaluation (l : interior n) :
    cutMap (ULift.up 0) (ULift.up l.val) (ULift.up (Fin.last (n + 1))) ≫
      cutEvaluation k D l =
        (InnerHornProperMaps.properMap k D 0 l.val (leftProper l) ⊗ₘ
          InnerHornProperMaps.properMap k D l.val
            (Fin.last (n + 1)) (rightProper l)) ≫
              eComp SSet (D.obj 0) (D.obj l.val) (D.obj (Fin.last (n + 1))) := by
  change (cutIso _ _ _).hom ≫ ((cutIso _ _ _).inv ≫ _ ≫ _) = _
  simp only [Iso.hom_inv_id_assoc]

abbrev evaluateProper (i j : Fin (n + 2))
    (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1)))
    (q : SimplexCategoryᵒᵖ) (γ : (hom (ULift.up i) (ULift.up j)).obj q) :=
  (InnerHornProperMaps.properMap k D i j hp).app q γ

theorem evaluateProper_comp
    (i j l : Fin (n + 2)) (hij : i ≤ j) (hjl : j ≤ l)
    (hpil : ¬ (i = 0 ∧ l = Fin.last (n + 1)))
    (hpij : ¬ (i = 0 ∧ j = Fin.last (n + 1)))
    (hpjl : ¬ (j = 0 ∧ l = Fin.last (n + 1)))
    (q : SimplexCategoryᵒᵖ) (γ : (hom (ULift.up i) (ULift.up j)).obj q)
    (δ : (hom (ULift.up j) (ULift.up l)).obj q) :
    evaluateProper k D i l hpil q
        ((compose (ULift.up i) (ULift.up j) (ULift.up l)).app q (γ, δ)) =
      elementComp q (evaluateProper k D i j hpij q γ)
        (evaluateProper k D j l hpjl q δ) :=
  congrFun (congrArg (fun f ↦ f.app q)
    (InnerHornProperMaps.properMap_comp_forward k D i j l
      hij hjl hpil hpij hpjl)) (γ, δ)

theorem cutEvaluation_app (l : interior n) (q : SimplexCategoryᵒᵖ)
    (γ : (extremeCut.{u} n l).toSSet.obj q) :
    (cutEvaluation k D l).app q γ =
      elementComp q (evaluateProper k D 0 l.val (leftProper l) q (splitChainLeft γ))
        (evaluateProper k D l.val (Fin.last (n + 1)) (rightProper l) q
          (splitChainRight γ)) := rfl

/-- The omitted facet is admitted exactly when it differs from the missing horn facet. -/
theorem omittedAdmissible (l : interior n) (hlk : l ≠ k) :
    Admissible k (missingFace l.val) := by
  refine ⟨l.val, fun h ↦ hlk (Subtype.ext h), ?_⟩
  intro h
  exact (mem_missingFace l.val l.val).mp h rfl

/-- Evaluate an actually admitted omitted facet with its complete face functor. -/
def omittedEvaluation (l : interior n) (hlk : l ≠ k) :
    (extremeOmitted.{u} n l).toSSet ⟶
      (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))) :=
  SSet.Subcomplex.homOfLE (omitted_le_paths l.val 0 (Fin.last (n + 1))) ≫
    D.faceEvaluation (missingFace l.val) ⟨0, missingFace_zero l⟩
      (omittedAdmissible k l hlk) 0 (Fin.last (n + 1))
      (missingFace_zero l) (missingFace_last l)

/-- Two evaluations from an admitted common face coincide on any subcomplex. -/
theorem evaluation_from_common
    {i j : Fin (n + 2)} {U : (hom (ULift.up i) (ULift.up j)).Subcomplex}
    (s t : Finset (Fin (n + 2))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hps : Admissible k s) (hpt : Admissible k t) (hst : s ⊆ t)
    (hi : i ∈ s) (hj : j ∈ s) (hUs : U ≤ pathsInFace s i j)
    (hUt : U ≤ pathsInFace t i j) :
    SSet.Subcomplex.homOfLE hUt ≫
      D.faceEvaluation t ht hpt i j (hst hi) (hst hj) =
        SSet.Subcomplex.homOfLE hUs ≫
          D.faceEvaluation s hs hps i j hi hj := by
  have h := D.faceEvaluation_restrict s t hs ht hps hpt hst i j hi hj
  rw [← h, ← Category.assoc, SSet.Subcomplex.homOfLE_comp]

end

end DaggerOrdinaryRigidificationCof.InnerHornFacetMaps
