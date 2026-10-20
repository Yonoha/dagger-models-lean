import NativeInnerHornDataPostcomposition
import OriginalInnerHornNerveFiller

/-! Reconstruct the ORIGINAL enriched simplex from its ORIGINAL inner-horn face data. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial
open DaggerOrdinaryRigidificationCof
open DaggerOrdinaryRigidificationCof.BoundaryData DaggerOrdinaryRigidificationCof.PathFacets
open DaggerOrdinaryRigidificationCof.InnerHornFaces
universe u
namespace DaggerNativeInnerHornSimplexReconstruction
noncomputable section

private theorem map_heq {C B : SC.{u}} {F G : C ⟶ B} (h : F = G) (x y : C.Obj) :
    HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

theorem simplex_restriction {d : ℕ} {C : SC.{u}} (K : (Δ[d] : SSet.{u}).Subcomplex)
    (G : T.obj ⦋d⦌ ⟶ C) {m : SimplexCategory} (φ : m ⟶ ⦋d⦌)
    (hφ : SubcomplexNerveData.Contains K φ) :
    SubcomplexNerveData.simplex K (K.ι ≫ SSet.yonedaEquiv.symm (ULift.up G)) φ hφ =
      T.map φ ≫ G := rfl

variable {n : ℕ} {C : SC.{u}} (k : interior n) (G : T.obj ⦋n + 1⦌ ⟶ C)

def restriction : (SSet.horn.{u} (n + 1) k.val).toSSet ⟶ N.obj C :=
  (SSet.horn (n + 1) k.val).ι ≫ SSet.yonedaEquiv.symm (ULift.up G)

theorem data_obj (i : Fin (n + 2)) :
    (InnerHornData.data k (restriction k G)).obj i = G.obj (.mk (ULift.up i)) := rfl

theorem canonicalF_restriction (s : Finset (Fin (n + 2))) (hs : s.Nonempty)
    (hp : Admissible k s) :
    (InnerHornData.data k (restriction k G)).canonicalF s hs hp =
      SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom ≫ G := by
  rw [InnerHornData.data_canonicalF]
  unfold SubcomplexNerveData.faceFunctor restriction
  rw [simplex_restriction, ← Category.assoc]
  congr 1
  change EnrichedFunctor.comp SSet
    (SimplicialThickening.functor (faceBackward s hs).uliftMap)
    (SimplicialThickening.functor (faceOrdinal s hs).toOrderHom.uliftMap) = _
  rw [← SimplicialThickening.functor_comp]
  congr 1
  apply DFunLike.ext
  intro x
  apply ULift.ext
  change ((faceOrderIso s hs) ((faceOrderIso s hs).symm x.down)).val = x.down.val
  exact congrArg Subtype.val (OrderIso.apply_symm_apply _ _)

theorem properMap_restriction (i j : Fin (n + 2))
    (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    InnerHornProperMaps.properMap k (InnerHornData.data k (restriction k G)) i j hp =
      G.map (.mk (ULift.up i)) (.mk (ULift.up j)) := by
  by_cases hij : i ≤ j
  · simp only [InnerHornProperMaps.properMap, dif_pos hij,
      InnerHornProperMaps.forwardProperMap]
    have hm := map_heq (canonicalF_restriction k G (Finset.Icc i j) (intervalNonempty i j hij)
      (interval_admissible k i j hp))
      (.mk (intervalLeft i j hij)) (.mk (intervalRight i j hij))
    rw [eq_of_heq hm]
    change (intervalHomIso i j hij).inv ≫
      ((intervalHomIso i j hij).hom ≫ G.map (.mk (ULift.up i)) (.mk (ULift.up j))) = _
    exact Iso.inv_hom_id_assoc _ _
  · exact empty_hom_ext (J := vertices.{u} (n + 1))
      (i := ULift.up i) (j := ULift.up j) (lt_of_not_ge hij) _ _

theorem faceMap_restriction (s : Finset (Fin (n + 2))) (hs : s.Nonempty)
    (hp : Admissible k s) (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    (InnerHornData.data k (restriction k G)).faceMap s hs hp i j hi hj =
      homFromFace s i j hi hj ≫ G.map (.mk (ULift.up i)) (.mk (ULift.up j)) :=
  eq_of_heq (map_heq (canonicalF_restriction k G s hs hp) (label s i hi) (label s j hj))

theorem faceEvaluation_restriction (s : Finset (Fin (n + 2))) (hs : s.Nonempty)
    (hp : Admissible k s) (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    (InnerHornData.data k (restriction k G)).faceEvaluation s hs hp i j hi hj =
      (pathsInFace s i j).ι ≫ G.map (.mk (ULift.up i)) (.mk (ULift.up j)) := by
  apply (cancel_epi (facePathsIso.{u} s i j hi hj).hom).mp
  change facePathMap s i j hi hj ≫ _ = facePathMap s i j hi hj ≫
    (pathsInFace s i j).ι ≫ G.map (.mk (ULift.up i)) (.mk (ULift.up j))
  rw [CompatibleFaceData.facePathMap_evaluation, ← Category.assoc, facePathMap_ι]
  exact faceMap_restriction k G s hs hp i j hi hj

theorem omittedEvaluation_restriction (l : interior n) (hlk : l ≠ k) :
    InnerHornFacetMaps.omittedEvaluation k (InnerHornData.data k (restriction k G)) l hlk =
      (extremeOmitted n l).ι ≫ G.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1)))) := by
  unfold InnerHornFacetMaps.omittedEvaluation
  rw [faceEvaluation_restriction, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]

theorem cutEvaluation_restriction (l : interior n) :
    InnerHornFacetMaps.cutEvaluation k (InnerHornData.data k (restriction k G)) l =
      (extremeCut n l).ι ≫ G.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1)))) := by
  apply (cancel_epi
    (cutIso (ULift.up 0) (ULift.up l.val) (ULift.up (Fin.last (n + 1)))).hom).mp
  change cutMap (ULift.up 0) (ULift.up l.val) (ULift.up (Fin.last (n + 1))) ≫ _ =
    cutMap (ULift.up 0) (ULift.up l.val) (ULift.up (Fin.last (n + 1))) ≫
      (extremeCut n l).ι ≫ G.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1))))
  rw [InnerHornFacetMaps.cutMap_evaluation, properMap_restriction, properMap_restriction]
  exact (G.map_comp (.mk (ULift.up 0)) (.mk (ULift.up l.val))
    (.mk (ULift.up (Fin.last (n + 1))))).symm

theorem facetEvaluation_restriction (l : InnerHornDiagram.FacetIndex k) :
    InnerHornGlue.facetEvaluation k (InnerHornData.data k (restriction k G)) l =
      (InnerHornDiagram.facetSub k l).ι ≫
        G.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1)))) := by
  cases l with
  | inl l => exact omittedEvaluation_restriction k G l.val l.property
  | inr l => exact cutEvaluation_restriction k G l

theorem hornMap_restriction :
    InnerHornGlue.hornMap k (InnerHornData.data k (restriction k G)) =
      (extremeHorn n k).ι ≫ G.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1)))) := by
  apply Multicofork.IsColimit.hom_ext (InnerHornDiagram.isColimit k)
  intro l
  change SSet.Subcomplex.homOfLE (InnerHornDiagram.facet_le k l) ≫ _ =
    SSet.Subcomplex.homOfLE (InnerHornDiagram.facet_le k l) ≫
      (extremeHorn n k).ι ≫ G.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1))))
  rw [InnerHornGlue.hornMap_restrict, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]
  exact facetEvaluation_restriction k G l

theorem completeMap_restriction (i j : Fin (n + 2)) :
    InnerHornCompleteMaps.completeMap k (InnerHornData.data k (restriction k G))
        (G.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1))))) i j =
      G.map (.mk (ULift.up i)) (.mk (ULift.up j)) := by
  by_cases h : i = 0 ∧ j = Fin.last (n + 1)
  · rcases h with ⟨rfl, rfl⟩
    rw [InnerHornCompleteMaps.completeMap_extreme]
  · rw [InnerHornCompleteMaps.completeMap_proper k _ _ i j h]
    exact properMap_restriction k G i j h

theorem extensionFunctor_restriction :
    InnerHornExtension.extensionFunctor k (InnerHornData.data k (restriction k G))
      (G.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1)))))
      (hornMap_restriction k G).symm = G := by
  apply EnrichedFunctor.ext SSet
    (F := InnerHornExtension.extensionFunctor k (InnerHornData.data k (restriction k G))
      (G.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1)))))
      (hornMap_restriction k G).symm) (G := G) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact completeMap_restriction k G x.as.down y.as.down

end
end DaggerNativeInnerHornSimplexReconstruction
