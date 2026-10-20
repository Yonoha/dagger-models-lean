import OriginalInnerHornGlue

/-! Postcomposition of the ORIGINAL compatible inner-horn faces and their extreme-Hom map. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial
open DaggerOrdinaryRigidificationCof
open DaggerOrdinaryRigidificationCof.BoundaryData
open DaggerOrdinaryRigidificationCof.PathFacets
open DaggerOrdinaryRigidificationCof.InnerHornFaces
open DaggerOrdinaryRigidificationCof.InnerHornProperMaps
open DaggerOrdinaryRigidificationCof.InnerHornFacetMaps
universe u
namespace DaggerNativeInnerHornFacePostcomposition
noncomputable section

private theorem map_heq {C B : SC.{u}} {F G : C ⟶ B} (h : F = G) (x y : C.Obj) :
    HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

def post {d : ℕ} {C B : SC.{u}} {P : Finset (Fin (d + 1)) → Prop}
    (D : CompatibleFaceData d C P) (p : C ⟶ B) : CompatibleFaceData d B P where
  obj i := p.obj (D.obj i)
  F s hs hp := D.F s hs hp ≫ p
  F_obj s hs hp x := congrArg p.obj (D.F_obj s hs hp x)
  F_restrict s t hs ht hps hpt hst := by
    rw [← Category.assoc, D.F_restrict s t hs ht hps hpt hst]

theorem canonicalF_post {d : ℕ} {C B : SC.{u}} {P : Finset (Fin (d + 1)) → Prop}
    (D : CompatibleFaceData d C P) (p : C ⟶ B) (s : Finset (Fin (d + 1)))
    (hs : s.Nonempty) (hp : P s) :
    (post D p).canonicalF s hs hp = D.canonicalF s hs hp ≫ p := by
  rw [CompatibleFaceData.canonicalF_eq, CompatibleFaceData.canonicalF_eq]
  rfl

theorem faceMap_post {d : ℕ} {C B : SC.{u}} {P : Finset (Fin (d + 1)) → Prop}
    (D : CompatibleFaceData d C P) (p : C ⟶ B) (s : Finset (Fin (d + 1)))
    (hs : s.Nonempty) (hp : P s) (i j : Fin (d + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    (post D p).faceMap s hs hp i j hi hj =
      D.faceMap s hs hp i j hi hj ≫ p.map (D.obj i) (D.obj j) :=
  eq_of_heq (map_heq (canonicalF_post D p s hs hp) (label s i hi) (label s j hj))

theorem faceEvaluation_post {d : ℕ} {C B : SC.{u}} {P : Finset (Fin (d + 1)) → Prop}
    (D : CompatibleFaceData d C P) (p : C ⟶ B) (s : Finset (Fin (d + 1)))
    (hs : s.Nonempty) (hp : P s) (i j : Fin (d + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    (post D p).faceEvaluation s hs hp i j hi hj =
      D.faceEvaluation s hs hp i j hi hj ≫ p.map (D.obj i) (D.obj j) := by
  unfold CompatibleFaceData.faceEvaluation
  rw [faceMap_post, Category.assoc]

variable {n : ℕ} {C B : SC.{u}} (k : interior n)
variable (D : CompatibleFaceData (n + 1) C (Admissible k)) (p : C ⟶ B)

theorem properMap_post (i j : Fin (n + 2)) (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    InnerHornProperMaps.properMap k (post D p) i j hp =
      InnerHornProperMaps.properMap k D i j hp ≫ p.map (D.obj i) (D.obj j) := by
  by_cases hij : i ≤ j
  · simp only [InnerHornProperMaps.properMap, dif_pos hij, InnerHornProperMaps.forwardProperMap]
    have hm := map_heq (canonicalF_post D p (Finset.Icc i j) (intervalNonempty i j hij)
      (interval_admissible k i j hp))
      (.mk (intervalLeft i j hij)) (.mk (intervalRight i j hij))
    rw [eq_of_heq hm, Category.assoc]
    rfl
  · exact empty_hom_ext (J := vertices.{u} (n + 1))
      (i := ULift.up i) (j := ULift.up j) (lt_of_not_ge hij) _ _

theorem omittedEvaluation_post (l : interior n) (hlk : l ≠ k) :
    InnerHornFacetMaps.omittedEvaluation k (post D p) l hlk =
      InnerHornFacetMaps.omittedEvaluation k D l hlk ≫
        p.map (D.obj 0) (D.obj (Fin.last (n + 1))) := by
  unfold InnerHornFacetMaps.omittedEvaluation
  rw [faceEvaluation_post, Category.assoc]

theorem cutEvaluation_post (l : interior n) :
    InnerHornFacetMaps.cutEvaluation k (post D p) l =
      InnerHornFacetMaps.cutEvaluation k D l ≫ p.map (D.obj 0) (D.obj (Fin.last (n + 1))) := by
  unfold InnerHornFacetMaps.cutEvaluation
  rw [properMap_post, properMap_post, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  dsimp only [post]
  exact congrArg (fun f ↦ (cutIso (ULift.up 0) (ULift.up l.val)
    (ULift.up (Fin.last (n + 1)))).inv ≫
      (InnerHornProperMaps.properMap k D 0 l.val (leftProper l) ⊗ₘ
        InnerHornProperMaps.properMap k D l.val (Fin.last (n + 1)) (rightProper l)) ≫ f)
    (p.map_comp (D.obj 0) (D.obj l.val) (D.obj (Fin.last (n + 1)))).symm


theorem facetEvaluation_post (l : InnerHornDiagram.FacetIndex k) :
    InnerHornGlue.facetEvaluation k (post D p) l = InnerHornGlue.facetEvaluation k D l ≫
      p.map (D.obj 0) (D.obj (Fin.last (n + 1))) := by
  cases l with
  | inl l => exact omittedEvaluation_post k D p l.val l.property
  | inr l => exact cutEvaluation_post k D p l

theorem hornMap_post : InnerHornGlue.hornMap k (post D p) = InnerHornGlue.hornMap k D ≫
    p.map (D.obj 0) (D.obj (Fin.last (n + 1))) := by
  apply Multicofork.IsColimit.hom_ext (InnerHornDiagram.isColimit k)
  intro l
  change SSet.Subcomplex.homOfLE (InnerHornDiagram.facet_le k l) ≫
      InnerHornGlue.hornMap k (post D p) =
    SSet.Subcomplex.homOfLE (InnerHornDiagram.facet_le k l) ≫
      InnerHornGlue.hornMap k D ≫ p.map (D.obj 0) (D.obj (Fin.last (n + 1)))
  rw [InnerHornGlue.hornMap_restrict, ← Category.assoc, InnerHornGlue.hornMap_restrict]
  exact facetEvaluation_post k D p l

end
end DaggerNativeInnerHornFacePostcomposition
