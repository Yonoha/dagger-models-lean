import ChosenNecklaceFlagEvaluation
import ChosenFlagEnrichment
import ChosenNecklaceEnrichedFunctor

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode)

theorem necklaceFlagEvaluation_identity (x : (toSSet.{u} T).obj (op ⦋0⦌)) :
    flagIdentity (toSSet T) x ≫ necklaceFlagEvaluation T =
      pathId (⟨T.verticesEquiv x⟩ : NecklaceThickening.{u} T) := by
  ext q v
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change mapVertices (NecklacesOver.point x).map '' Set.univ = {T.verticesEquiv x}
    ext w
    constructor
    · rintro ⟨k, _, he⟩
      have hk : k = ULift.up (0 : Fin 1) := by
        apply ULift.ext
        apply Fin.ext
        change k.down.val = 0
        have hk := k.down.isLt
        change k.down.val < 1 at hk
        omega
      subst k
      exact Set.mem_singleton_iff.mpr
        (he.symm.trans (over_map_vertices_first T (NecklacesOver.point x)))
    · intro hw
      refine ⟨ULift.up 0, Set.mem_univ _, ?_⟩
      exact (over_map_vertices_first T (NecklacesOver.point x)).trans
        (Set.mem_singleton_iff.mp hw).symm))

theorem necklaceFlagEvaluation_composition
    (x y z : (toSSet.{u} T).obj (op ⦋0⦌)) :
    flagComposition (toSSet T) x y z ≫ necklaceFlagEvaluation T =
      (necklaceFlagEvaluation T ⊗ₘ necklaceFlagEvaluation T) ≫
        pathComp ⟨T.verticesEquiv x⟩ ⟨T.verticesEquiv y⟩ ⟨T.verticesEquiv z⟩ := by
  ext q v
  rcases v with ⟨v, w⟩
  induction v using Quot.ind with | _ p
  induction w using Quot.ind with | _ r
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change mapVertices (NecklacesOver.wedge p.1 r.1).map ''
        (mapVertices (wedgeιLeft p.1.code r.1.code) '' p.2.chain i ∪
          mapVertices (wedgeιRight p.1.code r.1.code) '' r.2.chain i) =
      mapVertices p.1.map '' p.2.chain i ∪ mapVertices r.1.map '' r.2.chain i
    rw [Set.image_union, Set.image_image, Set.image_image]
    change (mapVertices (NecklacesOver.wedge p.1 r.1).map ∘
        mapVertices (wedgeιLeft p.1.code r.1.code)) '' p.2.chain i ∪
      (mapVertices (NecklacesOver.wedge p.1 r.1).map ∘
        mapVertices (wedgeιRight p.1.code r.1.code)) '' r.2.chain i = _
    rw [← mapVertices_comp, ← mapVertices_comp,
      NecklacesOver.wedge_left, NecklacesOver.wedge_right]))

/-- Full enriched evaluation on the original vertices and every original Hom of a necklace. -/
def necklaceFlagFunctor : E (toSSet.{u} T) ⟶ NC.{u} T where
  obj x := ⟨T.verticesEquiv x⟩
  map _ _ := necklaceFlagEvaluation T
  map_id x := necklaceFlagEvaluation_identity T x
  map_comp x y z := necklaceFlagEvaluation_composition T x y z

theorem necklaceFlagFunctor_obj (x : (toSSet.{u} T).obj (op ⦋0⦌)) :
    (necklaceFlagFunctor T).obj x = ⟨T.verticesEquiv x⟩ := rfl

theorem necklaceFlagFunctor_original_hom (x y : (toSSet.{u} T).obj (op ⦋0⦌)) :
    (necklaceFlagFunctor T).map x y = necklaceFlagEvaluation T := rfl

end

end DaggerChosenRigidificationNecklace
