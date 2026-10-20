import OriginalFlagFlankFunctor
import Mathlib.Order.Hom.Basic

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {T : NecklaceCode} {n : ℕ} (F : Flag.{u} T n) (hF : Flanked F)

include hF in
theorem flanked_selectedVertices (v : Fin (T.len + 1)) : v ∈ selectedVertices F := by
  apply (mem_selectedVertices F v).mpr
  rw [hF.2]
  exact Set.mem_univ _

include hF in
theorem flanked_selectedJoints : selectedJoints F = T.joints := by
  ext v
  rw [mem_selectedJoints, hF.1]
  rfl

/-- The inverse of the actual finite recoding, with its prescribed original vertex. -/
def inverseOrder : Fin (T.len + 1) →o Fin (flankLen F + 1) where
  toFun v := ((selectedVertices F).orderIsoOfFin (flank_card F)).symm
    ⟨v, flanked_selectedVertices F hF v⟩
  monotone' _ _ hvw :=
    ((selectedVertices F).orderIsoOfFin (flank_card F)).symm.monotone hvw

theorem embedding_inverseOrder (v : Fin (T.len + 1)) :
    flankEmbedding F (inverseOrder F hF v) = v := congrArg Subtype.val
  (((selectedVertices F).orderIsoOfFin (flank_card F)).apply_symm_apply
    ⟨v, flanked_selectedVertices F hF v⟩)

theorem inverseOrder_embedding (v : Fin (flankLen F + 1)) :
    inverseOrder F hF (flankEmbedding F v) = v := by
  apply (flankEmbedding F).injective
  exact embedding_inverseOrder F hF (flankEmbedding F v)

def recodingOrderIso : Fin (flankLen F + 1) ≃o Fin (T.len + 1) :=
  OrderIso.ofHomInv (flankEmbedding F).toOrderHom (inverseOrder F hF)
    (DFunLike.ext _ _ (embedding_inverseOrder F hF))
    (DFunLike.ext _ _ (inverseOrder_embedding F hF))

theorem inverseOrder_first : inverseOrder F hF 0 = 0 := by
  apply (flankEmbedding F).injective
  rw [embedding_inverseOrder, flankEmbedding_first]

theorem inverseOrder_last :
    inverseOrder F hF (Fin.last T.len) = Fin.last (flankLen F) := by
  apply (flankEmbedding F).injective
  rw [embedding_inverseOrder, flankEmbedding_last]

theorem inverseOrder_no_joint (b : T.Bead) (v : Fin (flankLen F + 1))
    (hv : v ∈ (flankCode F).joints)
    (hl : inverseOrder F hF b.left < v) (hr : v < inverseOrder F hF b.right) : False := by
  have hj : flankEmbedding F v ∈ T.joints := by
    rw [← flanked_selectedJoints F hF]
    exact (Finset.mem_filter.mp hv).2
  have hleft := (flankEmbedding F).strictMono hl
  have hright := (flankEmbedding F).strictMono hr
  rw [embedding_inverseOrder] at hleft hright
  exact b.no_joint _ hj hleft hright

theorem inverseOrder_beadCondition :
    BeadImageCondition (T := T) (U := flankCode F) (inverseOrder F hF) := by
  intro b
  obtain ⟨c, hc⟩ := interval_in_original_bead (flankCode F)
    (inverseOrder F hF b.left) (inverseOrder F hF b.right)
    ((recodingOrderIso F hF).symm.strictMono b.lt) (inverseOrder_no_joint F hF b)
  left
  refine ⟨c, ?_⟩
  intro v hv
  obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
  exact hc _ (Finset.mem_Icc.mpr
    ⟨(inverseOrder F hF).monotone hl, (inverseOrder F hF).monotone hr⟩)

def recodingInverse : NecklaceCode.Hom.{u} T (flankCode F) where
  map := orderLift (T := T) (U := flankCode F)
    (inverseOrder F hF) (inverseOrder_beadCondition F hF)
  first := by
    apply (flankCode F).verticesEquiv.injective
    have h := orderLift_vertices (T := T) (U := flankCode F)
      (inverseOrder F hF) (inverseOrder_beadCondition F hF) (ULift.up 0 : Vertices.{u} T)
    change _ = ULift.up (inverseOrder F hF 0) at h
    rw [inverseOrder_first] at h
    simpa only [mapVertices, first, Equiv.apply_symm_apply] using h
  last := by
    apply (flankCode F).verticesEquiv.injective
    have h := orderLift_vertices (T := T) (U := flankCode F)
      (inverseOrder F hF) (inverseOrder_beadCondition F hF)
      (ULift.up (Fin.last T.len) : Vertices.{u} T)
    change _ = ULift.up (inverseOrder F hF (Fin.last T.len)) at h
    rw [inverseOrder_last] at h
    simpa only [mapVertices, last, Equiv.apply_symm_apply] using h

theorem recodingInverse_vertices (v : Vertices.{u} T) :
    mapVertices (recodingInverse F hF).map v = ULift.up (inverseOrder F hF v.down) :=
  orderLift_vertices (T := T) (U := flankCode F)
    (inverseOrder F hF) (inverseOrder_beadCondition F hF) v

theorem recodingInverse_inclusion :
    (recodingInverse F hF).map ≫ (flankInclusion F).map = 𝟙 T.toSSet := by
  apply hom_ext_vertices
  funext v
  rw [mapVertices_comp, mapVertices_id]
  change mapVertices (flankInclusion F).map (mapVertices (recodingInverse F hF).map v) = v
  rw [recodingInverse_vertices, flankInclusion_vertex]
  apply ULift.ext
  exact embedding_inverseOrder F hF v.down

theorem inclusion_recodingInverse :
    (flankInclusion F).map ≫ (recodingInverse F hF).map = 𝟙 (flankCode F).toSSet := by
  apply hom_ext_vertices
  funext v
  rw [mapVertices_comp, mapVertices_id]
  change mapVertices (recodingInverse F hF).map (mapVertices (flankInclusion F).map v) = v
  rw [flankInclusion_vertex, recodingInverse_vertices]
  apply ULift.ext
  exact inverseOrder_embedding F hF v.down

theorem recodingInverse_flag : NecklaceCode.Flag.map (recodingInverse F hF) F = flankFlag F := by
  apply NecklaceCode.Flag.ext
  intro i
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change flankVertex F (mapVertices (recodingInverse F hF).map w) ∈ F.chain i
    rw [recodingInverse_vertices]
    have hh : flankVertex F (ULift.up (inverseOrder F hF w.down)) = w := by
      apply ULift.ext
      exact embedding_inverseOrder F hF w.down
    simpa only [hh] using hw
  · intro hv
    refine ⟨flankVertex F v, hv, ?_⟩
    rw [recodingInverse_vertices]
    apply ULift.ext
    exact inverseOrder_embedding F hF v.down

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

def recodingInverseOver (p : Degree X a b n) (hp : Flanked p.2) :
    p.1 ⟶ (flankDegreeObj p).1 where
  hom := recodingInverse p.2 hp
  w := by
    change (recodingInverse p.2 hp).map ≫
      ((flankInclusion p.2).map ≫ p.1.map) = p.1.map
    rw [← Category.assoc, recodingInverse_inclusion, Category.id_comp]

/-- Both inverse laws are literal whole maps over the original X, not code equalities. -/
def recodingIso (p : Degree X a b n) (hp : Flanked p.2) : flankDegreeObj p ≅ p where
  hom := inclusionDegree p
  inv := CategoryOfElements.homMk _ _ (recodingInverseOver p hp)
    (recodingInverse_flag p.2 hp)
  hom_inv_id := by
    apply Subtype.ext
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    exact inclusion_recodingInverse p.2 hp
  inv_hom_id := by
    apply Subtype.ext
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    exact recodingInverse_inclusion p.2 hp

theorem recodingIso_hom (p : Degree X a b n) (hp : Flanked p.2) :
    (recodingIso p hp).hom = (inclusion X a b n).app p := rfl

end

end DaggerOriginalFlagFlankification
