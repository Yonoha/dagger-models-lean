import ChosenNecklaceBeadCoordinates

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable {T U : NecklaceCode}

theorem constant_mem_complex (T : NecklaceCode) (v : Fin (T.len + 1)) {n : ℕ}
    (x : (Δ[T.len] : SSet.{u}).obj (op ⦋n⦌)) (hx : ∀ i, x i = v) :
    x ∈ T.complex.obj (op ⦋n⦌) := by
  apply (T.mem_complex_iff x).mpr
  by_cases hv : v = 0
  · exact Or.inl (fun i ↦ (hx i).trans hv)
  · obtain ⟨b, hb⟩ := T.exists_bead_interval v hv
    exact Or.inr ⟨b, fun i ↦ (hx i).symm ▸ hb⟩

/-- Exactly the whole-bead image condition; collapsed beads may land at any target vertex. -/
def BeadImageCondition (f : Fin (T.len + 1) →o Fin (U.len + 1)) : Prop :=
  ∀ b : T.Bead,
    (∃ c : U.Bead, ∀ v ∈ b.interval, f v ∈ c.interval) ∨
      (∃ v, ∀ w ∈ b.interval, f w = v)

def ambientOrderMap (f : Fin (T.len + 1) →o Fin (U.len + 1)) :
    toSSet.{u} T ⟶ Δ[U.len] :=
  T.inclusion ≫ SSet.stdSimplex.map (SimplexCategory.Hom.mk f)

theorem ambientOrderMap_apply (f : Fin (T.len + 1) →o Fin (U.len + 1))
    {n : ℕ} (x : (toSSet.{u} T).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    (ambientOrderMap f).app _ x i = f (T.inclusion.app _ x i) := rfl

theorem ambientOrderMap_mem (f : Fin (T.len + 1) →o Fin (U.len + 1))
    (hf : BeadImageCondition f) (q : SimplexCategoryᵒᵖ) (x : (toSSet.{u} T).obj q) :
    (ambientOrderMap f).app q x ∈ U.complex.obj q := by
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  have hx : T.inclusion.app _ x ∈ T.complex.obj (op ⦋n⦌) :=
    (T.complexIso.hom.app _ x).property
  rcases (T.mem_complex_iff _).mp hx with hx | ⟨b, hx⟩
  · apply constant_mem_complex U (f 0)
    intro i
    rw [ambientOrderMap_apply, hx i]
  · rcases hf b with ⟨c, hc⟩ | ⟨v, hv⟩
    · apply (U.mem_complex_iff _).mpr
      right
      refine ⟨c, ?_⟩
      intro i
      rw [ambientOrderMap_apply]
      exact hc _ (hx i)
    · apply constant_mem_complex U v
      intro i
      rw [ambientOrderMap_apply]
      exact hv _ (hx i)

def orderLift (f : Fin (T.len + 1) →o Fin (U.len + 1)) (hf : BeadImageCondition f) :
    toSSet.{u} T ⟶ toSSet.{u} U :=
  SSet.Subcomplex.lift (ambientOrderMap f) (by
    rintro q y ⟨x, rfl⟩
    exact ambientOrderMap_mem f hf q x) ≫ U.complexIso.inv

theorem orderLift_inclusion (f : Fin (T.len + 1) →o Fin (U.len + 1))
    (hf : BeadImageCondition f) :
    orderLift f hf ≫ U.inclusion = ambientOrderMap f := by
  simp only [orderLift, inclusion, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

theorem orderLift_vertices (f : Fin (T.len + 1) →o Fin (U.len + 1))
    (hf : BeadImageCondition f) (v : Vertices.{u} T) :
    mapVertices (orderLift f hf) v = ULift.up (f v.down) := by
  apply ULift.ext
  change SSet.stdSimplex.obj₀Equiv
    (U.inclusion.app _ ((orderLift f hf).app _ (T.verticesEquiv.symm v))) = f v.down
  have h := congrFun (NatTrans.congr_app (orderLift_inclusion f hf) (op ⦋0⦌))
    (T.verticesEquiv.symm v)
  change U.inclusion.app _ ((orderLift f hf).app _ (T.verticesEquiv.symm v)) =
    (ambientOrderMap f).app _ (T.verticesEquiv.symm v) at h
  rw [h]
  change f (SSet.stdSimplex.obj₀Equiv (T.inclusion.app _ (T.verticesEquiv.symm v))) = _
  rw [T.inclusion_vertex]

theorem orderLift_unique (f : Fin (T.len + 1) →o Fin (U.len + 1))
    (hf : BeadImageCondition f) (g : toSSet.{u} T ⟶ toSSet.{u} U)
    (hg : ∀ v, mapVertices g v = ULift.up (f v.down)) : g = orderLift f hf := by
  apply hom_ext_vertices
  funext v
  exact (hg v).trans (orderLift_vertices f hf v).symm

end

end DaggerChosenRigidificationNecklace.NecklaceCode
