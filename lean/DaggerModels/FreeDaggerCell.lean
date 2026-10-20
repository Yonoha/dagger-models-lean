import DaggerModels.FreeDaggerCofibration
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# The simplices of an actual free dagger boundary cell

These lemmas describe the explicit two-copy free completion used in Part I,
`dj.lem.free-cof`. Outside the free boundary, a positive-dimensional cell has
exactly two copies of each epimorphism onto the standard simplex. A zero-cell
has only one copy. No characteristic map is assumed to be a monomorphism.
-/

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DaggerModels
namespace FreeDaggerCell

open FreeDaggerPushout

/-- Membership of a left-copy simplex in the free image is ordinary image membership.
This holds for any map, without a monomorphism assumption. -/
theorem inl_mem_range_mapUnderlying_iff {A B : SSet.{u}} (f : A ⟶ B)
    (m : SimplexCategoryᵒᵖ) (b : B.obj m) :
    (inl B).app m b ∈ Set.range ((mapUnderlying f).app m) ↔ b ∈ Set.range (f.app m) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain (⟨a, rfl⟩ | ⟨a, rfl⟩) := exists_copy A m x
    · rw [mapUnderlying_inl_apply] at hx
      exact ⟨a, inl_app_injective B m hx⟩
    · rw [mapUnderlying_inr_apply] at hx
      obtain ⟨v, hb, ha⟩ := (inl_eq_inr_iff B m b _).1 hx.symm
      change (SSetVertices.inclusion B).app m v = f.app m (SSet.opObjEquiv a) at ha
      exact ⟨SSet.opObjEquiv a, ha.symm.trans hb⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(inl A).app m a, mapUnderlying_inl_apply f m a⟩

/-- The analogous exact image criterion for the right copy. -/
theorem inr_mem_range_mapUnderlying_iff {A B : SSet.{u}} (f : A ⟶ B)
    (m : SimplexCategoryᵒᵖ) (b : B.op.obj m) :
    (inr B).app m b ∈ Set.range ((mapUnderlying f).app m) ↔
      b ∈ Set.range ((SSet.opFunctor.map f).app m) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain (⟨a, rfl⟩ | ⟨a, rfl⟩) := exists_copy A m x
    · rw [mapUnderlying_inl_apply] at hx
      obtain ⟨v, ha, hb⟩ := (inl_eq_inr_iff B m _ b).1 hx
      change (SSetVertices.opInclusion B).app m v =
        (SSet.opFunctor.map f).app m (SSet.opObjEquiv.symm a) at ha
      exact ⟨SSet.opObjEquiv.symm a, ha.symm.trans hb⟩
    · rw [mapUnderlying_inr_apply] at hx
      exact ⟨a, inr_app_injective B m hx⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(inr A).app m a, mapUnderlying_inr_apply f m a⟩

/-- The free image of the actual standard boundary inclusion. -/
def boundaryRange (n k : ℕ) : Set ((underlying (Δ[n] : SSet.{u})) _⦋k⦌) :=
  Set.range ((mapUnderlying (SSet.boundary.{u} n).ι).app (op ⦋k⦌))

/-- The left-copy simplex indexed by a simplex-category morphism. -/
noncomputable def left {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌) :
    (underlying (Δ[n] : SSet.{u})) _⦋k⦌ :=
  (inl (Δ[n] : SSet.{u})).app (op ⦋k⦌) (SSet.stdSimplex.objEquiv.symm α)

/-- The right-copy simplex with the same simplex label. Its simplicial operators
are reversed; its evaluation under a characteristic map uses reversal. -/
noncomputable def right {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌) :
    (underlying (Δ[n] : SSet.{u})) _⦋k⦌ :=
  (inr (Δ[n] : SSet.{u})).app (op ⦋k⦌)
    (SSet.opObjEquiv.symm (SSet.stdSimplex.objEquiv.symm α))

theorem simplex_mem_range_boundary_iff {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌) :
    SSet.stdSimplex.objEquiv.{u}.symm α ∈
      Set.range ((SSet.boundary.{u} n).ι.app (op ⦋k⦌)) ↔ ¬ Epi α := by
  change (∃ x : {x : (Δ[n] : SSet.{u}) _⦋k⦌ | x ∈ (SSet.boundary n).obj (op ⦋k⦌)},
    x.val = SSet.stdSimplex.objEquiv.symm α) ↔ ¬ Epi α
  rw [Subtype.exists]
  simp only [exists_prop, exists_eq_right]
  change ¬ Function.Surjective α.toOrderHom ↔ ¬ Epi α
  rw [SimplexCategory.epi_iff_surjective]

/-- Exactly the non-epimorphic simplex labels belong to the free boundary. -/
theorem left_mem_boundaryRange_iff {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌) :
    left.{u} α ∈ boundaryRange n k ↔ ¬ Epi α :=
  (inl_mem_range_mapUnderlying_iff (SSet.boundary n).ι _ _).trans
    (simplex_mem_range_boundary_iff α)

theorem right_mem_boundaryRange_iff {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌) :
    right.{u} α ∈ boundaryRange n k ↔ ¬ Epi α :=
  (inr_mem_range_mapUnderlying_iff (SSet.boundary n).ι _ _).trans
    (simplex_mem_range_boundary_iff α)

/-- Each individual copy keeps its simplex labels injectively. -/
theorem left_injective (n k : ℕ) :
    Function.Injective (left.{u} (n := n) (k := k)) := by
  intro α β h
  apply SSet.stdSimplex.objEquiv.symm.injective
  exact inl_app_injective (Δ[n] : SSet.{u}) (op ⦋k⦌) h

theorem right_injective (n k : ℕ) :
    Function.Injective (right.{u} (n := n) (k := k)) := by
  intro α β h
  apply SSet.stdSimplex.objEquiv.symm.injective
  exact inr_app_injective (Δ[n] : SSet.{u}) (op ⦋k⦌) h

/-- An epimorphic simplex in positive cell dimension cannot be a total vertex degeneracy. -/
theorem epi_not_vertex {n k : ℕ} (hn : 0 < n) (α : ⦋k⦌ ⟶ ⦋n⦌) [Epi α]
    (v : (Δ[n] : SSet.{u}) _⦋0⦌) :
    (SSetVertices.inclusion (Δ[n] : SSet.{u})).app (op ⦋k⦌) v ≠
      SSet.stdSimplex.objEquiv.symm α := by
  intro h
  have hα : SimplexCategory.const ⦋k⦌ ⦋0⦌ 0 ≫ SSet.stdSimplex.objEquiv v = α :=
    congrArg SSet.stdSimplex.objEquiv h
  have : Epi (SimplexCategory.const ⦋k⦌ ⦋0⦌ 0 ≫ SSet.stdSimplex.objEquiv v) :=
    hα ▸ inferInstance
  have : Epi (SSet.stdSimplex.objEquiv v) :=
    epi_of_epi (SimplexCategory.const ⦋k⦌ ⦋0⦌ 0) (SSet.stdSimplex.objEquiv v)
  have hle : n ≤ 0 := SimplexCategory.le_of_epi (SSet.stdSimplex.objEquiv v)
  omega

/-- The two interior copies of a positive-dimensional cell are distinct. -/
theorem left_ne_right {n k : ℕ} (hn : 0 < n)
    (α β : ⦋k⦌ ⟶ ⦋n⦌) [Epi α] : left.{u} α ≠ right β := by
  intro h
  obtain ⟨v, hv, _⟩ := (inl_eq_inr_iff (Δ[n] : SSet.{u}) (op ⦋k⦌) _ _).1 h
  exact epi_not_vertex hn α v hv

/-- All vertices and all their degeneracies in a zero-cell have a single copy. -/
theorem left_eq_right_zero {k : ℕ} (α : ⦋k⦌ ⟶ ⦋0⦌) : left.{u} α = right α := by
  apply (inl_eq_inr_iff (Δ[0] : SSet.{u}) (op ⦋k⦌) _ _).2
  refine ⟨SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌), ?_, ?_⟩
  · change SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.const ⦋k⦌ ⦋0⦌ 0 ≫ 𝟙 _) = SSet.stdSimplex.objEquiv.symm α
    rw [Category.comp_id, SimplexCategory.eq_const_to_zero α]
  · change SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.const ⦋k⦌ ⦋0⦌ 0 ≫ 𝟙 _) = SSet.stdSimplex.objEquiv.symm α
    rw [Category.comp_id, SimplexCategory.eq_const_to_zero α]

/-- `false` denotes the left copy and `true` the right copy. -/
noncomputable def copy {n k : ℕ} (side : Bool) (α : ⦋k⦌ ⟶ ⦋n⦌) :
    (underlying (Δ[n] : SSet.{u})) _⦋k⦌ :=
  match side with
  | false => left α
  | true => right α

@[simp] theorem copy_false {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌) :
    copy.{u} false α = left α := rfl

@[simp] theorem copy_true {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌) :
    copy.{u} true α = right α := rfl

theorem copy_mem_boundaryRange_iff {n k : ℕ} (side : Bool) (α : ⦋k⦌ ⟶ ⦋n⦌) :
    copy.{u} side α ∈ boundaryRange n k ↔ ¬ Epi α := by
  cases side
  · exact left_mem_boundaryRange_iff α
  · exact right_mem_boundaryRange_iff α

/-- Every simplex outside the free boundary has a copy and an epimorphic label. -/
theorem exists_copy_epi {n k : ℕ} (x : (underlying (Δ[n] : SSet.{u})) _⦋k⦌)
    (hx : x ∉ boundaryRange n k) :
    ∃ (side : Bool) (α : ⦋k⦌ ⟶ ⦋n⦌), Epi α ∧ copy side α = x := by
  obtain (⟨a, ha⟩ | ⟨b, hb⟩) := exists_copy (Δ[n] : SSet.{u}) (op ⦋k⦌) x
  · have he : copy false (SSet.stdSimplex.objEquiv a) = x := by
      simpa only [copy_false, left, Equiv.symm_apply_apply] using ha
    refine ⟨false, SSet.stdSimplex.objEquiv a, ?_, he⟩
    by_contra hnot
    exact hx (he ▸ (copy_mem_boundaryRange_iff false _).2 hnot)
  · have he : copy true (SSet.stdSimplex.objEquiv (SSet.opObjEquiv b)) = x := by
      simpa only [copy_true, right, Equiv.symm_apply_apply] using hb
    refine ⟨true, SSet.stdSimplex.objEquiv (SSet.opObjEquiv b), ?_, he⟩
    by_contra hnot
    exact hx (he ▸ (copy_mem_boundaryRange_iff true _).2 hnot)

/-- In positive cell dimension the copy and epimorphic label are unique. -/
theorem copy_epi_injective {n k : ℕ} (hn : 0 < n) :
    Function.Injective (fun p : Bool × {α : ⦋k⦌ ⟶ ⦋n⦌ // Epi α} ↦
      copy.{u} p.1 p.2.val) := by
  rintro ⟨side, α, hα⟩ ⟨side', β, hβ⟩ h
  cases side <;> cases side'
  · have hαβ := left_injective n k h
    exact Prod.ext rfl (Subtype.ext hαβ)
  · let : Epi α := hα
    exact False.elim (left_ne_right hn α β h)
  · let : Epi β := hβ
    exact False.elim (left_ne_right hn β α h.symm)
  · have hαβ := right_injective n k h
    exact Prod.ext rfl (Subtype.ext hαβ)

theorem existsUnique_copy_epi {n k : ℕ} (hn : 0 < n)
    (x : (underlying (Δ[n] : SSet.{u})) _⦋k⦌) (hx : x ∉ boundaryRange n k) :
    ∃! p : Bool × {α : ⦋k⦌ ⟶ ⦋n⦌ // Epi α}, copy p.1 p.2.val = x := by
  obtain ⟨side, α, hα, he⟩ := exists_copy_epi x hx
  refine ⟨⟨side, α, hα⟩, he, ?_⟩
  intro p hp
  exact copy_epi_injective hn (hp.trans he.symm)

/-- A zero-cell has one simplex label in each degree, with no duplicate copy. -/
theorem existsUnique_left_zero {k : ℕ}
    (x : (underlying (Δ[0] : SSet.{u})) _⦋k⦌) :
    ∃! α : ⦋k⦌ ⟶ ⦋0⦌, left α = x := by
  have he : ∃ α : ⦋k⦌ ⟶ ⦋0⦌, left α = x := by
    obtain (⟨a, ha⟩ | ⟨b, hb⟩) := exists_copy (Δ[0] : SSet.{u}) (op ⦋k⦌) x
    · exact ⟨SSet.stdSimplex.objEquiv a, by
        simpa only [left, Equiv.symm_apply_apply] using ha⟩
    · refine ⟨SSet.stdSimplex.objEquiv (SSet.opObjEquiv b), ?_⟩
      rw [left_eq_right_zero]
      simpa only [right, Equiv.symm_apply_apply] using hb
  obtain ⟨α, hα⟩ := he
  exact ⟨α, hα, fun β hβ ↦ left_injective 0 k (hβ.trans hα.symm)⟩

/-- The left copy evaluates along the ordinary simplex operator. -/
theorem desc_left_apply {Y : DaggerSSet.{u}} {n k : ℕ}
    (σ : Y.toSSet _⦋n⦌) (α : ⦋k⦌ ⟶ ⦋n⦌) :
    (desc (SSet.yonedaEquiv.symm σ)).hom.app (op ⦋k⦌) (left α) =
      Y.toSSet.map α.op σ :=
  congrFun (NatTrans.congr_app (inl_descUnderlying (SSet.yonedaEquiv.symm σ))
    (op ⦋k⦌)) (SSet.stdSimplex.objEquiv.symm α)

/-- The right copy evaluates on the dagger simplex with the reversed operator.
In particular, no monicity of the characteristic map is used. -/
theorem desc_right_apply {Y : DaggerSSet.{u}} {n k : ℕ}
    (σ : Y.toSSet _⦋n⦌) (α : ⦋k⦌ ⟶ ⦋n⦌) :
    (desc (SSet.yonedaEquiv.symm σ)).hom.app (op ⦋k⦌) (right α) =
      Y.toSSet.map (SimplexCategory.rev.map α).op (Y.daggerSimplex σ) := by
  have he := congrFun
    (NatTrans.congr_app (inr_descUnderlying (SSet.yonedaEquiv.symm σ)) (op ⦋k⦌))
    (SSet.opObjEquiv.symm (SSet.stdSimplex.objEquiv.symm α))
  change (desc (SSet.yonedaEquiv.symm σ)).hom.app (op ⦋k⦌) (right α) =
    Y.daggerSimplex (Y.toSSet.map α.op σ) at he
  exact he.trans (congrFun (Y.dagger.naturality α.op) σ)

end FreeDaggerCell
end DaggerModels
