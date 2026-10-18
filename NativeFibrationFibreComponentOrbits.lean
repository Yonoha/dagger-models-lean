import TopCatModelCategory.ModelCategorySSet
import TopCatModelCategory.SSet.HomotopySequenceAction

/-! Equality of fibre components in the total space is exactly a native loop-action orbit. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra
open SSet SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFibrationFibreComponentOrbits
noncomputable section

theorem fibre_component_eq_iff_loop_orbit {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [IsFibrant B] (b : B _⦋0⦌)
    (u v : (Subcomplex.fiber p b : SSet.{u}).π₀) :
    SSet.mapπ₀ (Subcomplex.fiber p b).ι u = SSet.mapπ₀ (Subcomplex.fiber p b).ι v ↔
      ∃ g : (FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b),
        π₀FiberAction p g u = v := by
  have : IsFibrant E := isFibrant_of_fibration p
  obtain ⟨u, rfl⟩ := SSet.π₀.mk_surjective u
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective v
  have hu : p.app _ u.val = b := by
    simpa only [Subcomplex.mem_fiber_obj_zero_iff] using u.property
  have hv : p.app _ v.val = b := by
    simpa only [Subcomplex.mem_fiber_obj_zero_iff] using v.property
  constructor
  · intro h
    change SSet.π₀.mk u.val = SSet.π₀.mk v.val at h
    obtain ⟨e⟩ := (SSet.KanComplex.π₀_mk_eq_π₀_mk_iff _ _).mp h
    let q : Edge (FundamentalGroupoid.mk b) (FundamentalGroupoid.mk b) :=
      Edge.mk (e.map ≫ p) (by rw [e.comm₀_assoc, SSet.const_comp, hu])
        (by rw [e.comm₁_assoc, SSet.const_comp, hv])
    refine ⟨FundamentalGroupoid.homMk q, (π₀FiberAction_mk_eq_iff p q u v).mpr ?_⟩
    exact ⟨{ map := e.map, map_p := rfl, δ₁_map := e.comm₀, δ₀_map := e.comm₁ }⟩
  · rintro ⟨g, hg⟩
    obtain ⟨q, rfl⟩ := FundamentalGroupoid.homMk_surjective g
    obtain ⟨h⟩ := (π₀FiberAction_mk_eq_iff p q u v).mp hg
    change SSet.π₀.mk u.val = SSet.π₀.mk v.val
    apply (SSet.KanComplex.π₀_mk_eq_π₀_mk_iff _ _).mpr
    exact ⟨Edge.mk h.map h.δ₁_map h.δ₀_map⟩

theorem fibre_component_injective_of_trivial_action {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [IsFibrant B] (b : B _⦋0⦌)
    (h : ∀ (g : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b)
      (u : (Subcomplex.fiber p b : SSet.{u}).π₀), π₀FiberAction p g u = u) :
    Function.Injective (SSet.mapπ₀ (Subcomplex.fiber p b).ι) := by
  intro u v huv
  obtain ⟨g, hg⟩ := (fibre_component_eq_iff_loop_orbit p b u v).mp huv
  exact (h g u).symm.trans hg

end
end DaggerNativeFibrationFibreComponentOrbits
