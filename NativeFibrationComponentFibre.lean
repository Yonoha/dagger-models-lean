import NativeFibrationFibreComponentOrbits

/-! Under trivial native monodromy, components of the fibre equal the fibre of components. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra
open SSet SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativeFibrationFibreComponentOrbits
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFibrationComponentFibre
noncomputable section

def componentFibreMap {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (Subcomplex.fiber p b : SSet.{u}).π₀ →
      {c : E.π₀ // SSet.mapπ₀ p c = SSet.π₀.mk b} :=
  fun c ↦ ⟨SSet.mapπ₀ (Subcomplex.fiber p b).ι c, by
    obtain ⟨e, rfl⟩ := SSet.π₀.mk_surjective c
    change SSet.π₀.mk (p.app _ e.val) = SSet.π₀.mk b
    congr 1
    simpa only [Subcomplex.mem_fiber_obj_zero_iff] using e.property⟩

theorem componentFibreMap_surjective {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [IsFibrant B] (b : B _⦋0⦌) :
    Function.Surjective (componentFibreMap p b) := by
  have : IsFibrant E := isFibrant_of_fibration p
  rintro ⟨c, hc⟩
  obtain ⟨e, rfl⟩ := SSet.π₀.mk_surjective c
  change SSet.π₀.mk (p.app _ e) = SSet.π₀.mk b at hc
  obtain ⟨q⟩ := (SSet.KanComplex.π₀_mk_eq_π₀_mk_iff _ _).mp hc
  obtain ⟨e', ⟨h⟩⟩ := FiberActionStruct.nonempty p q e rfl
  let v : (Subcomplex.fiber p b : SSet.{u}) _⦋0⦌ :=
    ⟨e', by simpa only [Subcomplex.mem_fiber_obj_zero_iff] using h.app_one⟩
  refine ⟨SSet.π₀.mk v, Subtype.ext ?_⟩
  change SSet.π₀.mk e' = SSet.π₀.mk e
  symm
  apply (SSet.KanComplex.π₀_mk_eq_π₀_mk_iff _ _).mpr
  exact ⟨Edge.mk h.map h.δ₁_map h.δ₀_map⟩

theorem componentFibreMap_bijective {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [IsFibrant B] (b : B _⦋0⦌)
    (h : ∀ (g : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b)
      (u : (Subcomplex.fiber p b : SSet.{u}).π₀), π₀FiberAction p g u = u) :
    Function.Bijective (componentFibreMap p b) := by
  refine ⟨?_, componentFibreMap_surjective p b⟩
  intro u v huv
  exact fibre_component_injective_of_trivial_action p b h (congrArg Subtype.val huv)

def componentFibreEquiv {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [IsFibrant B] (b : B _⦋0⦌)
    (h : ∀ (g : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b)
      (u : (Subcomplex.fiber p b : SSet.{u}).π₀), π₀FiberAction p g u = u) :
    (Subcomplex.fiber p b : SSet.{u}).π₀ ≃
      {c : E.π₀ // SSet.mapπ₀ p c = SSet.π₀.mk b} :=
  Equiv.ofBijective (componentFibreMap p b) (componentFibreMap_bijective p b h)

theorem componentFibreEquiv_val {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [IsFibrant B] (b : B _⦋0⦌)
    (h : ∀ (g : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b)
      (u : (Subcomplex.fiber p b : SSet.{u}).π₀), π₀FiberAction p g u = u)
    (u : (Subcomplex.fiber p b : SSet.{u}).π₀) :
    (componentFibreEquiv p b h u).val = SSet.mapπ₀ (Subcomplex.fiber p b).ι u := rfl

end
end DaggerNativeFibrationComponentFibre
