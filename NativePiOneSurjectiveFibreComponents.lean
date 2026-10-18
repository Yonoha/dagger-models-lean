import NativeFibrationComponentFibre

/-! Actual pi-one surjectivity kills native fibre monodromy and identifies fibre components. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra
open SSet SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativeFibrationComponentFibre
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePiOneSurjectiveFibreComponents
noncomputable section

theorem fibre_monodromy_trivial_of_pi_one_surjective {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [IsFibrant B]
    (hp : ∀ (e : E _⦋0⦌) (b : B _⦋0⦌) (he : p.app _ e = b),
      Function.Surjective (mapπ p 1 e b he))
    (b : B _⦋0⦌) (g : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b)
    (u : (Subcomplex.fiber p b : SSet.{u}).π₀) : π₀FiberAction p g u = u := by
  have : IsFibrant E := isFibrant_of_fibration p
  obtain ⟨e, rfl⟩ := SSet.π₀.mk_surjective u
  have he : p.app _ e.val = b := by
    simpa only [Subcomplex.mem_fiber_obj_zero_iff] using e.property
  have hd : ∀ r : π 1 B b, HomotopySequence.δ' p he 0 0 r = 1 := by
    intro r
    obtain ⟨s, rfl⟩ := hp e.val b he r
    exact HomotopySequence.δ'_map₂_apply (p := p) he s 0
  have hh := (hd (homEquiv g)).trans (hd (homEquiv (𝟙 (FundamentalGroupoid.mk b)))).symm
  simp only [HomotopySequence.δ'_eq_π₀FiberAction, Equiv.symm_apply_apply,
    π₀FiberAction_id] at hh
  exact (π₀EquivπZero _).injective hh

theorem componentFibreMap_bijective_of_pi_one_surjective {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [IsFibrant B]
    (hp : ∀ (e : E _⦋0⦌) (b : B _⦋0⦌) (he : p.app _ e = b),
      Function.Surjective (mapπ p 1 e b he)) (b : B _⦋0⦌) :
    Function.Bijective (componentFibreMap p b) :=
  componentFibreMap_bijective p b (fibre_monodromy_trivial_of_pi_one_surjective p hp b)

theorem fibre_inclusion_components_injective_of_pi_one_surjective {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] [IsFibrant B]
    (hp : ∀ (e : E _⦋0⦌) (b : B _⦋0⦌) (he : p.app _ e = b),
      Function.Surjective (mapπ p 1 e b he)) (b : B _⦋0⦌) :
    Function.Injective (SSet.mapπ₀ (Subcomplex.fiber p b).ι) :=
  DaggerNativeFibrationFibreComponentOrbits.fibre_component_injective_of_trivial_action p b
    (fibre_monodromy_trivial_of_pi_one_surjective p hp b)

end
end DaggerNativePiOneSurjectiveFibreComponents
