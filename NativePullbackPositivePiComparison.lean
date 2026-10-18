import NativePullbackPiExact

/-! The canonical positive-pi comparison for the actual pullback, by native exactness. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet SSet.KanComplex DaggerNativePullbackPiExact
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePullbackPositivePiComparison
noncomputable section

theorem positiveComparison_surjective {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    [Fibration p] [IsFibrant B] [IsFibrant C] (w : (pullback p q) _⦋0⦌) (n : ℕ) :
    Function.Surjective (positiveComparison p q w n) := by
  have : Fibration (pullback.snd p q) := inferInstance
  have : IsFibrant E := isFibrant_of_fibration p
  have : IsFibrant (pullback p q) := isFibrant_of_fibration (pullback.snd p q)
  rintro ⟨⟨a, c⟩, hac⟩
  have hd : HomotopySequence.δ' p (basepointEquation p q w) n 0
      (otherPi p q w (n + 1) c) = 1 := by
    rw [← hac]
    exact HomotopySequence.δ'_map₂_apply (p := p) (he := basepointEquation p q w) a 0
  have hc : HomotopySequence.δ' (pullback.snd p q) (e := w) rfl n 0 c = 1 := by
    apply (fibrePiMap_bijective p q w n).injective
    rw [fibre_delta_naturality]
    simpa only [fibrePiMap, mapπ_one] using hd
  obtain ⟨u, hu⟩ := HomotopySequence.exists_of_δ'_eq_one
    (p := pullback.snd p q) (he := rfl) hc
  have hur : rightPi p q w (n + 1) u = c := hu
  have hk : HomotopySequence.map₂ p (basepointEquation p q w) (n + 1)
      (a * (leftPi p q w (n + 1) u)⁻¹) = 1 := by
    change basePi p q w (n + 1) (a * (leftPi p q w (n + 1) u)⁻¹) = 1
    dsimp only [basePi]
    rw [mapπ_mul, mapπ_inv]
    change basePi p q w (n + 1) a *
      (basePi p q w (n + 1) (leftPi p q w (n + 1) u))⁻¹ = 1
    rw [hac, projection_compatibility, hur]
    exact mul_inv_cancel _
  obtain ⟨v, hv⟩ := HomotopySequence.exists_of_map₂_eq_one
    (p := p) (he := basepointEquation p q w) hk
  obtain ⟨t, ht⟩ := (fibrePiMap_bijective p q w (n + 1)).surjective v
  let z := HomotopySequence.map₁ (pullback.snd p q) rfl (n + 1) t * u
  have hl : leftPi p q w (n + 1) z = a := by
    dsimp only [z, leftPi]
    rw [mapπ_mul]
    change leftPi p q w (n + 1)
      (HomotopySequence.map₁ (pullback.snd p q) rfl (n + 1) t) *
        leftPi p q w (n + 1) u = a
    rw [leftPi_fibrePi, ht, hv]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hr : rightPi p q w (n + 1) z = c := by
    dsimp only [z, rightPi]
    rw [mapπ_mul]
    change rightPi p q w (n + 1)
      (HomotopySequence.map₁ (pullback.snd p q) rfl (n + 1) t) *
        rightPi p q w (n + 1) u = c
    rw [rightPi_fibre, hur, one_mul]
  exact ⟨z, Subtype.ext (Prod.ext hl hr)⟩

theorem joint_kernel_trivial {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    [Fibration p] [IsFibrant B] [IsFibrant C] (w : (pullback p q) _⦋0⦌) (n : ℕ)
    (hp : Function.Surjective (basePi p q w (n + 2)))
    (s : π (n + 1) (pullback p q) w)
    (hl : leftPi p q w (n + 1) s = 1) (hr : rightPi p q w (n + 1) s = 1) : s = 1 := by
  have : Fibration (pullback.snd p q) := inferInstance
  have : IsFibrant E := isFibrant_of_fibration p
  have : IsFibrant (pullback p q) := isFibrant_of_fibration (pullback.snd p q)
  obtain ⟨u, hu⟩ := HomotopySequence.exists_of_map₂_eq_one
    (p := pullback.snd p q) (he := rfl) hr
  have hk : HomotopySequence.map₁ p (basepointEquation p q w) (n + 1)
      (fibrePiMap p q w (n + 1) u) = 1 := by
    rw [← leftPi_fibrePi, hu, hl]
  obtain ⟨v, hv⟩ := HomotopySequence.exists_of_map₁_eq_one
    (p := p) (he := basepointEquation p q w) hk (0 : Fin (n + 3))
  obtain ⟨v', hv'⟩ := hp v
  have hd : HomotopySequence.δ' p (basepointEquation p q w) (n + 1) 0 v = 1 := by
    rw [← hv']
    exact HomotopySequence.δ'_map₂_apply (p := p) (he := basepointEquation p q w) v' 0
  have hf : fibrePiMap p q w (n + 1) u = 1 := hv.symm.trans hd
  have hu₁ : u = 1 := (fibrePiMap_bijective p q w (n + 1)).injective (by
    simpa only [fibrePiMap, mapπ_one] using hf)
  rw [← hu, hu₁]
  simp only [HomotopySequence.map₁, mapπ_one]

theorem positiveComparison_injective {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    [Fibration p] [IsFibrant B] [IsFibrant C] (w : (pullback p q) _⦋0⦌) (n : ℕ)
    (hp : Function.Surjective (basePi p q w (n + 2))) :
    Function.Injective (positiveComparison p q w n) := by
  have : Fibration (pullback.snd p q) := inferInstance
  have : IsFibrant E := isFibrant_of_fibration p
  have : IsFibrant (pullback p q) := isFibrant_of_fibration (pullback.snd p q)
  intro s t h
  have hl : leftPi p q w (n + 1) s = leftPi p q w (n + 1) t :=
    congrArg (fun z ↦ z.val.1) h
  have hr : rightPi p q w (n + 1) s = rightPi p q w (n + 1) t :=
    congrArg (fun z ↦ z.val.2) h
  have hkl : leftPi p q w (n + 1) (s * t⁻¹) = 1 := by
    simp only [leftPi, mapπ_mul, mapπ_inv]
    change leftPi p q w (n + 1) s * (leftPi p q w (n + 1) t)⁻¹ = 1
    rw [hl, mul_inv_cancel]
  have hkr : rightPi p q w (n + 1) (s * t⁻¹) = 1 := by
    simp only [rightPi, mapπ_mul, mapπ_inv]
    change rightPi p q w (n + 1) s * (rightPi p q w (n + 1) t)⁻¹ = 1
    rw [hr, mul_inv_cancel]
  exact mul_inv_eq_one.mp (joint_kernel_trivial p q w n hp (s * t⁻¹) hkl hkr)

theorem positiveComparison_bijective {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    [Fibration p] [IsFibrant B] [IsFibrant C] (w : (pullback p q) _⦋0⦌) (n : ℕ)
    (hp : Function.Surjective (basePi p q w (n + 2))) :
    Function.Bijective (positiveComparison p q w n) :=
  ⟨positiveComparison_injective p q w n hp, positiveComparison_surjective p q w n⟩

end
end DaggerNativePullbackPositivePiComparison
