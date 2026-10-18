import NativeHornPointWeakEquivalences
import TopCatModelCategory.SSet.PiZero

/-! A native fibration surjective on components is surjective in every degree, without Kan bases. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial
open HomotopicalAlgebra DaggerNativeHornPointWeakEquivalences
open DaggerNativeStandardSimplexContraction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFibrationSurjectiveComponents
noncomputable section

theorem yoneda_coface {Z : SSet.{u}} {n : ℕ} (i : Fin (n + 2))
    (a : (Δ[n + 1] : SSet.{u}) ⟶ Z) :
    SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ a) = Z.δ i (SSet.yonedaEquiv a) :=
  congrFun (a.naturality (SimplexCategory.δ i).op)
    (SSet.stdSimplex.objEquiv.symm (𝟙 _))

theorem simplex_point_trivialCofibration (n : ℕ)
    (a : (Δ[0] : SSet.{u}) ⟶ Δ[n]) : trivialCofibrations SSet.{u} a := by
  have : Mono a := ⟨fun f g _ ↦ SSet.stdSimplex.isTerminalObj₀.hom_ext f g⟩
  have : Cofibration a := (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  have : WeakEquivalence (toUnit (Δ[n] : SSet.{u})) :=
    contractible_terminal_weak (simplexContractible n)
  have : WeakEquivalence (toUnit (Δ[0] : SSet.{u})) :=
    contractible_terminal_weak (simplexContractible 0)
  have h : a ≫ toUnit (Δ[n] : SSet.{u}) = toUnit (Δ[0] : SSet.{u}) :=
    isTerminalTensorUnit.hom_ext _ _
  exact (mem_trivialCofibrations_iff _).mpr
    ⟨inferInstance, weakEquivalence_of_postcomp_of_fac h⟩

theorem edge_lift_at_vertex {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (e : B _⦋1⦌) (i : Fin 2) (x : E _⦋0⦌) (hx : p.app _ x = B.δ i e) :
    ∃ l : E _⦋1⦌, p.app _ l = e ∧ E.δ i l = x := by
  have ht := simplex_point_trivialCofibration 1 (SSet.stdSimplex.δ i)
  have : Cofibration (SSet.stdSimplex.δ i : (Δ[0] : SSet.{u}) ⟶ Δ[1]) :=
    (mem_trivialCofibrations_iff _).mp ht |>.1
  have : WeakEquivalence (SSet.stdSimplex.δ i : (Δ[0] : SSet.{u}) ⟶ Δ[1]) :=
    (mem_trivialCofibrations_iff _).mp ht |>.2
  let sq : CommSq (SSet.yonedaEquiv.symm x) (SSet.stdSimplex.δ i) p
      (SSet.yonedaEquiv.symm e) := ⟨by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      yoneda_coface, Equiv.apply_symm_apply]
    exact hx⟩
  refine ⟨SSet.yonedaEquiv sq.lift, ?_, ?_⟩
  · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv sq.fac_right
  · simpa only [yoneda_coface, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv sq.fac_left

theorem vertex_image_edge_iff {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (e : B _⦋1⦌) :
    (∃ x : E _⦋0⦌, p.app _ x = B.δ 1 e) ↔
      ∃ y : E _⦋0⦌, p.app _ y = B.δ 0 e := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨l, hl, _⟩ := edge_lift_at_vertex p e 1 x hx
    refine ⟨E.δ 0 l, ?_⟩
    rw [SSet.δ_naturality_apply, hl]
  · rintro ⟨y, hy⟩
    obtain ⟨l, hl, _⟩ := edge_lift_at_vertex p e 0 y hy
    refine ⟨E.δ 1 l, ?_⟩
    rw [SSet.δ_naturality_apply, hl]

theorem vertices_surjective_of_components {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (hp : Function.Surjective (SSet.mapπ₀ p)) : Function.Surjective (p.app (op ⦋0⦌)) := by
  intro b
  obtain ⟨c, hc⟩ := hp (SSet.π₀.mk b)
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
  have he := (SSet.π₀.mk_eq_mk_iff (p.app _ x) b).mp hc
  have hinv : ∀ a b : B _⦋0⦌, Relation.EqvGen SSet.π₀Rel a b →
      ((∃ e : E _⦋0⦌, p.app _ e = a) ↔ ∃ e : E _⦋0⦌, p.app _ e = b) := by
    intro a b h
    induction h with
    | rel a b hab =>
      obtain ⟨e, rfl, rfl⟩ := hab
      exact vertex_image_edge_iff p e
    | refl a => rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  exact (hinv _ _ he).mp ⟨x, rfl⟩

theorem degree_surjective_of_vertices {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (hp : Function.Surjective (p.app (op ⦋0⦌))) (n : ℕ) :
    Function.Surjective (p.app (op ⦋n⦌)) := by
  intro b
  let v : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.const (firstVertex n)
  have ht := simplex_point_trivialCofibration n v
  have : Cofibration v := (mem_trivialCofibrations_iff _).mp ht |>.1
  have : WeakEquivalence v := (mem_trivialCofibrations_iff _).mp ht |>.2
  obtain ⟨x, hx⟩ := hp (SSet.yonedaEquiv (v ≫ SSet.yonedaEquiv.symm b))
  let sq : CommSq (SSet.yonedaEquiv.symm x) v p (SSet.yonedaEquiv.symm b) := ⟨by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hx⟩
  refine ⟨SSet.yonedaEquiv sq.lift, ?_⟩
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
    congrArg SSet.yonedaEquiv sq.fac_right

theorem degree_surjective_of_components {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (hp : Function.Surjective (SSet.mapπ₀ p)) (n : ℕ) :
    Function.Surjective (p.app (op ⦋n⦌)) :=
  degree_surjective_of_vertices p (vertices_surjective_of_components p hp) n

end
end DaggerNativeFibrationSurjectiveComponents
