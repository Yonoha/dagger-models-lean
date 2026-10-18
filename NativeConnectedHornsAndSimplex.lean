import NativeFibrationWeakFromVertexFibres
import OriginalSimplicialPiZeroWeakEquivalence
import ActualConstantSimplicialCategory

/-! Native components of standard simplices and positive horns are subsingletons. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra
open DaggerNativeStandardSimplexContraction DaggerNativeFibrationWeakFromVertexFibres
open DaggerOriginalSimplicialPiZeroWeakEquivalence
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeConnectedHornsAndSimplex
noncomputable section

theorem zeroSimplex_components_subsingleton : Subsingleton ((Δ[0] : SSet.{u}).π₀) := by
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
  congr 1
  apply SSet.stdSimplex.obj₀Equiv.injective
  apply Fin.ext
  omega

instance simplex_components_subsingleton (n : ℕ) :
    Subsingleton ((Δ[n] : SSet.{u}).π₀) := by
  have : WeakEquivalence (SSet.const (firstVertex n) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) :=
    first_vertex_weak n
  have hb := (bijective_mapPiZero
    (SSet.const (firstVertex n) : (Δ[0] : SSet.{u}) ⟶ Δ[n])).2
  letI := zeroSimplex_components_subsingleton.{u}
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := hb a
  obtain ⟨b, rfl⟩ := hb b
  exact congrArg _ (Subsingleton.elim a b)

instance horn_components_subsingleton (n : ℕ) (k : Fin (n + 2)) :
    Subsingleton (((Λ[n + 1, k] : (Δ[n + 1] : SSet.{u}).Subcomplex) : SSet.{u}).π₀) := by
  have ht : trivialCofibrations SSet
      (Λ[n + 1, k] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι :=
    (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).mp
      (SSet.anodyneExtensions.horn_ι_mem n k)
  have : WeakEquivalence (Λ[n + 1, k] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι :=
    (mem_trivialCofibrations_iff _).mp ht |>.2
  have hb := (bijective_mapPiZero
    (Λ[n + 1, k] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι).1
  exact ⟨fun a b ↦ hb (Subsingleton.elim _ _)⟩

end
end DaggerNativeConnectedHornsAndSimplex
