import OriginalCompactGeneration
import TopCatModelCategory.Convenient.CartesianClosed
import TopCatModelCategory.Convenient.Product

/-!
# The original compact-open exponential law with compact-generated source

The source need not be locally compact. For a compact-generated, locally compact
parameter space, a continuous family of ordinary compact-open maps has a continuous
uncurried map. The proof uses the existing generated mapping space and its native
curry equivalence. This is a point-set bridge for the original EC₂ mapping problem;
it does not assert weak-equivalence preservation.
-/

set_option autoImplicit false

open CategoryTheory Topology DaggerOriginalCompactGeneration

universe u

namespace DaggerOriginalCompactOpenExponentialLaw

noncomputable section

variable {E K Y : Type u} [TopologicalSpace E] [TopologicalSpace K]
  [TopologicalSpace Y]

/-- An ordinary continuous map gives the same map in the native generated mapping space. -/
def ordinaryToGenerated (f : C(E, Y)) : ContinuousMapGeneratedBy compactHausFamily.{u} E Y :=
  ⟨f, f.continuous.continuousGeneratedBy⟩

/-- The passage from the literal compact-open topology to the native mapping topology is
continuous. -/
theorem ordinaryToGenerated_continuous :
    Continuous (ordinaryToGenerated (E := E) (Y := Y)) := by
  rw [ContinuousMapGeneratedBy.continuous_iff]
  intro P p
  exact ContinuousMap.continuous_precomp p

/-- An ordinary product with a generated locally compact parameter is still generated. -/
theorem generated_product [IsGeneratedBy compactHausFamily.{u} E]
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K] :
    IsGeneratedBy compactHausFamily.{u} (E × K) := by
  let : Inhabited CompHaus.{u} := ⟨CompHaus.of PUnit.{u + 1}⟩
  have : Nonempty (compactHausFamily.{u} default) := ⟨PUnit.unit⟩
  infer_instance

/-- Compact-open families uncurried over generated locally compact parameters are continuous. -/
theorem continuous_uncurry [IsGeneratedBy compactHausFamily.{u} E]
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    (f : C(K, C(E, Y))) : Continuous (fun p : E × K ↦ f p.2 p.1) := by
  have : IsGeneratedBy compactHausFamily.{u} (E × K) := generated_product
  let g : ContinuousMapGeneratedBy compactHausFamily.{u} K
      (ContinuousMapGeneratedBy compactHausFamily.{u} E Y) :=
    ⟨fun k ↦ ordinaryToGenerated (f k),
      (ordinaryToGenerated_continuous.comp f.continuous).continuousGeneratedBy⟩
  let h : ContinuousMapGeneratedBy compactHausFamily.{u} (E × K) Y :=
    ContinuousMapGeneratedBy.curryEquiv.symm g
  exact (IsGeneratedBy.continuous_iff compactHausFamily _).2 h.prop

/-- The exponential equivalence uses the original compact-open continuous maps on both sides. -/
def compactParameterCurryEquiv [IsGeneratedBy compactHausFamily.{u} E]
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K] :
    C(E × K, Y) ≃ C(K, C(E, Y)) where
  toFun f := ContinuousMap.curry (f.comp ⟨_, (Homeomorph.prodComm K E).continuous⟩)
  invFun f := ⟨fun p ↦ f p.2 p.1, continuous_uncurry f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Currying keeps the original pointwise formula. -/
theorem compactParameterCurryEquiv_apply [IsGeneratedBy compactHausFamily.{u} E]
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    (f : C(E × K, Y)) (k : K) (e : E) :
    compactParameterCurryEquiv f k e = f (e, k) := rfl

/-- Uncurrying keeps the original pointwise formula. -/
theorem compactParameterCurryEquiv_symm_apply [IsGeneratedBy compactHausFamily.{u} E]
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    (f : C(K, C(E, Y))) (e : E) (k : K) :
    compactParameterCurryEquiv.symm f (e, k) = f k e := rfl

end

end DaggerOriginalCompactOpenExponentialLaw
