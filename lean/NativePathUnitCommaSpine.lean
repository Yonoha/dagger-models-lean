import NativePathUnitCommaFullyFaithful
import NativeFreePathGeneratorComplex
import NativeGroupoidCompletionNerveBaseCases

/-! The actual lifted graph's generator spine maps weakly to the entire actual unit-comma nerve. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeFreePathCompletionQuiverBridge DaggerNativePathUnitLiftedQuiver
open DaggerNativePathUnitCommaFullyFaithful DaggerNativeFreePathGeneratorComplex
open DaggerNativeGroupoidCompletionNerveBaseCases
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePathUnitCommaSpine
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V] (d : Quiver.FreeGroupoid V)

def commaEquivalence : Paths (Vertex V d) ≌ StructuredArrow d (pathUnit V) :=
  (commaFunctor V d).asEquivalence

theorem commaFunctor_nerve_weak : WeakEquivalence (nerveMap (commaFunctor V d)) :=
  nerveMap_weak_of_equivalence _

def spineToComma : (generatorComplex (Vertex V d)).toSSet ⟶
    nerve (StructuredArrow d (pathUnit V)) :=
  (generatorComplex (Vertex V d)).ι ≫ nerveMap (commaFunctor V d)

theorem spineToComma_weak : WeakEquivalence (spineToComma V d) := by
  have := generatorComplex_weak (V := Vertex V d)
  have := commaFunctor_nerve_weak V d
  unfold spineToComma
  infer_instance

end
end DaggerNativePathUnitCommaSpine
