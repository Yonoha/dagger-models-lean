import OriginalLeftMappingFibrationSequence

/-!
# Higher homotopy recognition through the actual original left mapping spaces

The native natural boundary bijections transport an original mapping-space
weak equivalence to all positive homotopy degrees of the original Kan map.
Together with bijectivity on actual components, this proves weak equivalence
of that same original simplicial map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalLeftMappingFunctoriality DaggerOriginalLeftMappingFibrationSequence
open DaggerOriginalQuasicategoryLeftMappingSpace
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreContainsKanSubcomplexes

universe u

namespace DaggerOriginalKanMappingHomotopyRecognition

noncomputable section

/-- An actual original self-mapping-space weak equivalence detects every positive degree. -/
theorem mapπ_positive_bijective_of_leftMappingW {X Y : SSet.{u}}
    [X.KanComplex] [Y.KanComplex] (f : X ⟶ Y) (x : X.obj (op ⦋0⦌))
    (hf : SSet.KanComplex.W (leftMappingMap f x x)) (n : ℕ) :
    Function.Bijective
      (SSet.KanComplex.mapπ f (n + 1) x (f.app (op ⦋0⦌) x) rfl) := by
  let x' := f.app (op ⦋0⦌) x
  have hsource := leftMappingBoundary_bijective X x n
  have htarget := leftMappingBoundary_bijective Y x' n
  have hmapping := hf.bijective n (leftMappingBasePoint X x)
    (leftMappingBasePoint Y x') (leftMappingMap_basePoint f x)
  have hcomp := hmapping.comp hsource
  have hnat : leftMappingBoundary Y x' n ∘
        SSet.KanComplex.mapπ f (n + 1) x x' rfl =
      SSet.KanComplex.mapπ (leftMappingMap f x x) n (leftMappingBasePoint X x)
        (leftMappingBasePoint Y x') (leftMappingMap_basePoint f x) ∘
        leftMappingBoundary X x n := by
    funext p
    exact leftMappingBoundary_naturality f x n p
  rw [← hnat] at hcomp
  constructor
  · intro p q hpq
    apply hcomp.1
    exact congrArg (leftMappingBoundary Y x' n) hpq
  · intro q
    obtain ⟨p, hp⟩ := hcomp.2 (leftMappingBoundary Y x' n q)
    exact ⟨p, htarget.1 hp⟩

/-- The same positive-degree conclusion from a native mapping-space weak equivalence. -/
theorem mapπ_positive_bijective_of_leftMappingWeakEquivalence {X Y : SSet.{u}}
    [X.KanComplex] [Y.KanComplex] (f : X ⟶ Y) (x : X.obj (op ⦋0⦌))
    (hf : WeakEquivalence (leftMappingMap f x x)) (n : ℕ) :
    Function.Bijective
      (SSet.KanComplex.mapπ f (n + 1) x (f.app (op ⦋0⦌) x) rfl) := by
  haveI := leftMappingSpace_kan (innerHornFillers_of_kan X) x x
  haveI := leftMappingSpace_kan (innerHornFillers_of_kan Y)
    (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) x)
  exact mapπ_positive_bijective_of_leftMappingW f x
    ((SSet.weakEquivalence_iff_kanComplexW _).1 hf) n

/-- Actual component bijectivity and actual self-mapping weak equivalences recognize the
 original Kan map itself as a native weak equivalence. -/
theorem weakEquivalence_of_components_and_leftMappingWeakEquivalences {X Y : SSet.{u}}
    [X.KanComplex] [Y.KanComplex] (f : X ⟶ Y)
    (hcomponents : Function.Bijective (SSet.mapπ₀ f))
    (hmap : ∀ x : X.obj (op ⦋0⦌), WeakEquivalence (leftMappingMap f x x)) :
    WeakEquivalence f := by
  apply (SSet.weakEquivalence_iff_kanComplexW _).2
  apply (SSet.KanComplex.W_iff _).2
  refine ⟨hcomponents, ?_⟩
  rintro n x _ rfl
  exact mapπ_positive_bijective_of_leftMappingWeakEquivalence f x (hmap x) n

end

end DaggerOriginalKanMappingHomotopyRecognition
