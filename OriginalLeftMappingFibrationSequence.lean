import OriginalKanVertexCosliceFibration
import OriginalVertexCosliceContraction
import OriginalLeftMappingFunctoriality
import TopCatModelCategory.SSet.FibrationSequence

/-!
# Native fibration sequence for the original left mapping space

The fiber is exactly the original strict left mapping space from x to x.
The total space is the original vertex coslice and its projection is the
original suffix projection. Its contraction makes the native boundary map
bijective in every degree. All comparisons retain the original simplicial
map and its original identity-edge basepoint.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open SSet.modelCategoryQuillen
open DaggerOriginalSimplexCoslice DaggerOriginalQuasicategoryLeftMappingSpace
open DaggerOriginalLeftMappingVertices DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalKanVertexCosliceFibration DaggerOriginalVertexCosliceContraction

universe u

namespace DaggerOriginalLeftMappingFibrationSequence

noncomputable section

/-- The actual identity-edge vertex of the original left mapping space. -/
def leftMappingBasePoint (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    (leftMappingSpace X x x).obj (op ⦋0⦌) := edgeVertex X x x (SSet.Edge.id x)

/-- The actual original mapping-space map retains the same identity-edge basepoint. -/
theorem leftMappingMap_basePoint {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X.obj (op ⦋0⦌)) :
    (leftMappingMap f x x).app (op ⦋0⦌) (leftMappingBasePoint X x) =
      leftMappingBasePoint Y (f.app (op ⦋0⦌) x) := by
  apply Subtype.ext
  apply Subtype.ext
  change f.app (op ⦋1⦌) (X.map (SimplexCategory.σ (0 : Fin 1)).op x) =
    Y.map (SimplexCategory.σ (0 : Fin 1)).op (f.app (op ⦋0⦌) x)
  exact congrFun (f.naturality (SimplexCategory.σ (0 : Fin 1)).op) x

/-- The native fibration sequence with the same original fiber, coslice, and projection. -/
def leftMappingSequence (X : SSet.{u}) [X.KanComplex] (x : X.obj (op ⦋0⦌)) :
    SSet.FibrationSequence.{u} where
  F := leftMappingSpace X x x
  E := simplexCoslice ⦋0⦌ X x
  B := X
  i := (leftMappingSubcomplex X x x).ι
  p := cosliceProjection ⦋0⦌ X x
  hp := vertex_coslice_projection_fibration X x
  f := leftMappingBasePoint X x
  e := (leftMappingBasePoint X x).val
  b := x
  hf := rfl
  he := by
    change X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌).op (SSet.Edge.id x).edge = x
    rw [vertex_join_inr]
    exact (SSet.Edge.id x).tgt_eq
  isPullback := leftMappingSpace_isPullback X x x

/-- The base of the exact original sequence has the given native Kan structure. -/
instance leftMappingSequence_base_fibrant (X : SSet.{u}) [X.KanComplex]
    (x : X.obj (op ⦋0⦌)) : IsFibrant (leftMappingSequence X x).B := by
  change X.KanComplex
  infer_instance

/-- The total space of this exact original fibration sequence is contractible. -/
theorem leftMappingSequence_total_isContractible (X : SSet.{u}) [X.KanComplex]
    (x : X.obj (op ⦋0⦌)) : SSet.IsContractible (leftMappingSequence X x).E :=
  vertex_coslice_isContractible X x

/-- The native boundary map shifts homotopy of X to its actual left mapping space. -/
def leftMappingBoundary (X : SSet.{u}) [X.KanComplex] (x : X.obj (op ⦋0⦌)) (n : ℕ) :
    SSet.KanComplex.π (n + 1) X x →
      SSet.KanComplex.π n (leftMappingSpace X x x) (leftMappingBasePoint X x) :=
  (leftMappingSequence X x).δ n

/-- Every original boundary map is bijective, including the degree-zero fiber comparison. -/
theorem leftMappingBoundary_bijective (X : SSet.{u}) [X.KanComplex]
    (x : X.obj (op ⦋0⦌)) (n : ℕ) : Function.Bijective (leftMappingBoundary X x n) := by
  haveI := leftMappingSequence_total_isContractible X x
  exact (leftMappingSequence X x).bijective_δ n

/-- The same original simplicial map induces the actual native morphism of sequences. -/
def leftMappingSequenceMap {X Y : SSet.{u}} [X.KanComplex] [Y.KanComplex]
    (f : X ⟶ Y) (x : X.obj (op ⦋0⦌)) :
    leftMappingSequence X x ⟶ leftMappingSequence Y (f.app (op ⦋0⦌) x) where
  mor₁ := leftMappingMap f x x
  mor₂ := cosliceMap f ⦋0⦌ x
  mor₃ := f
  comm_i := (leftMappingMap_ι f x x).symm
  comm_p := (cosliceMap_projection f ⦋0⦌ x).symm
  mor₁_app_f := leftMappingMap_basePoint f x

/-- The native boundary square commutes for the exact original pointed maps. -/
theorem leftMappingBoundary_naturality {X Y : SSet.{u}} [X.KanComplex] [Y.KanComplex]
    (f : X ⟶ Y) (x : X.obj (op ⦋0⦌)) (n : ℕ) (p : SSet.KanComplex.π (n + 1) X x) :
    leftMappingBoundary Y (f.app (op ⦋0⦌) x) n
        (SSet.KanComplex.mapπ f (n + 1) x (f.app (op ⦋0⦌) x) rfl p) =
      SSet.KanComplex.mapπ (leftMappingMap f x x) n (leftMappingBasePoint X x)
        (leftMappingBasePoint Y (f.app (op ⦋0⦌) x)) (leftMappingMap_basePoint f x)
        (leftMappingBoundary X x n p) :=
  SSet.FibrationSequence.δ_naturality_apply (leftMappingSequenceMap f x) p

end

end DaggerOriginalLeftMappingFibrationSequence
