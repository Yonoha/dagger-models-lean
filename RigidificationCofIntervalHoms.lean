import RigidificationCofConvexHoms
import RigidificationCofCanonicalFaces
import RigidificationCofPathUnits

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ}

def subsetEmbedding (s : Finset (Fin (n + 1))) : ULift.{u} s ↪o vertices.{u} n where
  toFun x := ⟨x.down.val⟩
  inj' _ _ h := ULift.ext _ _ (Subtype.ext (congrArg ULift.down h))
  map_rel_iff' := Iff.rfl

def intervalLeft (i j : Fin (n + 1)) (hij : i ≤ j) : ULift.{u} (Finset.Icc i j) :=
  ⟨⟨i, Finset.mem_Icc.mpr ⟨le_rfl, hij⟩⟩⟩

def intervalRight (i j : Fin (n + 1)) (hij : i ≤ j) : ULift.{u} (Finset.Icc i j) :=
  ⟨⟨j, Finset.mem_Icc.mpr ⟨hij, le_rfl⟩⟩⟩

theorem interval_range (i j : Fin (n + 1)) (hij : i ≤ j) (x : vertices.{u} n)
    (hi : subsetEmbedding (Finset.Icc i j) (intervalLeft i j hij) ≤ x)
    (hj : x ≤ subsetEmbedding (Finset.Icc i j) (intervalRight i j hij)) :
    x ∈ Set.range (subsetEmbedding (Finset.Icc i j)) :=
  ⟨⟨⟨x.down, Finset.mem_Icc.mpr ⟨hi, hj⟩⟩⟩, rfl⟩

def intervalNonempty (i j : Fin (n + 1)) (hij : i ≤ j) : (Finset.Icc i j).Nonempty :=
  ⟨i, Finset.mem_Icc.mpr ⟨le_rfl, hij⟩⟩

theorem intervalProper (i j : Fin (n + 1)) (hp : ¬ (i = 0 ∧ j = Fin.last n)) :
    Finset.Icc i j ≠ Finset.univ := by
  intro h
  have hi : 0 ∈ Finset.Icc i j := by rw [h]; exact Finset.mem_univ _
  have hj : Fin.last n ∈ Finset.Icc i j := by rw [h]; exact Finset.mem_univ _
  apply hp
  constructor
  · exact le_antisymm (Finset.mem_Icc.mp hi).1 (Fin.zero_le _)
  · exact le_antisymm (Fin.le_last _) (Finset.mem_Icc.mp hj).2

def intervalHomIso (i j : Fin (n + 1)) (hij : i ≤ j) :
    hom (intervalLeft.{u} i j hij) (intervalRight i j hij) ≅
      hom (ULift.up i) (ULift.up j) :=
  convexHomIso (subsetEmbedding (Finset.Icc i j)) (intervalLeft i j hij)
    (intervalRight i j hij) (interval_range i j hij)

variable {A : SC.{u}}

/-- Every proper forward interval retains its ENTIRE original Hom, not only an edge. -/
def forwardProperMap (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (i j : Fin (n + 2)) (hij : i ≤ j) (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    hom (ULift.up i) (ULift.up j) ⟶ vertex a i ⟶[SSet.{u}] vertex a j :=
  (intervalHomIso i j hij).inv ≫
    (canonicalFaceFunctor a (Finset.Icc i j) (intervalNonempty i j hij)
      (intervalProper i j hp)).map (.mk (intervalLeft i j hij))
        (.mk (intervalRight i j hij))

/-- Backward intervals use the actual empty Path Hom; equal endpoints remain included. -/
def properMap (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (i j : Fin (n + 2)) (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    hom (ULift.up i) (ULift.up j) ⟶ vertex a i ⟶[SSet.{u}] vertex a j :=
  if hij : i ≤ j then forwardProperMap a i j hij hp
  else emptyHomMap (show ULift.up j < ULift.up i from lt_of_not_ge hij) _

end

end DaggerOrdinaryRigidificationCof.BoundaryData
