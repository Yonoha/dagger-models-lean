import OriginalCompatibleFaceData
import OriginalInnerHornFaces

set_option autoImplicit false

open CategoryTheory Simplicial Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornData

open BoundaryData PathFacets InnerHornFaces
open DaggerModels.OrdinaryRigidification.NerveVertices

variable {n : ℕ} (k : interior n)

/-- An included ordinal simplex omits a vertex different from the missing horn index. -/
theorem contains_iff_omits {m : SimplexCategory} (φ : m ⟶ ⦋n + 1⦌) :
    SubcomplexNerveData.Contains (SSet.horn.{u} (n + 1) k.val) φ ↔
      ∃ j, j ≠ k.val ∧ ∀ i, φ.toOrderHom i ≠ j := by
  classical
  change Set.range φ.toOrderHom ∪ {k.val} ≠ Set.univ ↔ _
  constructor
  · intro h
    by_contra ha
    apply h
    apply Set.eq_univ_iff_forall.mpr
    intro j
    by_cases hjk : j = k.val
    · exact Or.inr hjk
    · left
      by_contra hj
      exact ha ⟨j, hjk, fun i hi ↦ hj ⟨i, hi⟩⟩
  · rintro ⟨j, hjk, hj⟩ he
    have hmem : j ∈ Set.range φ.toOrderHom ∪ {k.val} := by
      rw [he]
      exact Set.mem_univ _
    rcases hmem with ⟨i, hi⟩ | hi
    · exact hj i hi
    · exact hjk hi

/-- Every actual vertex map lies in this inner horn, with its original ordinal map. -/
theorem vertex_contains (i : Fin (n + 2)) :
    SubcomplexNerveData.Contains (SSet.horn.{u} (n + 1) k.val) (vertexMap i) := by
  obtain ⟨j, hjk, hj⟩ := singleton_admissible k i
  apply (contains_iff_omits k (vertexMap i)).mpr
  refine ⟨j, hjk, fun _ hi ↦ ?_⟩
  change i = j at hi
  exact hj (Finset.mem_singleton.mpr hi.symm)

variable {A : SC.{u}}

/-- Compatible face data extracted from the given original inner-horn map itself. -/
noncomputable def data (a : (SSet.horn.{u} (n + 1) k.val).toSSet ⟶ N.obj A) :
    CompatibleFaceData (n + 1) A (Admissible k) :=
  CompatibleFaceData.ofSubcomplex (SSet.horn (n + 1) k.val) a
    (vertex_contains k) (fun s hs hp ↦ (faceOrdinal_mem_iff k s hs).mpr hp)

/-- The common object is evaluated at the very same supplied horn vertex. -/
theorem data_obj (a : (SSet.horn.{u} (n + 1) k.val).toSSet ⟶ N.obj A)
    (i : Fin (n + 2)) :
    (data k a).obj i =
      (a.app (op ⦋0⦌)
        ⟨SSet.stdSimplex.objEquiv.symm (vertexMap i), vertex_contains k i⟩).down.obj
          zeroObject := rfl

/-- Each whole face functor is the original evaluation under the supplied horn map. -/
theorem data_F (a : (SSet.horn.{u} (n + 1) k.val).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : Admissible k s) :
    (data k a).F s hs hp =
      SubcomplexNerveData.faceFunctor (SSet.horn (n + 1) k.val) a s hs
        ((faceOrdinal_mem_iff k s hs).mpr hp) := rfl

/-- Canonical object names retain that exact whole original face functor. -/
theorem data_canonicalF (a : (SSet.horn.{u} (n + 1) k.val).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : Admissible k s) :
    (data k a).canonicalF s hs hp =
      SubcomplexNerveData.faceFunctor (SSet.horn (n + 1) k.val) a s hs
        ((faceOrdinal_mem_iff k s hs).mpr hp) :=
  (data k a).canonicalF_eq s hs hp

end DaggerOrdinaryRigidificationCof.InnerHornData
