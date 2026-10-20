import OriginalEC2CompactParameterLifting
import OriginalBorelFreeGenerators

/-!
# Original EC₂ mapping lifting against the actual TopCat generators

Realizations of the original simplex subcomplexes are locally compact, by the
native closed-embedding and finite-realization theorems. Thus the original
boundary and horn right-lifting classes reduce to literal EC₂ product lifting.
No lifting property of those product arrows is assumed to hold automatically.
-/

set_option autoImplicit false

open CategoryTheory Topology DaggerModels Simplicial
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompactGeneration
open DaggerOriginalEC2HomotopyFixedPointFunctor DaggerOriginalEC2CompactParameterHomEquiv
open DaggerOriginalEC2CompactParameterLifting

universe u

namespace DaggerOriginalEC2GeneratorLifting

noncomputable section

/-- Every original realized simplex subcomplex is Hausdorff by the native closed embedding. -/
instance simplexSubcomplex_t2 (n : ℕ) (A : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}).Subcomplex) :
    T2Space (SSet.toTop.obj A.toSSet) :=
  (SSet.closedEmbeddings_toObj_map_of_mono A.ι).isEmbedding.t2Space

/-- Every original realized simplex subcomplex is locally compact by native finite realization. -/
instance simplexSubcomplex_locallyCompact (n : ℕ)
    (A : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}).Subcomplex) :
    LocallyCompactSpace (SSet.toTop.obj A.toSSet) := by
  infer_instance

/-- The actual original boundary lifting is the corresponding equivariant EC₂ product lifting. -/
theorem originalPostcompose_boundary_rlp_iff {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) :
    TopCat.modelCategory.I.rlp (postcompose p) ↔
      ∀ n, HasLiftingProperty (originalEC2TensorMap (SSet.toTop.map (SSet.boundary n).ι))
        p.hom := by
  constructor
  · intro hp n
    exact (originalEC2_lifting_iff _ p).2 (hp _ ⟨n⟩)
  · rintro hp _ _ _ ⟨n⟩
    exact (originalEC2_lifting_iff _ p).1 (hp n)

/-- Actual positive-dimensional horn lifting has the same original EC₂ product formulation. -/
theorem originalPostcompose_horn_rlp_iff {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) :
    TopCat.modelCategory.J.rlp (postcompose p) ↔
      ∀ (n : ℕ) (i : Fin (n + 2)),
        HasLiftingProperty (originalEC2TensorMap (SSet.toTop.map (SSet.horn (n + 1) i).ι))
          p.hom := by
  constructor
  · intro hp n i
    have hi : TopCat.modelCategory.J (SSet.toTop.map (SSet.horn (n + 1) i).ι) := by
      simp only [TopCat.modelCategory.J, MorphismProperty.iSup_iff]
      exact ⟨n, ⟨i⟩⟩
    exact (originalEC2_lifting_iff _ p).2 (hp _ hi)
  · intro hp _ _ i hi
    simp only [TopCat.modelCategory.J, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨i⟩⟩ := hi
    exact (originalEC2_lifting_iff _ p).1 (hp n i)

end

end DaggerOriginalEC2GeneratorLifting
