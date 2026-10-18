import OriginalUnitaryCoreConstruction

/-!
# Original canonical unitary vertices and their exact functorial labels

Every original input vertex determines its original core vertex and the
canonical constant vertex in the original full unitary subcomplex. These
vertices exhaust that subcomplex in degree zero. The original dagger map
preserves those exact labels. Full-subcomplex membership in every degree is
expressed using the original input labels, rather than replacement vertices.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalDaggerCoreCandidate DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalEC2HomotopyFixedPointFunctor DaggerOriginalEC2CanonicalVertexSubcomplex
open DaggerOriginalUnitaryCoreConstruction

universe u

namespace DaggerOriginalUnitaryCoreCanonicalVertices

noncomputable section

/-- The original constant homotopy-fixed vertex belongs to the exact unitary full subcomplex. -/
def canonicalUnitaryVertex (X : DaggerSSet.{u}) (x : X.toSSet.obj (op ⦋0⦌)) :
    (unitaryCore X).obj (op ⦋0⦌) :=
  ⟨canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x), by
    intro v
    have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst v
    refine ⟨(coreVertexEquiv X).symm x, ?_⟩
    simp only [op_id, FunctorToTypes.map_id_apply]
    rfl⟩

/-- The actual original core map preserves the same original lifted vertex label. -/
theorem coreVertexEquiv_naturality {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x : X.toSSet.obj (op ⦋0⦌)) :
    (daggerCoreMap f).hom.app (op ⦋0⦌) ((coreVertexEquiv X).symm x) =
      (coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) x) := Subtype.ext rfl

/-- The unitary map sends the original canonical vertex to the canonical original image vertex. -/
theorem canonicalUnitaryVertex_naturality {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x : X.toSSet.obj (op ⦋0⦌)) :
    (unitaryCoreFunctor.map f).app (op ⦋0⦌) (canonicalUnitaryVertex X x) =
      canonicalUnitaryVertex Y (f.hom.app (op ⦋0⦌) x) := by
  apply Subtype.ext
  change (daggerHomotopyFixedPointFunctor.map (daggerCoreMap f)).app (op ⦋0⦌)
    (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x)) =
      canonicalZeroSimplex (daggerCoreCandidate Y)
        ((coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) x))
  rw [canonicalZeroSimplex_naturality, coreVertexEquiv_naturality]

/-- Every actual zero-simplex of the unitary core has an original canonical input label. -/
theorem canonicalUnitaryVertex_surjective (X : DaggerSSet.{u}) :
    Function.Surjective (canonicalUnitaryVertex X) := by
  intro s
  obtain ⟨y, hy⟩ := s.property (𝟙 ⦋0⦌)
  have hy' : canonicalZeroSimplex (daggerCoreCandidate X) y = s.val := by
    simpa only [op_id, FunctorToTypes.map_id_apply] using hy
  refine ⟨coreVertexEquiv X y, ?_⟩
  apply Subtype.ext
  change canonicalZeroSimplex (daggerCoreCandidate X)
    ((coreVertexEquiv X).symm (coreVertexEquiv X y)) = s.val
  rw [Equiv.symm_apply_apply]
  exact hy'

/-- Full unitary-subcomplex membership uses exactly the canonical original input vertices. -/
theorem unitaryCore_mem_iff (X : DaggerSSet.{u}) (q : SimplexCategoryᵒᵖ)
    (s : (unitaryCoreAmbientFunctor.obj X).obj q) :
    s ∈ (canonicalVertexSubcomplex (daggerCoreCandidate X)).obj q ↔
      ∀ v : ⦋0⦌ ⟶ q.unop, ∃ x : X.toSSet.obj (op ⦋0⦌),
        canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x) =
          (unitaryCoreAmbientFunctor.obj X).map v.op s := by
  change (∀ v : ⦋0⦌ ⟶ q.unop, (unitaryCoreAmbientFunctor.obj X).map v.op s ∈
    canonicalVertices (daggerCoreCandidate X)) ↔ _
  rw [unitaryCore_selected_vertices]
  rfl

end

end DaggerOriginalUnitaryCoreCanonicalVertices
