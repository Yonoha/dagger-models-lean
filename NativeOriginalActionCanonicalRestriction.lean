import NativeOriginalActionCanonicalConstants
import NativeRealEdgewiseCanonicalWeak

/-! Restrict the OLD EC2 mapping complexes to literal constants at selected ORIGINAL vertices. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerNativeOriginalC2RealizationMapping
open DaggerNativeOriginalActionCanonicalConstants DaggerOriginalFullVertexSubcomplex
open DaggerOriginalFullVertexPointedHomotopyComparison
open DaggerOriginalFullVertexWeakEquivalenceRestriction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalActionCanonicalRestriction
noncomputable section

/-- A strict original equivariant map preserves any original action-fixed vertex. -/
theorem image_fixed {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B) (x : A.V _⦋0⦌)
    (hx : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) x = x) (y : B.V _⦋0⦌)
    (hxy : f.hom.app (op ⦋0⦌) x = y) :
    ∀ g, (B.ρ g).asHom.app (op ⦋0⦌) y = y := by
  intro g
  subst y
  have h := congrFun (NatTrans.congr_app (f.comm g) (op ⦋0⦌)) x
  change f.hom.app (op ⦋0⦌) ((A.ρ g).asHom.app (op ⦋0⦌) x) =
    (B.ρ g).asHom.app (op ⦋0⦌) (f.hom.app (op ⦋0⦌) x) at h
  rw [hx] at h
  exact h.symm

variable {α β : Type u}
variable (A : Action SSet.{u} C2.{u}) (v : α → A.V _⦋0⦌)
variable (hv : ∀ i g, (A.ρ g).asHom.app (op ⦋0⦌) (v i) = v i)

/-- The selected set consists of the literal OLD equivariant EC2 constant vertices. -/
def vertices : Set ((mappingFunctor.obj A) _⦋0⦌) :=
  Set.range (fun i ↦ canonicalZero A (v i) (hv i))

def canonicalSubcomplex : (mappingFunctor.obj A).Subcomplex :=
  fullVertexSubcomplex _ (vertices A v hv)

instance canonical_kan : SSet.KanComplex (canonicalSubcomplex A v hv).toSSet := by
  change SSet.KanComplex (fullVertexSubcomplex (mappingFunctor.obj A) (vertices A v hv) : SSet)
  infer_instance

/-- Keep each ORIGINAL vertex as its actual constant zero-simplex in the full subcomplex. -/
def canonicalVertex (i : α) : (canonicalSubcomplex A v hv).toSSet _⦋0⦌ :=
  ⟨canonicalZero A (v i) (hv i), by
    intro t
    have ht : t = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst t
    simpa using (show canonicalZero A (v i) (hv i) ∈ vertices A v hv from ⟨i, rfl⟩)⟩

variable {A v hv}
variable {B : Action SSet.{u} C2.{u}} {w : β → B.V _⦋0⦌}
variable {hw : ∀ i g, (B.ρ g).asHom.app (op ⦋0⦌) (w i) = w i}
variable (f : A ⟶ B) (j : α → β) (hj : ∀ i, f.hom.app (op ⦋0⦌) (v i) = w (j i))

include f j hj

theorem preservesVertices : ∀ z, z ∈ vertices A v hv →
    (mappingFunctor.map f).app (op ⦋0⦌) z ∈ vertices B w hw := by
  rintro _ ⟨i, rfl⟩
  exact ⟨j i, (canonicalZero_naturality f (v i) (hv i) (w (j i)) (hw (j i)) (hj i)).symm⟩

/-- Restrict the SAME original ambient mapping map by the OLD full-vertex construction. -/
def map : (canonicalSubcomplex A v hv).toSSet ⟶ (canonicalSubcomplex B w hw).toSSet :=
  restrictedMap _ _ (mappingFunctor.map f) (preservesVertices (hv := hv) (hw := hw) f j hj)

theorem map_vertex (i : α) :
    (map (hv := hv) (hw := hw) f j hj).app (op ⦋0⦌) (canonicalVertex A v hv i) =
      canonicalVertex B w hw (j i) := by
  apply Subtype.ext
  exact canonicalZero_naturality f (v i) (hv i) (w (j i)) (hw (j i)) (hj i)

theorem map_zero_surjective (hjs : Function.Surjective j) :
    Function.Surjective ((map (hv := hv) (hw := hw) f j hj).app (op ⦋0⦌)) := by
  intro y
  obtain ⟨k, hk⟩ := fullVertex_vertex_mem (vertices B w hw) y
  obtain ⟨i, rfl⟩ := hjs k
  refine ⟨canonicalVertex A v hv i, ?_⟩
  apply Subtype.ext
  exact (canonicalZero_naturality f (v i) (hv i) (w (j i)) (hw (j i)) (hj i)).trans hk

/-- The exact restriction is weak when the original ambient map is weak and labels cover. -/
theorem map_weak [WeakEquivalence f.hom] (hjs : Function.Surjective j) :
    WeakEquivalence (map (hv := hv) (hw := hw) f j hj) := by
  have : WeakEquivalence (mappingFunctor.map f) := mapping_map_weak f
  exact restrictedMap_weakEquivalence _ _ _ _
    (DaggerNativeKanRigHomWeakRecognition.mapπ₀_surjective_of_vertices _
      (map_zero_surjective (hv := hv) (hw := hw) f j hj hjs))

end
end DaggerNativeOriginalActionCanonicalRestriction
