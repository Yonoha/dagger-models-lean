import OriginalDaggerCoreKan
import OriginalEC2CanonicalVertexKan

/-!
# The original unitary core construction applied to the verified greatest dagger Kan core

First take the literal original greatest Kan core with its original restricted
dagger. Then apply the existing singular equivariant mapping construction and
retain the full subcomplex spanned by the original canonical constant vertices.
Every original vertex is identified with its original core vertex. This gives
the exact functorial point-set unitary core and its native Kan property. The
derived fixed-point comparison and intrinsic weak-equivalence recognition are
separate remaining requirements.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalInnerHornFillers
open DaggerOriginalDaggerCoreCandidate DaggerOriginalDaggerCoreCandidateFunctor
open DaggerOriginalDaggerCoreKan DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalEC2HomotopyFixedPointFunctor DaggerOriginalEC2CanonicalVertexSubcomplex
open DaggerOriginalEC2CanonicalVertexKan

universe u

namespace DaggerOriginalUnitaryCoreConstruction

noncomputable section

/-- The original greatest dagger core retains every original vertex, with the same label. -/
def coreVertexEquiv (X : DaggerSSet.{u}) :
    (daggerCoreCandidate X).toSSet.obj (op ⦋0⦌) ≃ X.toSSet.obj (op ⦋0⦌) where
  toFun s := s.val
  invFun x := ⟨x, vertex_mem_ordinaryCoreCandidate X.toSSet x⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- The original homotopy fixed-point point-set functor of the same original dagger core. -/
def unitaryCoreAmbientFunctor : DaggerSSet.{u} ⥤ SSet.{u} :=
  daggerCoreFunctor ⋙ daggerHomotopyFixedPointFunctor

/-- The full canonical-vertex subcomplex functor applied to the same original dagger core. -/
def unitaryCoreFunctor : DaggerSSet.{u} ⥤ SSet.{u} :=
  daggerCoreFunctor ⋙ canonicalVertexFunctor

/-- The literal original unitary core object, with the verified original core as its input. -/
def unitaryCore (X : DaggerSSet.{u}) : SSet.{u} := unitaryCoreFunctor.obj X

/-- The original unitary core inclusions are a natural transformation into the original ambient. -/
def unitaryCoreInclusion : unitaryCoreFunctor.{u} ⟶ unitaryCoreAmbientFunctor :=
  Functor.whiskerLeft daggerCoreFunctor canonicalVertexInclusion

/-- The selected canonical vertices are exactly those associated to the original input vertices. -/
theorem unitaryCore_selected_vertices (X : DaggerSSet.{u}) :
    canonicalVertices (daggerCoreCandidate X) =
      Set.range (fun x : X.toSSet.obj (op ⦋0⦌) ↦
        canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x)) := by
  ext s
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨coreVertexEquiv X y, ?_⟩
    exact congrArg (canonicalZeroSimplex (daggerCoreCandidate X))
      ((coreVertexEquiv X).symm_apply_apply y)
  · rintro ⟨x, rfl⟩
    exact ⟨(coreVertexEquiv X).symm x, rfl⟩

/-- The object is exactly the original full subcomplex of the original core mapping object. -/
theorem unitaryCore_eq_canonicalVertexSubcomplex (X : DaggerSSet.{u}) :
    unitaryCore X = (canonicalVertexSubcomplex (daggerCoreCandidate X)).toSSet := rfl

/-- The original unitary core is Kan by the native full-vertex-subcomplex theorem. -/
theorem unitaryCore_kan (X : DaggerSSet.{u}) : (unitaryCore X).KanComplex :=
  canonicalVertexSubcomplex_kan (daggerCoreCandidate X)

/-- On an original dagger quasi-category the input to the construction is its greatest Kan core,
and the resulting original unitary core is a native Kan complex. -/
theorem unitaryCore_input_and_output_kan (X : DaggerSSet.{u})
    (hX : innerHornFillers X.toSSet) :
    (daggerCoreCandidate X).toSSet.KanComplex ∧ (unitaryCore X).KanComplex :=
  ⟨daggerCoreCandidate_kan X hX, unitaryCore_kan X⟩

/-- The unitary map is exactly the existing canonical full-subcomplex map of the original core map.
-/
theorem unitaryCoreFunctor_map {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    unitaryCoreFunctor.map f = canonicalVertexMap (daggerCoreMap f) := rfl

/-- The underlying inclusion is exactly the original full-subcomplex ambient inclusion. -/
theorem unitaryCoreInclusion_app (X : DaggerSSet.{u}) :
    unitaryCoreInclusion.app X = (canonicalVertexSubcomplex (daggerCoreCandidate X)).ι := rfl

end

end DaggerOriginalUnitaryCoreConstruction
