import OriginalUnitaryCoreEvaluation

/-!
# Original unitary-component surjectivity implies original core-component surjectivity

This uses the retained native simplicial-set π₀, the actual original unitary
map and the actual original core map. The proof evaluates the original
canonical vertices and uses the existing bijectivity theorem for π₀ of the
realization-singular unit. It does not assume the intrinsic recognition
theorem or ordinary quasi-category essential-surjectivity recognition.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalDaggerCoreCandidate DaggerOriginalDaggerCoreCandidateFunctor
open DaggerOriginalUnitaryCoreConstruction DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerOriginalUnitaryCoreEvaluation

universe u

namespace DaggerOriginalUnitaryCoreComponentSurjectivity

noncomputable section

/-- Native π₀-surjectivity is exactly surjectivity on components of original canonical vertices.
-/
theorem unitary_pi0_surjective_iff_canonical {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) ↔
      ∀ y : Y.toSSet.obj (op ⦋0⦌), ∃ x : X.toSSet.obj (op ⦋0⦌),
        SSet.π₀.mk (canonicalUnitaryVertex Y (f.hom.app (op ⦋0⦌) x)) =
          SSet.π₀.mk (canonicalUnitaryVertex Y y) := by
  constructor
  · intro h y
    obtain ⟨c, hc⟩ := h (SSet.π₀.mk (canonicalUnitaryVertex Y y))
    obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective c
    obtain ⟨x, rfl⟩ := canonicalUnitaryVertex_surjective X s
    exact ⟨x, by simpa only [SSet.mapπ₀_mk, canonicalUnitaryVertex_naturality] using hc⟩
  · intro h c
    obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective c
    obtain ⟨y, rfl⟩ := canonicalUnitaryVertex_surjective Y s
    obtain ⟨x, hx⟩ := h y
    refine ⟨SSet.π₀.mk (canonicalUnitaryVertex X x), ?_⟩
    simpa only [SSet.mapπ₀_mk, canonicalUnitaryVertex_naturality] using hx

/-- Every original target vertex lies in the image component of the actual original core map.
-/
theorem core_canonical_component_surjectivity {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (h : Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)))
    (y : Y.toSSet.obj (op ⦋0⦌)) :
    ∃ x : X.toSSet.obj (op ⦋0⦌),
      SSet.π₀.mk ((daggerCoreMap f).hom.app (op ⦋0⦌) ((coreVertexEquiv X).symm x)) =
        SSet.π₀.mk ((coreVertexEquiv Y).symm y) := by
  obtain ⟨x, hx⟩ := (unitary_pi0_surjective_iff_canonical f).1 h y
  refine ⟨x, ?_⟩
  rw [coreVertexEquiv_naturality]
  apply (SSet.bijective_mapπ₀_sSetTopAdj_unit_app (daggerCoreCandidate Y).toSSet).1
  have he := congrArg (SSet.mapπ₀ (unitaryEvaluation Y)) hx
  simpa only [SSet.mapπ₀_mk, unitaryEvaluation_canonical] using he

/-- Surjectivity on actual unitary components implies surjectivity on actual ordinary-core π₀.
-/
theorem core_pi0_surjective_of_unitary_pi0_surjective {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (h : Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f))) :
    Function.Surjective (SSet.mapπ₀ (daggerCoreMap f).hom) := by
  intro c
  obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective c
  obtain ⟨x, hx⟩ := core_canonical_component_surjectivity f h (coreVertexEquiv Y y)
  refine ⟨SSet.π₀.mk ((coreVertexEquiv X).symm x), ?_⟩
  simpa only [SSet.mapπ₀_mk, Equiv.symm_apply_apply] using hx

end

end DaggerOriginalUnitaryCoreComponentSurjectivity
