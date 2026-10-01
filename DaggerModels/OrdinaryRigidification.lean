import DaggerModels.SimplicialColimits
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Ordinary rigidification from the existing simplicial thickening

This module bundles Mathlib's `CategoryTheory.SimplicialThickening.functor` as a
cosimplicial object in the existing category of simplicial categories. Its left
Kan extension along `uliftYoneda` is left adjoint to the restricted Yoneda nerve.
The existence of this extension uses the proved `simplicialCatHasColimits`.
The comparison with Mathlib's actual `SimplicialNerve` is a natural isomorphism,
including naturality in target enriched functors; it transports the adjunction.

Objects and mapping spaces both remain in an arbitrary universe `u`. The finite
orders use `ULift.{u}`, exactly as in Mathlib's `SimplicialNerve`. No model
structure, fibrancy, or Quillen property is asserted.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace DaggerModels.OrdinaryRigidification

/-- Mathlib's thickening of the lifted finite order, bundled without replacing its homs. -/
noncomputable def simplexThickening (n : SimplexCategory) : SimplicialCat.{u, u} :=
  SimplicialCat.of (SimplicialThickening (ULift.{u} (Fin (n.len + 1))))

/-- The existing thickening functor, bundled as a cosimplicial simplicial category. -/
noncomputable def cosimplicialThickening : SimplexCategory ⥤ SimplicialCat.{u, u} where
  obj := simplexThickening
  map f := SimplicialThickening.functor f.toOrderHom.uliftMap
  map_id n := by
    exact SimplicialThickening.functor_id _
  map_comp f g := by
    exact SimplicialThickening.functor_comp f.toOrderHom.uliftMap g.toOrderHom.uliftMap

/-- The bundled hom is the original nerve of the original Mathlib path category. -/
theorem simplexThickening_hom (n : SimplexCategory)
    (i j : SimplicialThickening (ULift.{u} (Fin (n.len + 1)))) :
    (i ⟶[SSet.{u}] j) = nerve (i ⟶ j) := rfl

/-- Every simplex operator acts by Mathlib's existing enriched thickening functor. -/
theorem cosimplicialThickening_map {n m : SimplexCategory} (f : n ⟶ m) :
    cosimplicialThickening.{u}.map f =
      SimplicialThickening.functor f.toOrderHom.uliftMap := rfl

/-- The restricted Yoneda nerve retains the standard `ULift` around its enriched functors. -/
noncomputable def coherentNerve : SimplicialCat.{u, u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{u} cosimplicialThickening

/-- Simplices are the lifted sets of enriched functors from the standard thickening. -/
theorem coherentNerve_obj_obj (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    (coherentNerve.obj C).obj n = ULift.{u}
      (EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1))))
        C.Obj) := rfl

/-- Simplex operators act by precomposition with the standard thickening functor. -/
theorem coherentNerve_obj_map (C : SimplicialCat.{u, u})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (P : (coherentNerve.obj C).obj n) :
    ((coherentNerve.obj C).map f P).down =
      EnrichedFunctor.comp SSet
        (SimplicialThickening.functor f.unop.toOrderHom.uliftMap) P.down := rfl

/-- A target enriched functor acts by postcomposition on every simplex. -/
theorem coherentNerve_map_app {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) (P : (coherentNerve.obj C).obj n) :
    ((coherentNerve.map F).app n P).down = EnrichedFunctor.comp SSet P.down F := rfl

local instance : HasColimits.{u} SimplicialCat.{u, u} := simplicialCatHasColimits

local instance : HasColimitsOfSize.{0, u} SimplicialCat.{u, u} :=
  hasColimitsOfSizeShrink.{0, u} SimplicialCat.{u, u}

/-- Rigidification is the existing chosen left Kan extension of the thickening. -/
noncomputable def rigidification : SSet.{u} ⥤ SimplicialCat.{u, u} :=
  uliftYoneda.{u}.leftKanExtension cosimplicialThickening

/-- The ordinary rigidification/coherent-nerve adjunction follows from the presheaf API. -/
noncomputable def rigidificationCoherentNerveAdjunction :
    rigidification.{u} ⊣ coherentNerve.{u} := by
  unfold rigidification coherentNerve
  exact Presheaf.uliftYonedaAdjunction _
    (uliftYoneda.{u}.leftKanExtensionUnit cosimplicialThickening)

/-- Remove the restricted-Yoneda `ULift` to obtain Mathlib's actual simplicial nerve.
The target uses the canonical ordinary category with the same full enrichment. -/
noncomputable def coherentNerveObjIso (C : SimplicialCat.{u, u}) :
    coherentNerve.obj C ≅ SimplicialNerve (ForgetEnrichment SSet.{u} C.Obj) :=
  NatIso.ofComponents (fun _ ↦ uliftTrivial _) (by intro n m f; rfl)

/-- Mathlib's actual nerve on objects, with the usual postcomposition action on functors. -/
noncomputable def mathlibCoherentNerve : SimplicialCat.{u, u} ⥤ SSet.{u} where
  obj C := SimplicialNerve (ForgetEnrichment SSet.{u} C.Obj)
  map F :=
    { app _ P := EnrichedFunctor.comp SSet P F
      naturality n m f := by
        funext P
        apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
        intro i j
        simp [EnrichedFunctor.comp] }
  map_id C := by
    ext n P
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro i j
    exact Category.comp_id _
  map_comp F G := by
    ext n P
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro i j
    exact Category.assoc _ _ _

/-- The comparison is natural in both simplices and enriched functors of target categories. -/
noncomputable def coherentNerveIsoMathlib : coherentNerve.{u} ≅ mathlibCoherentNerve.{u} :=
  NatIso.ofComponents coherentNerveObjIso (by intro C D F; ext n P; rfl)

/-- The same constructed rigidification is left adjoint to Mathlib's actual coherent nerve. -/
noncomputable def rigidificationMathlibCoherentNerveAdjunction :
    rigidification.{u} ⊣ mathlibCoherentNerve.{u} :=
  rigidificationCoherentNerveAdjunction.ofNatIsoRight coherentNerveIsoMathlib

/-- On representables, the constructed rigidification is naturally the standard thickening. -/
noncomputable def rigidificationSimplexIso :
    uliftYoneda.{u} ⋙ rigidification.{u} ≅ cosimplicialThickening.{u} := by
  unfold rigidification
  exact Presheaf.isExtensionAlongULiftYoneda.{u} cosimplicialThickening.{u}

/-- A proposition wrapper for independently checking the constructed adjunction. -/
theorem rigidification_coherentNerve_adjunction :
    Nonempty (rigidification.{u} ⊣ coherentNerve.{u}) :=
  ⟨rigidificationCoherentNerveAdjunction⟩

/-- A proposition wrapper protecting the full natural comparison with Mathlib's nerve. -/
theorem coherentNerve_iso_mathlib :
    Nonempty (coherentNerve.{u} ≅ mathlibCoherentNerve.{u}) :=
  ⟨coherentNerveIsoMathlib⟩

/-- A proposition wrapper for the standard representable/thickening comparison. -/
theorem rigidification_simplex_iso :
    Nonempty (uliftYoneda.{u} ⋙ rigidification.{u} ≅ cosimplicialThickening.{u}) :=
  ⟨rigidificationSimplexIso⟩

end DaggerModels.OrdinaryRigidification
