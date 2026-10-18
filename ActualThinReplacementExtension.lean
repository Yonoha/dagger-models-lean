import NativeKanFibrationToSubsingleton
import ActualConstantSimplicialCategory

/-! Extend an actual locally weak map to a thin constant category through local Kan replacement. -/

set_option autoImplicit false
open CategoryTheory Opposite HomotopicalAlgebra DaggerModels
open OriginalOrdinaryLocalKanReplacement DaggerActualConstantSimplicialCategory
open DaggerOriginalEnrichedHomTransport
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualThinReplacementExtension
noncomputable section

local instance (A : Type u) [Category.{u} A] : EnrichedCategory SSet.{u} A :=
  DaggerUnitaryDiscrete.ordinaryEnriched A

variable {C D : SimplicialCat.{u, u}}

/-- The entire enriched extension uses the chosen replacement functor. -/
def extend (p : C ⟶ D) (r : replacement.obj D ⟶ D) : replacement.obj C ⟶ D :=
  replacement.map p ≫ r

/-- The extension restricts to the whole original enriched functor. -/
theorem unit_extend (p : C ⟶ D) (r : replacement.obj D ⟶ D)
    (hr : unit.app D ≫ r = 𝟙 D) : unit.app C ≫ extend p r = p := by
  unfold extend
  rw [← Category.assoc, ← unit.naturality, CategoryTheory.Functor.id_map,
    Category.assoc, hr]
  exact CategoryTheory.Category.comp_id p

/-- Surjectivity is retained on the original object types. -/
theorem extend_surjective (p : C ⟶ D) (r : replacement.obj D ⟶ D)
    (hr : unit.app D ≫ r = 𝟙 D) (ho : Function.Surjective p.obj) :
    Function.Surjective (extend p r).obj := by
  intro d
  obtain ⟨c, hc⟩ := ho d
  refine ⟨(unit.app C).obj c, ?_⟩
  have h := congrArg (fun f : C ⟶ D ↦ f.obj c) (unit_extend p r hr)
  exact h.trans hc

/-- Weakness of every actual Hom follows from the unit's proved anodyne Hom maps. -/
theorem extend_hom_GW (p : C ⟶ D) (r : replacement.obj D ⟶ D)
    (hr : unit.app D ≫ r = 𝟙 D)
    (hp : ∀ a b : C.Obj, DaggerSSetGluing.GW (p.map a b))
    (x y : (replacement.obj C).Obj) : DaggerSSetGluing.GW ((extend p r).map x y) := by
  obtain ⟨a, rfl⟩ := (unit_obj_bijective C).surjective x
  obtain ⟨b, rfl⟩ := (unit_obj_bijective C).surjective y
  have hu : DaggerSSetGluing.GW ((unit.app C).map a b) :=
    OriginalOrdinaryLocalKanReplacementHom.unit_hom_geometric C a b
  have hc : DaggerSSetGluing.GW ((unit.app C ≫ extend p r).map a b) :=
    (GW_functorHom_congr (unit_extend p r hr) a b).mpr (hp a b)
  have : WeakEquivalence ((unit.app C).map a b) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr hu
  have : WeakEquivalence ((unit.app C).map a b ≫
      (extend p r).map ((unit.app C).obj a) ((unit.app C).obj b)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr hc
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  exact weakEquivalence_of_precomp ((unit.app C).map a b) _

/-- An original surjective local weak map to a thin constant target extends to local trivial fibrations.
No weakness of the desired ordinary counit is supplied. -/
theorem exists_trivial_extension (A : Type u) [Category.{u} A] [Quiver.IsThin A]
    (p : C ⟶ constant A) (ho : Function.Surjective p.obj)
    (hp : ∀ a b : C.Obj, DaggerSSetGluing.GW (p.map a b)) :
    ∃ q : replacement.obj C ⟶ constant A,
      unit.app C ≫ q = p ∧ Function.Surjective q.obj ∧
      ∀ x y : (replacement.obj C).Obj, trivialFibrations SSet.{u} (q.map x y) := by
  obtain ⟨r, hr⟩ := DaggerActualFibrantGadgetExtensions.exists_retraction
    (constant A) (constant_locallyKan A)
  refine ⟨extend p r, unit_extend p r hr, extend_surjective p r hr ho, ?_⟩
  intro x y
  rw [mem_trivialFibrations_iff]
  refine ⟨DaggerNativeKanFibrationToSubsingleton.fibration _
    (replacement_locallyKan C x y) ?_, ?_⟩
  · intro s
    change Subsingleton ((extend p r).obj x ⟶ (extend p r).obj y)
    infer_instance
  · exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (extend_hom_GW p r hr hp x y)

end
end DaggerActualThinReplacementExtension
