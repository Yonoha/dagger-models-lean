import DaggerModels.DaggerSimplicialMonadicity
import Mathlib.CategoryTheory.Generator.StrongGenerator
import Mathlib.CategoryTheory.Functor.EpiMono

/-! Free images of strong generators under a faithful,
isomorphism-reflecting right adjoint. This does not assume the right adjoint is
full and does not assert cocompleteness or local finite presentability. -/

open CategoryTheory

universe u v u' v'

namespace DaggerModels.AdjunctionStrongGenerator

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Faithful]
  {P : ObjectProperty C}

include adj in
theorem separating (hP : P.IsSeparating) : (P.map F).IsSeparating := by
  intro X Y f g h
  apply G.map_injective
  apply hP
  intro A hA k
  have he := h (F.obj A) (P.prop_map_obj F hA) ((adj.homEquiv A X).symm k)
  have he' := congrArg (adj.homEquiv A Y) he
  simpa only [adj.homEquiv_naturality_right, Equiv.apply_symm_apply] using he'

include adj in
theorem strongGenerator [G.ReflectsIsomorphisms] (hP : P.IsStrongGenerator) :
    (P.map F).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨separating adj hP.isSeparating, fun X Y i _ hi ↦ ?_⟩
  letI := Functor.preservesMonomorphisms_of_adjunction adj
  haveI : IsIso (G.map i) := hP.isIso_of_mono (G.map i) (fun A hA k ↦ by
    obtain ⟨f, hf⟩ := hi (F.obj A) (P.prop_map_obj F hA) ((adj.homEquiv A Y).symm k)
    refine ⟨adj.homEquiv A X f, ?_⟩
    have he := congrArg (adj.homEquiv A Y) hf
    simpa only [adj.homEquiv_naturality_right, Equiv.apply_symm_apply] using he)
  exact isIso_of_reflects_iso i G

/-- Applies to the actual finite-path free functor, without a fullness premise. -/
theorem freeDaggerSimplicialCategory {P : ObjectProperty DaggerSimplicialGraph.{u}}
    (hP : P.IsStrongGenerator) :
    (P.map FreeDaggerSimplicialCategory.functor).IsStrongGenerator :=
  strongGenerator FreeDaggerSimplicialCategory.adjunction hP

end DaggerModels.AdjunctionStrongGenerator
