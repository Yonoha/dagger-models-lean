import AmalgamCollapse
import SimplicialIsoHoms

/-! All original old-Hom maps are monomorphisms at every arbitrary original pushout apex. -/

open CategoryTheory Limits DaggerModels
open DaggerAmalgamCollapse DaggerSimplicialIsoHoms

universe u
namespace DaggerAmalgamOriginalMonicity
noncomputable section
set_option autoImplicit false

variable (C B : DaggerSimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)
variable {P : DaggerSimplicialCat.{u, u}} (i : C ⟶ P) (j : B ⟶ P)
  (sq : IsPushout (DaggerDiscreteObjects.fromPoint C x)
    (DaggerDiscreteObjects.fromPoint B b) i j)

/-- The original splitting retains every object and every Hom simplex at each degree. -/
theorem original_degree_split (q : SimplexCategoryᵒᵖ) :
    degree (DaggerSimplicialCat.forget.map i) q ⋙
        degree (DaggerSimplicialCat.forget.map (original C B x b i j sq)) q =
      𝟭 (SimplicialEnrichment.At C.Obj q) := by
  rw [← degree_comp, ← Functor.map_comp, original_left, CategoryTheory.Functor.map_id, degree_id]
  rfl

/-- No object equality is suppressed in the arbitrary-apex argument. -/
theorem original_obj_split (a : C.Obj) :
    (original C B x b i j sq).obj (i.obj a) = a :=
  congrArg (fun F : C ⟶ C ↦ F.obj a) (original_left C B x b i j sq)

include B x b j sq in
/-- Reuse the existing faithful-composite cancellation, at every simplicial degree. -/
theorem original_degree_faithful (q : SimplexCategoryᵒᵖ) :
    (degree (DaggerSimplicialCat.forget.map i) q).Faithful :=
  CategoryTheory.Functor.Faithful.of_comp_eq
    (ℋ := CategoryTheory.Functor.Faithful.id) (original_degree_split C B x b i j sq q)

include B x b j sq in
/-- The injective function is literally the original full enriched-functor component. -/
theorem original_component_injective (a d : C.Obj) (q : SimplexCategoryᵒᵖ) :
    Function.Injective ((i.map a d).app q) := by
  have := original_degree_faithful C B x b i j sq q
  exact (degree (DaggerSimplicialCat.forget.map i) q).map_injective

include B x b j sq in
/-- The SAME original old-Hom map is Mono; no condition on either factor is needed. -/
theorem original_hom_mono (a d : C.Obj) : Mono (i.map a d) := by
  have : ∀ q, Mono ((i.map a d).app q) := fun q ↦
    (mono_iff_injective _).2 (original_component_injective C B x b i j sq a d q)
  exact NatTrans.mono_of_mono_app (i.map a d)

end
end DaggerAmalgamOriginalMonicity
