import DaggerModels.FreeDagger
import DaggerModels.Presentable

/-!
# Reflection by the forgetful functor

An invertible underlying simplicial map has a dagger-compatible inverse.
Together with the proved existence and preservation of colimits, this lets
us verify a dagger colimit using its actual underlying simplicial cocone.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.DaggerSSet

/-- The inverse of an underlying isomorphism automatically commutes with dagger. -/
theorem forget_reflectsIsomorphisms : forget.{u}.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    change IsIso f.hom at hf
    let g : Y ⟶ X :=
      { hom := inv f.hom
        comm := by
          rw [← cancel_epi f.hom]
          simp only [IsIso.hom_inv_id_assoc]
          rw [← Category.assoc, f.comm, Category.assoc, ← Functor.map_comp,
            IsIso.hom_inv_id, SSet.opFunctor.map_id, Category.comp_id] }
    exact ⟨⟨g, by apply Hom.ext; exact IsIso.hom_inv_id f.hom,
      by apply Hom.ext; exact IsIso.inv_hom_id f.hom⟩⟩

/-- Forgetting dagger reflects all `u`-small colimits. -/
theorem forget_reflectsColimits : ReflectsColimits forget.{u} := by
  let : forget.{u}.ReflectsIsomorphisms := forget_reflectsIsomorphisms
  let : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
  let : PreservesColimits forget.{u} := forget_preservesColimits
  exact reflectsColimits_of_reflectsIsomorphisms

end DaggerModels.DaggerSSet
