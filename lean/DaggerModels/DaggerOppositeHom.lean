import DaggerModels.DaggerStructureFromOpposite
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
Part I `bg.lem.creation`.
Lift exactly those enriched functors commuting with ordinary opposite dagger, then reflect
isomorphisms through the actual forgetful functor. Object and hom universes are independent.
-/

open CategoryTheory MonoidalCategory

universe o v

namespace DaggerModels.DaggerSimplicialCat

variable {C D : DaggerSimplicialCat.{o, v}}

/-- The original hom-level dagger compatibility implies the actual opposite square. -/
theorem Hom.commutingOpposite (F : Hom C D) :
    F.toEnrichedFunctor ≫ daggerNatural.app D =
      daggerNatural.app C ≫ SimplicialCat.oppositeFunctor.map F.toEnrichedFunctor :=
  daggerNatural.naturality F

/-- Lift an arbitrary enriched functor satisfying the actual opposite square. -/
def Hom.ofCommutingOpposite (F : C.toSimplicialCat ⟶ D.toSimplicialCat)
    (h : F ≫ daggerNatural.app D =
      daggerNatural.app C ≫ SimplicialCat.oppositeFunctor.map F) : Hom C D where
  toEnrichedFunctor := F
  map_dagger X Y := eq_of_heq (congr_arg_heq
    (fun G : C.toSimplicialCat ⟶ SimplicialCat.opposite D.toSimplicialCat ↦ G.map X Y) h)

/-- The lift retains the entire original enriched functor, including its object map. -/
@[simp]
theorem Hom.ofCommutingOpposite_toEnrichedFunctor
    (F : C.toSimplicialCat ⟶ D.toSimplicialCat)
    (h : F ≫ daggerNatural.app D =
      daggerNatural.app C ≫ SimplicialCat.oppositeFunctor.map F) :
    (Hom.ofCommutingOpposite F h).toEnrichedFunctor = F := rfl

/-- Forgetting the lifted dagger functor is exactly the specified ordinary functor. -/
@[simp]
theorem forget_map_ofCommutingOpposite (F : C.toSimplicialCat ⟶ D.toSimplicialCat)
    (h : F ≫ daggerNatural.app D =
      daggerNatural.app C ≫ SimplicialCat.oppositeFunctor.map F) :
    forget.map (Hom.ofCommutingOpposite F h) = F := rfl

/-- Recovering a dagger functor from its own opposite square changes no data. -/
@[simp]
theorem Hom.ofCommutingOpposite_commutingOpposite (F : Hom C D) :
    Hom.ofCommutingOpposite F.toEnrichedFunctor F.commutingOpposite = F := by
  apply Hom.ext
  rfl

/-- The ordinary inverse of a dagger functor automatically commutes with opposite dagger. -/
theorem inverse_commutingOpposite (F : C ⟶ D) [IsIso (forget.map F)] :
    inv (forget.map F) ≫ daggerNatural.app C =
      daggerNatural.app D ≫ SimplicialCat.oppositeFunctor.map (inv (forget.map F)) := by
  have hf : forget.map F ≫ daggerNatural.app D =
      daggerNatural.app C ≫ SimplicialCat.oppositeFunctor.map (forget.map F) :=
    F.commutingOpposite
  apply (cancel_epi (forget.map F)).1
  simp only [← Category.assoc]
  rw [IsIso.hom_inv_id, Category.id_comp, hf, Category.assoc,
    ← SimplicialCat.oppositeFunctor.map_comp, IsIso.hom_inv_id,
    SimplicialCat.oppositeFunctor.map_id]
  exact (Category.comp_id (daggerNatural.app C)).symm

/-- The actual ordinary inverse lifted to the original dagger hom bundle. -/
noncomputable def inverseOfOrdinaryIso (F : C ⟶ D) [IsIso (forget.map F)] : Hom D C :=
  Hom.ofCommutingOpposite (inv (forget.map F)) (inverse_commutingOpposite F)

@[simp]
theorem forget_map_inverseOfOrdinaryIso (F : C ⟶ D) [IsIso (forget.map F)] :
    forget.map (inverseOfOrdinaryIso F) = inv (forget.map F) := rfl

/-- The forward and inverse laws follow through the actual faithful forgetful functor. -/
@[simp]
theorem comp_inverseOfOrdinaryIso (F : C ⟶ D) [IsIso (forget.map F)] :
    F ≫ inverseOfOrdinaryIso F = 𝟙 C := by
  apply forget.map_injective
  change forget.map F ≫ inv (forget.map F) = forget.map (𝟙 C)
  rw [IsIso.hom_inv_id]
  exact (forget.map_id C).symm

@[simp]
theorem inverseOfOrdinaryIso_comp (F : C ⟶ D) [IsIso (forget.map F)] :
    inverseOfOrdinaryIso F ≫ F = 𝟙 D := by
  apply forget.map_injective
  change inv (forget.map F) ≫ forget.map F = forget.map (𝟙 D)
  rw [IsIso.inv_hom_id]
  exact (forget.map_id D).symm

/-- Ordinary dagger forgetting reflects actual isomorphisms at independent universes. -/
instance forgetReflectsIsomorphisms : forget.{o, v}.ReflectsIsomorphisms where
  reflects F := ⟨inverseOfOrdinaryIso F, comp_inverseOfOrdinaryIso F, inverseOfOrdinaryIso_comp F⟩

/-- The reflection property for the actual ordinary forgetful functor. -/
theorem forget_reflectsIsomorphisms : forget.{o, v}.ReflectsIsomorphisms := inferInstance

end DaggerModels.DaggerSimplicialCat
