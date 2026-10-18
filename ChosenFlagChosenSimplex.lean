import ChosenFlagChosenPostcomp
import ChosenFlagChosenNecklaceComparison
import ChosenFlagSimplexCocone

open CategoryTheory Functor Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

theorem chosenNecklaceIso_single (n : ℕ) :
    chosenNecklaceIso.{u} (single n) = singleChosenIso n := by
  apply Iso.ext
  apply forgetNC_cancel (single n)
  exact (chosenNecklaceIso_inclusion (single n)).trans
    (singleCanonicalComparison.{u} n).inclusion.symm

/-- Exact direct-path identification on representables, with the same actual ρ. -/
theorem chosenFlagFunctor_simplex (n : ℕ) :
    chosenFlagFunctor (Δ[n] : SSet.{u}) ≫ (ρ.app ⦋n⦌).hom = (flagSimplexIso n).hom := by
  let e := flagCategoryFunctor.mapIso (singleIso.{u} n)
  apply (cancel_epi e.hom).mp
  change EMap (singleIso n).hom ≫
    (chosenFlagFunctor Δ[n] ≫ (ρ.app ⦋n⦌).hom) =
      e.hom ≫ (flagSimplexIso n).hom
  rw [← Category.assoc, chosenFlagFunctor_naturality, chosenFlagFunctor_necklace_exact]
  simp only [flagChosenNecklaceIso, Iso.trans_hom, Iso.symm_hom,
    chosenNecklaceIso_single, singleChosenIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, flagSimplexIso, Category.assoc]
  rw [← Category.assoc (C.map (singleIso n).inv) (C.map (singleIso n).hom),
    ← C.map_comp, Iso.inv_hom_id, C.map_id]
  change _ = e.hom ≫ e.inv ≫
    (necklaceFlagIso (single n)).hom ≫ (singleNCIso n).hom
  rw [Iso.hom_inv_id_assoc]
  rw [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

/-- The actual left-Kan unit equals the exact flag simplex inverse followed by evaluation. -/
theorem simplexFlagUnit_chosen (n : SimplexCategory) :
    simplexFlagUnit.{u}.app n ≫ chosenFlagFunctor (uliftYoneda.obj n) =
      thickeningUnit.app n := by
  induction n using SimplexCategory.rec with | _ n
  apply (cancel_mono (ρ.app ⦋n⦌).hom).mp
  change (simplexFlagUnit.app ⦋n⦌ ≫ chosenFlagFunctor (Δ[n] : SSet.{u})) ≫
      (ρ.app ⦋n⦌).hom = thickeningUnit.app ⦋n⦌ ≫ (ρ.app ⦋n⦌).hom
  rw [Category.assoc, chosenFlagFunctor_simplex, representable_unit_hom]
  exact Iso.inv_hom_id (flagSimplexIso n)

theorem simplexFlagLeg_chosen (X : SSet.{u}) (σ : SimplexIndex X) :
    simplexFlagLeg X σ ≫ chosenFlagFunctor X =
      thickeningUnit.app σ.left ≫ C.map σ.hom := by
  unfold simplexFlagLeg
  rw [Category.assoc, chosenFlagFunctor_naturality, ← Category.assoc, simplexFlagUnit_chosen]

end

end DaggerChosenRigidificationNecklace
