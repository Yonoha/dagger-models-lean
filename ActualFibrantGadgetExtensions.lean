import ActualFibrantGadgetData
import OriginalOrdinaryNerveQuasicategory
import OriginalOrdinaryLocalKanReplacementHomReconciled
import ProofActualNecklaceConeBridge

/-! Extend the whole original map to a locally Kan target across the chosen gadget unit. -/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory
open DaggerModels OrdinaryRigidification OriginalOrdinaryLocalKanReplacement
open DaggerActualFibrantGadgetData
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualFibrantGadgetExtensions
noncomputable section

/-- A locally Kan target has the exact horn-cell right lifting property to the terminal. -/
theorem terminal_right (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    OriginalOrdinaryHornGenerators.generators.rlp
      (OriginalOrdinaryTerminal.terminalMap D) := by
  apply (OriginalOrdinaryLocalFibrations.generators_rlp_iff _).mpr
  intro x y
  have : SSet.KanComplex (x ⟶[SSet.{u}] y) := hD x y
  have ht : IsTerminal
      ((OriginalOrdinaryTerminal.terminalMap D).obj x ⟶[SSet.{u}]
        (OriginalOrdinaryTerminal.terminalMap D).obj y) := by
    change IsTerminal (𝟙_ SSet.{u})
    exact isTerminalTensorUnit
  exact (isFibrant_iff_of_isTerminal _ ht).mp inferInstance

/-- The chosen unit has an enriched retraction at every locally Kan target.
The retraction is required only for this fixed target, not chosen naturally in targets. -/
theorem exists_retraction (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    ∃ r : replacement.obj D ⟶ D,
      OriginalOrdinaryLocalKanReplacement.unit.app D ≫ r = 𝟙 D := by
  let sq : CommSq (𝟙 D) (OriginalOrdinaryLocalKanReplacement.unit.app D)
      (OriginalOrdinaryTerminal.terminalMap D)
      (OriginalOrdinaryTerminal.terminalMap (replacement.obj D)) :=
    ⟨by simp only [Category.id_comp, OriginalOrdinaryTerminal.terminalMap_naturality]⟩
  have hp : HasLiftingProperty (OriginalOrdinaryLocalKanReplacement.unit.app D)
      (OriginalOrdinaryTerminal.terminalMap D) :=
    unit_left D _ (terminal_right D hD)
  have : sq.HasLift := hp.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left⟩

/-- The whole original adjoint retains precomposition by every simplicial map. -/
theorem adjunct_precomp (D : SimplicialCat.{u, u}) {X Y : SSet.{u}} (f : X ⟶ Y)
    (σ : Y ⟶ coherentNerve.obj D) :
    adjunct D (f ≫ σ) = rigidification.map f ≫ adjunct D σ :=
  rigidificationCoherentNerveAdjunction.homEquiv_naturality_left_symm f σ

/-- Restricting the extension along the actual gadget unit recovers the entire original map. -/
theorem unit_extension (D : SimplicialCat.{u, u}) (r : replacement.obj D ⟶ D)
    (hr : OriginalOrdinaryLocalKanReplacement.unit.app D ≫ r = 𝟙 D)
    {X : SSet.{u}} (σ : X ⟶ coherentNerve.obj D) :
    DaggerActualFibrantGadgetData.unit.app X ≫ extension D r σ = σ := by
  calc
    _ = rigidificationCoherentNerveAdjunction.unit.app X ≫
        coherentNerve.map
          ((OriginalOrdinaryLocalKanReplacement.unit.app (rigidification.obj X) ≫
            replacement.map (adjunct D σ)) ≫ r) := by
      simp only [DaggerActualFibrantGadgetData.unit, extension,
        CategoryTheory.Functor.map_comp, Category.assoc]
    _ = rigidificationCoherentNerveAdjunction.unit.app X ≫
        coherentNerve.map
          (adjunct D σ ≫ (OriginalOrdinaryLocalKanReplacement.unit.app D ≫ r)) := by
      rw [← OriginalOrdinaryLocalKanReplacement.unit.naturality,
        CategoryTheory.Functor.id_map, Category.assoc]
    _ = σ := by
      rw [hr, Category.comp_id]
      have h := rigidificationCoherentNerveAdjunction.homEquiv_naturality_right
        (𝟙 (rigidification.obj X)) (adjunct D σ)
      simpa only [Category.id_comp, rigidificationCoherentNerveAdjunction.homEquiv_id,
        adjunct, Equiv.apply_symm_apply] using h.symm

/-- All simplicial operators intertwine the full extended maps to the original target. -/
theorem extension_naturality (D : SimplicialCat.{u, u}) (r : replacement.obj D ⟶ D)
    {X Y : SSet.{u}} (f : X ⟶ Y) (σ : Y ⟶ coherentNerve.obj D) :
    gadget.map f ≫ extension D r σ = extension D r (f ≫ σ) := by
  simp only [extension, adjunct_precomp, CategoryTheory.Functor.map_comp,
    gadget, CategoryTheory.Functor.comp_map, Category.assoc]

/-- The chosen gadget is a quasicategory for every original simplicial set. -/
theorem gadget_quasicategory (X : SSet.{u}) : SSet.Quasicategory (gadget.obj X) :=
  DaggerOrdinaryRigidificationCof.OriginalNerveQuasicategory.replacement_quasicategory
    (rigidification.obj X)

end
end DaggerActualFibrantGadgetExtensions
