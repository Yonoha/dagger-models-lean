import ActualFibrantNecklaceContractibility

/-! Propagate actual ordinal comparisons through the original functor F = N R C. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualFibrantGadgetData
open scoped Simplicial SSet.modelCategoryQuillen
universe u

namespace DaggerActualFibrantOrdinalPropagation
noncomputable section

local instance (A : Type u) [Category.{u} A] : EnrichedCategory SSet.{u} A :=
  DaggerUnitaryDiscrete.ordinaryEnriched A

/-- A nonempty Hom in a thin constant category is literally a terminal simplicial set. -/
theorem thin_hom_toUnit_GW (A : Type u) [Category.{u} A] [Quiver.IsThin A]
    (a b : (constant A).Obj)
    (h : Nonempty ((constant A).enriched.Hom a b |>.obj (op ⦋0⦌))) :
    DaggerSSetGluing.GW (toUnit ((constant A).enriched.Hom a b)) := by
  change Nonempty (a ⟶ b) at h
  obtain ⟨v⟩ := h
  let X : SSet.{u} := (constant A).enriched.Hom a b
  let c : 𝟙_ (SSet.{u}) ⟶ X :=
    { app := fun _ _ ↦ v, naturality := by intros; rfl }
  let e : X ≅ 𝟙_ (SSet.{u}) :=
    { hom := toUnit X
      inv := c
      hom_inv_id := by
        apply NatTrans.ext
        funext q x
        change (_ : a ⟶ b) = _
        exact Subsingleton.elim _ _
      inv_hom_id := isTerminalTensorUnit.hom_ext _ _ }
  have : IsIso e.hom := e.isIso_hom
  have : WeakEquivalence e.hom := inferInstance
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mp inferInstance

/-- The data specify an actual enriched map on the original C(X), with every Hom weak. -/
def hasOrdinalComparison (X : SSet.{u}) (n : ℕ) : Prop :=
  ∃ p : rigidification.obj X ⟶ constant (ULift.{u} (Fin (n + 1))),
    Function.Surjective p.obj ∧
      ∀ a b : (rigidification.obj X).Obj, DaggerSSetGluing.GW (p.map a b)

/-- Any nonempty original C(X) Hom is weakly contractible under this concrete comparison data. -/
theorem hom_toUnit_GW {X : SSet.{u}} {n : ℕ} (hp : hasOrdinalComparison X n)
    (a b : (rigidification.obj X).Obj)
    (h : Nonempty ((a ⟶[SSet.{u}] b).obj (op ⦋0⦌))) :
    DaggerSSetGluing.GW (toUnit (a ⟶[SSet.{u}] b)) := by
  obtain ⟨p, _, hh⟩ := hp
  let f := p.map a b
  let Y : SSet.{u} := (constant (ULift.{u} (Fin (n + 1)))).enriched.Hom (p.obj a) (p.obj b)
  have : WeakEquivalence f := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (hh a b)
  obtain ⟨v⟩ := h
  have ht : DaggerSSetGluing.GW (toUnit Y) :=
    thin_hom_toUnit_GW _ _ _ ⟨f.app (op ⦋0⦌) v⟩
  have : WeakEquivalence (toUnit Y) := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr ht
  have he : f ≫ toUnit Y = toUnit (a ⟶[SSet.{u}] b) := isTerminalTensorUnit.hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The actual F(X) again has an actual surjective local weak comparison to the same ordinal. -/
theorem next {X : SSet.{u}} {n : ℕ} (hp : hasOrdinalComparison X n) :
    hasOrdinalComparison (gadget.obj X) n := by
  obtain ⟨p, ho, hh⟩ := hp
  obtain ⟨q, _, hq, hqh⟩ := DaggerActualThinReplacementExtension.exists_trivial_extension
    (ULift.{u} (Fin (n + 1))) p ho hh
  let f := rigidification.map (coherentNerve.map q)
  let e := rigidification.mapIso (DaggerActualThinConstantCoherentNerve.ordinalNerveIso.{u} n)
  let t := DaggerActualOrdinalRigidificationComparison.comparison.{u} n
  obtain ⟨hf, hfo⟩ :=
    DaggerActualNerveTrivialFibrationRigidification.rigidification_nerve_local_and_surjective
      q hq hqh
  have heo : Function.Surjective e.hom.obj := by
    intro y
    refine ⟨e.inv.obj y, ?_⟩
    exact congrArg (fun g : rigidification.obj (Δ[n] : SSet.{u}) ⟶
      rigidification.obj (Δ[n] : SSet.{u}) ↦ g.obj y) e.inv_hom_id
  refine ⟨(f ≫ e.hom) ≫ t,
    (DaggerActualFibrantSimplexContractibility.comparison_surjective n).comp
      (heo.comp hfo), ?_⟩
  intro a b
  have : WeakEquivalence (f.map a b) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (hf a b)
  have : WeakEquivalence (e.hom.map (f.obj a) (f.obj b)) := inferInstance
  have : WeakEquivalence (t.map (e.hom.obj (f.obj a)) (e.hom.obj (f.obj b))) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerActualOrdinalRigidificationComparison.comparison_hom_GW n _ _)
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  change WeakEquivalence ((f.map a b ≫ e.hom.map (f.obj a) (f.obj b)) ≫
    t.map (e.hom.obj (f.obj a)) (e.hom.obj (f.obj b)))
  infer_instance

end
end DaggerActualFibrantOrdinalPropagation
