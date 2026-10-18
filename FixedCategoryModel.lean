import FixedCategoryColimits
import FixedCategoryMonadicLimits
import FixedCategorySmallObject
import FixedCategoryCellClosure
import FixedCategoryRightProper
import TopCatModelCategory.TopPackage

set_option autoImplicit false

/-! The actual fixed-object dagger simplicial CATEGORY model structure.
The original I/J, all-Hom geometric W and local fibrations F are retained.
The simplicial compatibility clause is a separate obligation. -/

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerFixedCategoryGenerators
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerFixedCategoryModel

noncomputable section

variable (O : Type u)

scoped instance categoryWeakEquivalences :
    CategoryWithWeakEquivalences (FixedDaggerSimplicialCat O) where
  weakEquivalences := W O

scoped instance categoryFibrations : CategoryWithFibrations (FixedDaggerSimplicialCat O) where
  fibrations := F O

scoped instance categoryCofibrations : CategoryWithCofibrations (FixedDaggerSimplicialCat O) where
  cofibrations := (I O).rlp.llp

/-- The Nat shape and the original u-small coproduct batches have independent universes. -/
theorem cells_le_W :
    (MorphismProperty.coproducts.{u} (J O)).pushouts.transfiniteCompositionsOfShape ℕ ≤ W O := by
  have h := MorphismProperty.transfiniteCompositionsOfShape_le_llp_rlp
    (MorphismProperty.coproducts.{u} (J O)).pushouts ℕ
  have h' : (MorphismProperty.coproducts.{u} (J O)).pushouts.transfiniteCompositionsOfShape ℕ ≤
      (J O).rlp.llp := by
    simpa only [MorphismProperty.rlp_pushouts, MorphismProperty.rlp_coproducts] using h
  exact h'.trans (DaggerFixedCategoryCellClosure.J_rlp_llp_le_W O)

/-- Preserve the same original relative-cell functor, rather than another chosen chain. -/
theorem preservesNatCellColimit (X : FixedDaggerSimplicialCat O)
    [IsFinitelyPresentable.{u} X] {A B : FixedDaggerSimplicialCat O} (f : A ⟶ B)
    (hf : RelativeCellComplex.{u} (fun (_ : ℕ) ↦ (I O ⊔ J O).homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op X)) := by
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (coyoneda.obj (Opposite.op X))
  infer_instance

/-- All sixteen recognition inputs belong to the original category and original families. -/
def recognitionPackage : TopPackage.{u} (FixedDaggerSimplicialCat O) where
  I' := I O
  J' := J O
  S' := {C | IsFinitelyPresentable.{u} C}
  hasFiniteLimits := hasFiniteLimits_of_hasLimitsOfSize _
  hasColimitsOfSize := DaggerFixedCategoryColimits.hasSmallColimits
  locallySmall := CategoryTheory.locallySmall_self _
  isSmall_I' := I_isSmall O
  isSmall_J' := J_isSmall O
  hasTwoOutOfThreeProperty := DaggerFixedCategoryGenerators.W_twoOutOfThree O
  isStableUnderRetracts := DaggerFixedCategoryGenerators.W_retracts O
  rlp_I'_le_rlp_J' := I_rlp_le_J_rlp O
  fibration_is_trivial_iff' p hp := by
    rw [HomotopicalAlgebra.weakEquivalence_iff]
    exact I_rlp_iff_W_of_J_rlp O p hp
  src_I_le_S' i hi := DaggerFixedCategoryFilteredDomains.I_domain_isFinitelyPresentable O i hi
  src_J_le_S' i hj := DaggerFixedCategoryFilteredDomains.J_domain_isFinitelyPresentable O i hj
  infiniteCompositions_le_W' := cells_le_W O
  preservesColimit' X hX {_ _} f hf := by
    letI : IsFinitelyPresentable.{u} X := hX
    exact preservesNatCellColimit O X f hf

/-- This model structure has no caller model or acyclicity hypothesis. -/
scoped instance modelCategory : ModelCategory (FixedDaggerSimplicialCat O) :=
  (recognitionPackage O).modelCategory rfl (J_rlp_eq O).symm

theorem weakEquivalences_eq : weakEquivalences (FixedDaggerSimplicialCat O) = W O := rfl

theorem fibrations_eq : fibrations (FixedDaggerSimplicialCat O) = F O := rfl

theorem cofibrations_eq : cofibrations (FixedDaggerSimplicialCat O) = (I O).rlp.llp := rfl

theorem weakEquivalence_iff_homwise {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    WeakEquivalence f ↔ ∀ x y : O, WeakEquivalence (f.val.map x y) := by
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  exact W_iff_homwise f

theorem weakEquivalence_iff_geometric {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    WeakEquivalence f ↔ ∀ x y : O,
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.val.map x y))) := by
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  exact W_iff_geometric f

theorem fibration_iff_homwise {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    Fibration f ↔ ∀ x y : O, Fibration (f.val.map x y) := by
  rw [HomotopicalAlgebra.fibration_iff]
  exact F_iff_homwise f

/-- Right properness of this actual model, retaining the original four-leg pullback. -/
theorem weakEquivalence_of_isPullback {E' E B' B : FixedDaggerSimplicialCat O}
    {t : E' ⟶ E} {l : E' ⟶ B'} {r : E ⟶ B} {b : B' ⟶ B}
    (sq : IsPullback t l r b) [Fibration r] [WeakEquivalence b] : WeakEquivalence t := by
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  exact DaggerFixedCategoryRightProper.W_of_isPullback sq
    (mem_fibrations r) (mem_weakEquivalences b)

theorem I_rlp_eq_trivialFibrations :
    (I O).rlp = trivialFibrations (FixedDaggerSimplicialCat O) := I_rlp_eq O

theorem J_rlp_eq_fibrations :
    (J O).rlp = fibrations (FixedDaggerSimplicialCat O) := J_rlp_eq O

theorem trivialCofibrations_eq_J_rlp_llp :
    trivialCofibrations (FixedDaggerSimplicialCat O) = (J O).rlp.llp := by
  rw [J_rlp_eq_fibrations, HomotopicalAlgebra.fibrations_llp]

/-- The original small-object choices are reused, including their Arrow functor and legs. -/
def cofibrationFactorization : MorphismProperty.FunctorialFactorizationData
    (cofibrations (FixedDaggerSimplicialCat O))
    (trivialFibrations (FixedDaggerSimplicialCat O)) :=
  DaggerFixedCategorySmallObject.I_semanticFactorizationData O

def trivialCofibrationFactorization : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (FixedDaggerSimplicialCat O))
    (fibrations (FixedDaggerSimplicialCat O)) :=
  (DaggerFixedCategorySmallObject.J_semanticFactorizationData O).ofLE
    (trivialCofibrations_eq_J_rlp_llp O).symm.le le_rfl

def cofibrationMapFactorization {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    MorphismProperty.MapFactorizationData (cofibrations (FixedDaggerSimplicialCat O))
      (trivialFibrations (FixedDaggerSimplicialCat O)) f :=
  (cofibrationFactorization O).factorizationData f

def trivialCofibrationMapFactorization {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    MorphismProperty.MapFactorizationData (trivialCofibrations (FixedDaggerSimplicialCat O))
      (fibrations (FixedDaggerSimplicialCat O)) f :=
  (trivialCofibrationFactorization O).factorizationData f

end

end DaggerFixedCategoryModel
