import NativeInnerPushoutIhom
import NativeBoundaryHoEquivalence

/-!
# Full native inner-left maps satisfy the original Joyal mapping weak predicate

Use the full native internal-Hom pullback square over the original terminal target.
Every boundary lifts by the proved whole inner pushout-product. Thus the literal
precomposition map is full mono-right, and its actual ho functor is an equivalence.
All quasi-category targets and all simplicial degrees are retained.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial HomotopicalAlgebra
open DaggerNativeInnerHornFactorization DaggerNativeInnerPushoutIhom
open DaggerNativeBoundaryHoEquivalence DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeInnerJoyalMappingWeak
noncomputable section

/-- The actual internal Hom of any object into the native terminal is itself terminal. -/
def ihomTerminal (A : SSet.{u}) : IsTerminal ((ihom A).obj (⊤_ SSet.{u})) :=
  IsTerminal.isTerminalObj (ihom A) _ terminalIsTerminal

/-- A full native internal-Hom pullback square whose projection is exactly precomposition. -/
def terminalPullback {A B : SSet.{u}} (i : A ⟶ B) (Z : SSet.{u}) :
    SSet.PullbackIhom i (terminal.from Z) where
  pt := (ihom A).obj Z
  fst := 𝟙 _
  snd := (ihomTerminal B).from _
  isPullback := by
    haveI : IsIso ((MonoidalClosed.internalHom.map i.op).app (⊤_ SSet.{u})) :=
      isIso_of_isTerminal (ihomTerminal B) (ihomTerminal A) _
    exact IsPullback.of_horiz_isIso ⟨(ihomTerminal A).hom_ext _ _⟩

/-- The projection of the full terminal pullback is the entire original precomposition map. -/
theorem terminalPullback_π {A B : SSet.{u}} (i : A ⟶ B) (Z : SSet.{u}) :
    (terminalPullback i Z).π = (MonoidalClosed.pre i).app Z := by
  simpa only [terminalPullback, Category.comp_id] using (terminalPullback i Z).π_fst

/-- Every original boundary lifts against precomposition by an arbitrary full inner-left map. -/
theorem inner_pre_boundary_rlp {A B : SSet.{u}} (i : A ⟶ B) (hi : innerAnodyne i)
    (Z : SSet.{u}) [Z.Quasicategory] (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι ((MonoidalClosed.pre i).app Z) := by
  let sq : SSet.PushoutTensor i (SSet.boundary n).ι :=
    Functor.PushoutObjObj.ofHasPushout _ _ _
  have hp : innerFibrations (terminal.from Z) :=
    (quasicategory_iff_inner_terminal _ terminalIsTerminal).1 inferInstance
  have h := (SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom sq
    (terminalPullback i Z)).1 (pushout_inner_left hi sq _ hp)
  simpa only [terminalPullback_π] using h

/-- The literal precomposition map is full mono-right for every quasi-category target. -/
theorem inner_pre_mono_rlp {A B : SSet.{u}} (i : A ⟶ B) (hi : innerAnodyne i)
    (Z : SSet.{u}) [Z.Quasicategory] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((MonoidalClosed.pre i).app Z) :=
  DaggerNativeBoundaryJoyalMappingWeak.boundary_rlp_monomorphisms _
    (inner_pre_boundary_rlp i hi Z)

/-- Every native inner-left map satisfies exactly the original full Joyal mapping weak test. -/
theorem innerAnodyne_weak {A B : SSet.{u}} (i : A ⟶ B) (hi : innerAnodyne i) :
    weakCategoricalEquivalences i := by
  intro Z _
  exact monoRight_ho_isEquivalence _ (inner_pre_mono_rlp i hi Z)

/-- The actual full functorial quasi-category replacement unit is Joyal mapping weak. -/
theorem unit_weak (X : SSet.{u}) : weakCategoricalEquivalences (unit.app X) :=
  innerAnodyne_weak _ (unit_innerAnodyne X)

end
end DaggerNativeInnerJoyalMappingWeak
