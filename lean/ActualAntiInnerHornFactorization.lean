import NativeInnerHornFactorization
import ActualAntiJoyalAdjointLifting
import Mathlib.CategoryTheory.Presentable.Adjunction

/-!
# Full functorial inner-horn replacement in the actual anti-involutive category

Free the entire original inner-horn family using the actual original adjunction.
The finite-domain small-object argument constructs full factorizations. The right class
is exactly the underlying native inner-fibration class; the left class is normal in every
degree. The resulting functor and unit are actual anti-involutive maps. Neither Joyal
mapping weakness of the unit nor the required second Joyal factorization is asserted.
-/
set_option autoImplicit false
open CategoryTheory Limits MorphismProperty Simplicial HomotopicalAlgebra DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerActualAntiNormalFactorization
open DaggerNativeInnerHornFactorization
universe u
namespace DaggerActualAntiInnerHornFactorization
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
attribute [local instance] SmallObjectFiniteDomains.aleph0OrdOrderBot

/-- Free the literal full inner-horn family in the original anti-involutive category. -/
def generator (a : DaggerNativeInnerHornFactorization.Index) :=
  freeAnti.{u}.map (DaggerNativeInnerHornFactorization.generator a)

def generators : MorphismProperty AntiInvolutiveSSet.{u} := ofHoms generator

def innerFibrations : MorphismProperty AntiInvolutiveSSet.{u} := generators.rlp

def innerAnodyne : MorphismProperty AntiInvolutiveSSet.{u} := generators.rlp.llp

instance generatorsSmall : IsSmall.{u} generators.{u} := isSmall_ofHoms _

/-- The existing cofree adjunction gives preservation of all needed filtered colimits. -/
instance forgetAccessible : antiForget.{u}.IsCardinalAccessible Cardinal.aleph0.{u} where

/-- The actual free inner-horn domains are finitely presentable by the actual free adjunction. -/
theorem generators_domain_finitePresentable {A B : AntiInvolutiveSSet.{u}} (i : A ⟶ B)
    (hi : generators i) : IsFinitelyPresentable.{u} A := by
  obtain ⟨a⟩ := hi
  exact freeAntiAdjunction.isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 _

instance generatorsCardinal : generators.{u}.IsCardinalForSmallObjectArgument
    Cardinal.aleph0.{u} :=
  SmallObjectFiniteDomains.isCardinalForSmallObjectArgument_aleph0.{u} _
    (fun i hi ↦ generators_domain_finitePresentable i hi)

instance generatorsSmallObject : HasSmallObjectArgument.{u} generators.{u} :=
  SmallObjectFiniteDomains.hasSmallObjectArgument.{u} _
    (fun i hi ↦ generators_domain_finitePresentable i hi)

/-- Native small-object factorization for every actual anti-involutive morphism. -/
def factorization : innerAnodyne.{u}.FunctorialFactorizationData innerFibrations.{u} :=
  SmallObject.functorialFactorizationData generators Cardinal.aleph0.{u}

instance hasFunctorialFactorization :
    innerAnodyne.{u}.HasFunctorialFactorization innerFibrations.{u} := ⟨⟨factorization⟩⟩

/-- The whole actual inner-right class is created by the original underlying functor. -/
theorem innerFibrations_iff_underlying {X Y : AntiInvolutiveSSet.{u}} (p : X ⟶ Y) :
    innerFibrations p ↔ DaggerNativeInnerHornFactorization.innerFibrations p.hom := by
  constructor
  · intro hp A B i hi
    obtain ⟨a⟩ := hi
    exact (freeAntiAdjunction.hasLiftingProperty_iff _ p).1 (hp _ ⟨a⟩)
  · intro hp A B i hi
    obtain ⟨a⟩ := hi
    exact (freeAntiAdjunction.hasLiftingProperty_iff _ p).2 (hp _ ⟨a⟩)

/-- Free inner horns are genuinely normal in all degrees, including zero. -/
theorem generators_le_normal : generators.{u} ≤ normalMonos.{u} := by
  intro A B i hi
  obtain ⟨a⟩ := hi
  haveI : Mono (DaggerNativeInnerHornFactorization.generator a) := by
    dsimp [DaggerNativeInnerHornFactorization.generator]
    infer_instance
  exact DaggerModels.OriginalAntiInvolutiveFreePairMono.freeAnti_map_normal _

/-- The entire inner-left class is normal, without substituting a smaller normal predicate. -/
theorem innerAnodyne_le_normal : innerAnodyne.{u} ≤ normalMonos.{u} := by
  have h := antitone_llp (antitone_rlp generators_le_normal.{u})
  rw [← normalMonos_eq_rlp_llp] at h
  exact h

/-- The actual terminal-arrow functor on full anti-involutive morphisms. -/
def terminalArrow : AntiInvolutiveSSet.{u} ⥤ Arrow AntiInvolutiveSSet.{u} where
  obj X := Arrow.mk (terminal.from X)
  map f := Arrow.homMk f (𝟙 _) (terminalIsTerminal.hom_ext _ _)

/-- The full anti-involutive replacement functor retains all reversal and naturality data. -/
def replacement : AntiInvolutiveSSet.{u} ⥤ AntiInvolutiveSSet.{u} :=
  terminalArrow ⋙ factorization.Z

def unit : 𝟭 AntiInvolutiveSSet.{u} ⟶ replacement.{u} where
  app X := factorization.i.app (terminalArrow.obj X)
  naturality _X _Y f := factorization.i.naturality (terminalArrow.map f)

/-- Every actual replacement has an underlying native quasi-category. -/
instance replacement_quasicategory (X : AntiInvolutiveSSet.{u}) :
    (replacement.obj X).toSSet.Quasicategory := by
  have hT := Limits.IsTerminal.isTerminalObj antiForget _ terminalIsTerminal
  exact (quasicategory_iff_inner_terminal
    (factorization.p.app (terminalArrow.obj X)).hom hT).2
      ((innerFibrations_iff_underlying _).1 (factorization.hp _))

/-- The original anti-involutive unit is in the entire actual inner-left class. -/
theorem unit_innerAnodyne (X : AntiInvolutiveSSet.{u}) : innerAnodyne (unit.app X) :=
  factorization.hi _

/-- The original anti-involutive unit is normal in every degree. -/
theorem unit_normal (X : AntiInvolutiveSSet.{u}) : AntiInvolutiveSSet.NormalMono (unit.app X) :=
  innerAnodyne_le_normal _ (unit_innerAnodyne X)

/-- The actual free functor preserves the full native inner-left class. -/
theorem freeAnti_map_innerAnodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : DaggerNativeInnerHornFactorization.innerAnodyne i) :
    innerAnodyne (freeAnti.map i) := by
  intro X Y p hp
  exact (freeAntiAdjunction.hasLiftingProperty_iff i p).2
    (hi p.hom ((innerFibrations_iff_underlying p).1 hp))

end
end DaggerActualAntiInnerHornFactorization
