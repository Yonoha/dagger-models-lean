import NativeInnerPushoutIhom
import NativeInnerJoyalMappingWeak

/-!
# Actual functor quasi-categories and exact internal-Hom inner fibrations

Use the proved whole inner pushout-product theorem. The initial-parameter pullback is
constructed explicitly at the existing pin; its projection is exactly the native ihom map.
The terminal-parameter pullback retains native precomposition exactly. No quasi-category
internal-Hom closure or ordinary Joyal model is assumed as an additional hypothesis.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed Simplicial
open DaggerNativeInnerHornFactorization DaggerNativeInnerPushoutIhom
open DaggerNativeInnerJoyalMappingWeak
universe u
namespace DaggerNativeIhomQuasicategories
noncomputable section

/-- The original empty parameter tensored with any object is still initial. -/
def initialTensor (X : SSet.{u}) : IsInitial ((⊥_ SSet.{u}) ⊗ X) :=
  IsInitial.isInitialObj (tensorRight X) _ initialIsInitial

/-- The original internal Hom out of the empty parameter is terminal for every target. -/
def initialIhom (Z : SSet.{u}) : IsTerminal ((ihom (⊥_ SSet.{u})).obj Z) := by
  letI (X : SSet.{u}) : Unique (X ⟶ (ihom (⊥_ SSet.{u})).obj Z) :=
    { default := MonoidalClosed.curry ((initialTensor X).to Z)
      uniq f := by
        apply MonoidalClosed.uncurry_injective
        exact (initialTensor X).hom_ext _ _ }
  exact IsTerminal.ofUnique _

/-- The full initial-parameter pullback on the actual native internal Hom. -/
def initialPullback (A : SSet.{u}) {E B : SSet.{u}} (p : E ⟶ B) :
    SSet.PullbackIhom (initial.to A) p where
  pt := (ihom A).obj B
  fst := (initialIhom E).from _
  snd := 𝟙 _
  isPullback := by
    haveI : IsIso ((MonoidalClosed.internalHom.obj (op (⊥_ SSet.{u}))).map p) :=
      isIso_of_isTerminal (initialIhom E) (initialIhom B) _
    exact IsPullback.of_vert_isIso ⟨(initialIhom B).hom_ext _ _⟩

/-- The whole pullback projection is exactly the actual ihom functor's map. -/
theorem initialPullback_π (A : SSet.{u}) {E B : SSet.{u}} (p : E ⟶ B) :
    (initialPullback A p).π = (ihom A).map p := by
  simpa only [initialPullback, Category.comp_id] using (initialPullback A p).π_snd

/-- Native internal Hom by any original parameter preserves the whole inner-right class. -/
theorem ihom_map_inner (A : SSet.{u}) {E B : SSet.{u}} (p : E ⟶ B)
    (hp : innerFibrations p) : innerFibrations ((ihom A).map p) := by
  haveI : Mono (initial.to A) := inferInstance
  have h := pullback_inner hp (initialPullback A p)
  simpa only [initialPullback_π] using h

/-- Every full native functor simplicial set into a quasi-category is a quasi-category. -/
theorem ihom_quasicategory (A Z : SSet.{u}) [Z.Quasicategory] :
    ((ihom A).obj Z).Quasicategory := by
  have hp : innerFibrations (terminal.from Z) :=
    (quasicategory_iff_inner_terminal _ terminalIsTerminal).1 inferInstance
  exact (quasicategory_iff_inner_terminal ((ihom A).map (terminal.from Z))
    (ihomTerminal A)).2 (ihom_map_inner A _ hp)

/-- Actual restriction along any mono into a quasi-category is an inner-right map. -/
theorem pre_mono_inner {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (Z : SSet.{u})
    [Z.Quasicategory] : innerFibrations ((MonoidalClosed.pre i).app Z) := by
  have hp : innerFibrations (terminal.from Z) :=
    (quasicategory_iff_inner_terminal _ terminalIsTerminal).1 inferInstance
  have h := pullback_inner hp (terminalPullback i Z)
  simpa only [terminalPullback_π] using h

end
end DaggerNativeIhomQuasicategories
