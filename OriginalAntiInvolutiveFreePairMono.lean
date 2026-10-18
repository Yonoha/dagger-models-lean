import OriginalAntiInvolutiveFreePair
import OriginalAntiInvolutiveNormalMonoClosure
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Monicity and normality of literal free anti-involutive maps

The concrete two-copy presentation makes the free action visible in every
degree. Transport through uniqueness of the left adjoint identifies these
facts with the original tagged left Kan extension `freeAnti`.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels.OriginalAntiInvolutiveFreePairMono

open DaggerModels.AntiInvolutiveSSet
open DaggerModels.OriginalAntiInvolutiveFreePair
open DaggerModels.OriginalAntiInvolutiveNormalMonoClosure
open DaggerModels.OriginalTaggedReverseFreeCompletion

/-- A pair map is monic when its ordinary simplex map is monic. -/
theorem pairMap_mono {A B : SSet.{u}} (f : A ⟶ B) [Mono f] :
    Mono (pairMap f) := by
  apply (mono_iff_mono_hom (pairMap f)).2
  apply (NatTrans.mono_iff_mono_app _).2
  intro n
  apply (CategoryTheory.mono_iff_injective _).2
  have hi : Function.Injective (f.app n) :=
    (CategoryTheory.mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app f).1 inferInstance n)
  intro p q hpq
  change (f.app n p.1, p.2) = (f.app n q.1, q.2) at hpq
  have ha : f.app n p.1 = f.app n q.1 :=
    congrArg (fun z : B.obj n × Bool ↦ z.1) hpq
  have hb : p.2 = q.2 :=
    congrArg (fun z : B.obj n × Bool ↦ z.2) hpq
  exact Prod.ext (hi ha) hb

/-- The explicit free pair has no fixed simplices in any degree. -/
theorem pairMap_normal {A B : SSet.{u}} (f : A ⟶ B) [Mono f] :
    NormalMono (pairMap f) := by
  refine ⟨(mono_iff_mono_hom (pairMap f)).1 (pairMap_mono f), ?_⟩
  intro n x _ _ hfix
  rcases x with ⟨a, b⟩
  cases b <;> cases hfix

/-- The literal tagged free functor takes ordinary monomorphisms to monomorphisms. -/
theorem freeAnti_map_mono {A B : SSet.{u}} (f : A ⟶ B) [Mono f] :
    Mono (freeAnti.map f) := by
  let e := Arrow.isoOfNatIso pairIsoFreeAnti (Arrow.mk f)
  exact ((MorphismProperty.monomorphisms AntiInvolutiveSSet.{u}).arrow_mk_iso_iff e).1
    (pairMap_mono f)

/-- The literal tagged free functor takes ordinary monomorphisms to normal maps. -/
theorem freeAnti_map_normal {A B : SSet.{u}} (f : A ⟶ B) [Mono f] :
    NormalMono (freeAnti.map f) := by
  let e := Arrow.isoOfNatIso pairIsoFreeAnti (Arrow.mk f)
  exact NormalMono.of_retract (CategoryTheory.Retract.ofIso e.symm)
    (pairMap_normal f)

end DaggerModels.OriginalAntiInvolutiveFreePairMono
