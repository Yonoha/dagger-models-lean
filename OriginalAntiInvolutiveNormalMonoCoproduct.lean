import OriginalAntiInvolutiveNormalMonoTransfinite
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Coproduct stability of actual anti-involutive normal monomorphisms

The existing dagger coproduct argument supplies degreewise disjoint-union
colimit calculations. Here the exact normality condition includes degree
zero and no fixed-vertex axiom is imposed. This is a closure input for the
literal freeAnti boundary generators, not an assumed DCH model structure.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.OriginalAntiInvolutiveNormalMonoCoproduct

open DaggerModels.AntiInvolutiveSSet
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalAntiInvolutiveNormalMonoClosure
open DaggerModels.OriginalAntiInvolutiveNormalMonoPushout

/-- A coproduct cocone becomes a coproduct of types in every simplicial degree. -/
noncomputable def isColimit_cofan_hom_app {I : Type u} {X : I → AntiInvolutiveSSet.{u}}
    {P : AntiInvolutiveSSet.{u}} (j : ∀ i, X i ⟶ P) (hj : IsColimit (Cofan.mk P j))
    (n : SimplexCategoryᵒᵖ) :
    IsColimit (Cofan.mk (P.toSSet.obj n) (fun i ↦ (j i).hom.app n)) := by
  let : PreservesColimits antiForget.{u} := antiForget_preservesColimits
  let ev : SSet.{u} ⥤ Type u := (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  let : PreservesColimitsOfShape (Discrete I) ev := evaluation_preservesColimitsOfShape n
  exact isColimitCofanMkObjOfIsColimit (antiForget ⋙ ev) X j hj

/-- A map between arbitrary coproducts of all-degree normal maps is normal. -/
theorem NormalMono.of_coproduct {I : Type u} {X Y : I → AntiInvolutiveSSet.{u}}
    {P Q : AntiInvolutiveSSet.{u}} (j : ∀ i, X i ⟶ P) (k : ∀ i, Y i ⟶ Q)
    (hj : IsColimit (Cofan.mk P j)) (hk : IsColimit (Cofan.mk Q k))
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, NormalMono (f i))
    (g : P ⟶ Q) (h : ∀ i, j i ≫ g = f i ≫ k i) : NormalMono g := by
  have hgn : ∀ n, Function.Injective (g.hom.app n) := by
    intro n x₁ x₂ he
    obtain ⟨i₁, a₁, rfl⟩ :=
      Cofan.inj_jointly_surjective_of_isColimit (isColimit_cofan_hom_app j hj n) x₁
    obtain ⟨i₂, a₂, rfl⟩ :=
      Cofan.inj_jointly_surjective_of_isColimit (isColimit_cofan_hom_app j hj n) x₂
    have he' : (k i₁).hom.app n ((f i₁).hom.app n a₁) =
        (k i₂).hom.app n ((f i₂).hom.app n a₂) := by
      calc
        _ = g.hom.app n ((j i₁).hom.app n a₁) :=
          (congrArg (fun t : X i₁ ⟶ Q ↦ t.hom.app n a₁) (h i₁)).symm
        _ = g.hom.app n ((j i₂).hom.app n a₂) := he
        _ = _ := congrArg (fun t : X i₂ ⟶ Q ↦ t.hom.app n a₂) (h i₂)
    obtain rfl := Cofan.eq_of_inj_apply_eq_of_isColimit
      (isColimit_cofan_hom_app k hk n) _ _ he'
    have ha := Cofan.inj_injective_of_isColimit (isColimit_cofan_hom_app k hk n) i₁ he'
    let : Mono (f i₁).hom := (hf i₁).1
    obtain rfl := (CategoryTheory.mono_iff_injective ((f i₁).hom.app n)).1 inferInstance ha
    rfl
  have hgm : Mono g.hom := by
    rw [NatTrans.mono_iff_mono_app]
    exact fun n ↦ (CategoryTheory.mono_iff_injective _).2 (hgn n)
  refine ⟨hgm, ?_⟩
  intro n x hx hnew hfix
  obtain ⟨i, y, hy⟩ :=
    Cofan.inj_jointly_surjective_of_isColimit (isColimit_cofan_hom_app k hk (op ⦋n⦌)) x
  have hynd : y ∈ (Y i).toSSet.nonDegenerate n := by
    rw [SSet.mem_nonDegenerate_iff_notMem_degenerate]
    intro hydeg
    have hdeg := SSet.degenerate_app_apply hydeg (k i).hom
    rw [show (k i).hom.app (op ⦋n⦌) y = x from hy] at hdeg
    exact (SSet.mem_nonDegenerate_iff_notMem_degenerate Q.toSSet x).1 hx hdeg
  have hynew : y ∉ Set.range ((f i).hom.app (op ⦋n⦌)) := by
    rintro ⟨a, rfl⟩
    apply hnew
    refine ⟨(j i).hom.app (op ⦋n⦌) a, ?_⟩
    exact (congrArg (fun t : X i ⟶ Q ↦ t.hom.app (op ⦋n⦌) a) (h i)).trans hy
  apply (hf i).2 n y hynd hynew
  apply Cofan.inj_injective_of_isColimit (isColimit_cofan_hom_app k hk (op ⦋n⦌)) i
  exact ((k i).dagger_comm y).trans ((congrArg Q.daggerSimplex hy).trans (hfix.trans hy.symm))

/-- The canonical coproduct of any small family of normal maps is normal. -/
theorem NormalMono.sigma_map {I : Type u} {X Y : I → AntiInvolutiveSSet.{u}}
    [HasCoproduct X] [HasCoproduct Y] (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, NormalMono (f i)) : NormalMono (Limits.Sigma.map f) :=
  NormalMono.of_coproduct (Sigma.ι X) (Sigma.ι Y)
    (coproductIsCoproduct X) (coproductIsCoproduct Y) f hf (Limits.Sigma.map f) (Sigma.ι_map f)

end DaggerModels.OriginalAntiInvolutiveNormalMonoCoproduct
