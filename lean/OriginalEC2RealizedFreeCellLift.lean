import OriginalEC2BorelCofibrancy
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Lifts for the realized regular C₂ cells

An equivariant map out of a realized regular cell coproduct is determined by
its identity-indexed component.  The other components are obtained by the
action, so a boundary-cell lift in `TopCat` extends to an equivariant lift.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2FreeCellAction
open DaggerOriginalEC2EquivariantSkeletalPushout
open DaggerOriginalEC2BorelCofibrancy

universe u

namespace DaggerOriginalEC2RealizedFreeCellLift

noncomputable section

private abbrev R : SSet.{u} ⥤ TopCat.{u} := SSet.toTop.{u}
private abbrev F (A : SSet.{u}) : Action TopCat.{u} C2.{u} :=
  (R.{u}.mapAction C2.{u}).obj (freeCellAction A)

private def j (A : SSet.{u}) (g : C2.{u}) : R.{u}.obj A ⟶ (F A).V :=
  R.{u}.map (Sigma.ι (fun (_ : C2.{u}) ↦ A) g)

private def freeCofanColimit (A : SSet.{u}) :
    IsColimit (Cofan.mk (F A).V (j A)) :=
  isColimitOfHasCoproductOfPreservesColimit R.{u} (fun (_ : C2.{u}) ↦ A)

private theorem j_action (A : SSet.{u}) (g h : C2.{u}) :
    j A g ≫ (F A).ρ h = j A (h * g) := by
  change R.{u}.map (Sigma.ι (fun (_ : C2.{u}) ↦ A) g) ≫
      R.{u}.map ((freeCellAction A).ρ h) =
    R.{u}.map (Sigma.ι (fun (_ : C2.{u}) ↦ A) (h * g))
  rw [← R.map_comp, freeCellAction_ι]

private theorem j_map {A B : SSet.{u}} (f : A ⟶ B) (g : C2.{u}) :
    j A g ≫ ((R.{u}.mapAction C2.{u}).map (freeCellMap f)).hom =
      R.{u}.map f ≫ j B g := by
  change R.{u}.map (Sigma.ι (fun (_ : C2.{u}) ↦ A) g) ≫
      R.{u}.map (Limits.Sigma.map (fun (_ : C2.{u}) ↦ f)) =
    R.{u}.map f ≫ R.{u}.map (Sigma.ι (fun (_ : C2.{u}) ↦ B) g)
  rw [← R.map_comp, ← R.map_comp, Limits.Sigma.ι_map]

/-- Extend an identity-component map to the whole realized regular orbit. -/
def extend (A : SSet.{u}) (X : Action TopCat.{u} C2.{u})
    (k : R.{u}.obj A ⟶ X.V) : F A ⟶ X where
  hom := Cofan.IsColimit.desc (freeCofanColimit A) (fun g ↦ k ≫ X.ρ g)
  comm h := by
    apply Cofan.IsColimit.hom_ext (freeCofanColimit A)
    intro g
    change (j A g ≫ (F A).ρ h) ≫
        Cofan.IsColimit.desc (freeCofanColimit A) (fun g ↦ k ≫ X.ρ g) =
      (j A g ≫ Cofan.IsColimit.desc (freeCofanColimit A)
        (fun g ↦ k ≫ X.ρ g)) ≫ X.ρ h
    rw [j_action]
    have hfac (t : C2.{u}) :
        j A t ≫ Cofan.IsColimit.desc (freeCofanColimit A)
          (fun g ↦ k ≫ X.ρ g) = k ≫ X.ρ t :=
      Cofan.IsColimit.fac (freeCofanColimit A) _ t
    rw [hfac (h * g), hfac g]
    change k ≫ X.ρ (h * g) = k ≫ X.ρ g ≫ X.ρ h
    rw [← Category.assoc]
    exact congrArg (fun t : X.V ⟶ X.V ↦ k ≫ t) (X.ρ.map_mul h g)

@[simp]
theorem j_extend (A : SSet.{u}) (X : Action TopCat.{u} C2.{u})
    (k : R.{u}.obj A ⟶ X.V) (g : C2.{u}) :
    j A g ≫ (extend A X k).hom = k ≫ X.ρ g :=
  Cofan.IsColimit.fac (freeCofanColimit A) _ g

/-- An equivariant map out of a regular orbit is fixed by its identity component. -/
theorem hom_ext_of_identity (A : SSet.{u}) (X : Action TopCat.{u} C2.{u})
    (f₁ f₂ : F A ⟶ X) (h : j A 1 ≫ f₁.hom = j A 1 ≫ f₂.hom) :
    f₁ = f₂ := by
  apply Action.Hom.ext
  apply Cofan.IsColimit.hom_ext (freeCofanColimit A)
  intro g
  change j A g ≫ f₁.hom = j A g ≫ f₂.hom
  have hg : j A g = j A 1 ≫ (F A).ρ g := by
    simpa using (j_action A 1 g).symm
  calc
    j A g ≫ f₁.hom = (j A 1 ≫ (F A).ρ g) ≫ f₁.hom :=
      congrArg (fun q ↦ q ≫ f₁.hom) hg
    _ = (j A 1 ≫ f₁.hom) ≫ X.ρ g := by
      rw [Category.assoc, f₁.comm, ← Category.assoc]
    _ = (j A 1 ≫ f₂.hom) ≫ X.ρ g := by rw [h]
    _ = (j A 1 ≫ (F A).ρ g) ≫ f₂.hom := by
      rw [Category.assoc, ← f₂.comm, ← Category.assoc]
    _ = j A g ≫ f₂.hom :=
      (congrArg (fun q ↦ q ≫ f₂.hom) hg).symm

/-- A regular realized cell lifts equivariantly whenever the underlying
boundary inclusion lifts against the underlying right-hand map. -/
theorem realized_freeCellMap_lifts {A B : SSet.{u}} (i : A ⟶ B)
    {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y)
    (hi : HasLiftingProperty (R.{u}.map i) p.hom) :
    HasLiftingProperty ((R.{u}.mapAction C2.{u}).map (freeCellMap i)) p := by
  let φ : F A ⟶ F B := (R.{u}.mapAction C2.{u}).map (freeCellMap i)
  refine ⟨fun {t} {b} sq ↦ ?_⟩
  let a : R.{u}.obj A ⟶ X.V := j A 1 ≫ t.hom
  let d : R.{u}.obj B ⟶ Y.V := j B 1 ≫ b.hom
  have hcomm : a ≫ p.hom = R.{u}.map i ≫ d := by
    calc
      a ≫ p.hom = j A 1 ≫ (t ≫ p).hom := by rfl
      _ = j A 1 ≫ (φ ≫ b).hom := by rw [sq.w]
      _ = R.{u}.map i ≫ d := by
        dsimp [d]
        change (j A 1 ≫ ((R.{u}.mapAction C2.{u}).map (freeCellMap i)).hom) ≫
            b.hom = (R.{u}.map i ≫ j B 1) ≫ b.hom
        rw [j_map]
  let sq₀ : CommSq a (R.{u}.map i) p.hom d := CommSq.mk hcomm
  let k := (hi.sq_hasLift sq₀).exists_lift.some.l
  have hk_left : R.{u}.map i ≫ k = a :=
    (hi.sq_hasLift sq₀).exists_lift.some.fac_left
  have hk_right : k ≫ p.hom = d :=
    (hi.sq_hasLift sq₀).exists_lift.some.fac_right
  refine CommSq.HasLift.mk' {
    l := extend B X k
    fac_left := ?_
    fac_right := ?_
  }
  · apply hom_ext_of_identity A X _ _
    change j A 1 ≫ φ.hom ≫ (extend B X k).hom = j A 1 ≫ t.hom
    rw [← Category.assoc, j_map, Category.assoc, j_extend]
    simpa [Action.ρ_one, a] using hk_left
  · apply hom_ext_of_identity B Y _ _
    change j B 1 ≫ (extend B X k).hom ≫ p.hom = j B 1 ≫ b.hom
    rw [← Category.assoc, j_extend]
    simpa [Action.ρ_one, d] using hk_right

end

end DaggerOriginalEC2RealizedFreeCellLift
