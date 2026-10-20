import Mathlib.CategoryTheory.Action.Basic

/-!
# Recover underlying colimits from colimits of trivial commutative actions

For a commutative monoid, each action operator is itself an equivariant endomorphism.
The universal property forces every operator on a colimit of trivial actions to be the identity.
Its underlying object therefore has the full original colimit universal property.
No colimits in the underlying category are assumed.
-/

set_option autoImplicit false
open CategoryTheory Limits
universe u v w a b
namespace DaggerOriginalCommutativeActionColimits
noncomputable section
variable {C : Type u} [Category.{v} C] {M : Type w} [CommMonoid M]
variable {J : Type a} [Category.{b} J]

/-- Give every original object and arrow the identity action. -/
def trivialFunctor (C : Type u) [Category.{v} C] (M : Type w) [CommMonoid M] :
    C ⥤ Action C M where
  obj := Action.trivial M
  map F := ⟨F, by intro g; simp [Action.trivial]⟩

/-- Commutativity makes each actual action operator an equivariant endomorphism. -/
def centralEnd (A : Action C M) (g : M) : A ⟶ A where
  hom := A.ρ g
  comm h := by
    change A.ρ g * A.ρ h = A.ρ h * A.ρ g
    rw [← A.ρ.map_mul, ← A.ρ.map_mul, mul_comm]

/-- Every action operator on the actual colimit of trivial actions is the identity. -/
theorem actionColimit_trivial (K : J ⥤ C) [HasColimit (K ⋙ trivialFunctor C M)] (g : M) :
    (colimit (K ⋙ trivialFunctor C M)).ρ g = 𝟙 _ := by
  have h : centralEnd (colimit (K ⋙ trivialFunctor C M)) g = 𝟙 _ := by
    apply colimit.hom_ext
    intro j
    apply Action.Hom.ext
    change (colimit.ι (K ⋙ trivialFunctor C M) j).hom ≫
      (colimit (K ⋙ trivialFunctor C M)).ρ g =
        (colimit.ι (K ⋙ trivialFunctor C M) j).hom ≫ 𝟙 _
    have hc := (colimit.ι (K ⋙ trivialFunctor C M) j).comm g
    change 𝟙 _ ≫ (colimit.ι (K ⋙ trivialFunctor C M) j).hom =
      (colimit.ι (K ⋙ trivialFunctor C M) j).hom ≫
        (colimit (K ⋙ trivialFunctor C M)).ρ g at hc
    simpa only [Category.id_comp, Category.comp_id] using hc.symm
  exact congrArg (fun F ↦ F.hom) h

/-- Lift the whole original cocone to the trivial-action diagram. -/
def liftedCocone (K : J ⥤ C) (s : Cocone K) : Cocone (K ⋙ trivialFunctor C M) where
  pt := Action.trivial M s.pt
  ι :=
    { app j := ⟨s.ι.app j, by intro g; simp [trivialFunctor, Action.trivial]⟩
      naturality i j f := by
        apply Action.Hom.ext
        exact s.ι.naturality f }

/-- Keep the original diagram arrows and the underlying colimit legs unchanged. -/
def underlyingCocone (K : J ⥤ C) [HasColimit (K ⋙ trivialFunctor C M)] : Cocone K where
  pt := (colimit (K ⋙ trivialFunctor C M)).V
  ι :=
    { app j := (colimit.ι (K ⋙ trivialFunctor C M) j).hom
      naturality i j f := by
        have h := congrArg (fun F ↦ F.hom) (colimit.w (K ⋙ trivialFunctor C M) f)
        change K.map f ≫ (colimit.ι (K ⋙ trivialFunctor C M) j).hom =
          (colimit.ι (K ⋙ trivialFunctor C M) i).hom at h
        exact h.trans (Category.comp_id _).symm }

/-- The underlying cocone satisfies existence, every original leg, and uniqueness. -/
def underlyingIsColimit (K : J ⥤ C) [HasColimit (K ⋙ trivialFunctor C M)] :
    IsColimit (underlyingCocone (M := M) K) where
  desc s := (colimit.desc (K ⋙ trivialFunctor C M) (liftedCocone K s)).hom
  fac s j := congrArg (fun F ↦ F.hom)
    (colimit.ι_desc (liftedCocone (M := M) K s) j)
  uniq s F h := by
    let F' : colimit (K ⋙ trivialFunctor C M) ⟶ Action.trivial M s.pt :=
      ⟨F, by
        intro g
        change (colimit (K ⋙ trivialFunctor C M)).ρ g ≫ F = F ≫ 𝟙 _
        rw [actionColimit_trivial, Category.id_comp, Category.comp_id]⟩
    have he : F' = colimit.desc (K ⋙ trivialFunctor C M) (liftedCocone K s) := by
      apply colimit.hom_ext
      intro j
      apply Action.Hom.ext
      change (colimit.ι (K ⋙ trivialFunctor C M) j).hom ≫ F = _
      have hj := h j
      change (colimit.ι (K ⋙ trivialFunctor C M) j).hom ≫ F = s.ι.app j at hj
      rw [hj]
      exact (congrArg (fun G ↦ G.hom)
        (colimit.ι_desc (liftedCocone (M := M) K s) j)).symm
    exact congrArg (fun G ↦ G.hom) he

/-- Actual colimits of trivial actions suffice for the corresponding underlying colimit. -/
theorem hasColimit_of_action (K : J ⥤ C) [HasColimit (K ⋙ trivialFunctor C M)] :
    HasColimit K := ⟨⟨underlyingCocone (M := M) K, underlyingIsColimit (M := M) K⟩⟩

/-- Recover all colimits of the same size from the commutative-action category. -/
theorem hasColimits_of_action [HasColimitsOfSize.{b, a} (Action C M)] :
    HasColimitsOfSize.{b, a} C where
  has_colimits_of_shape J _categoryJ :=
    ⟨fun (K : J ⥤ C) ↦ hasColimit_of_action (M := M) K⟩

end
end DaggerOriginalCommutativeActionColimits
