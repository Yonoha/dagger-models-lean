import TerminalArrowConnectedColimits
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits

/-! Original arrow endpoints retain their presentability rank through actual adjunctions. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerTerminalArrowConnectedColimits
universe u v w
namespace DaggerArrowEndpointPresentability
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
variable (C : Type w) [Category.{v} C]

def identityArrow : C ⥤ Arrow C where
  obj X := Arrow.mk (𝟙 X)
  map f := Arrow.homMk f f (by simp)

def identityToLeft : identityArrow C ⊣ Arrow.leftFunc :=
  Adjunction.mkOfUnitCounit
    { unit := 𝟙 _
      counit :=
        { app A := Arrow.homMk (𝟙 A.left) A.hom (by change 𝟙 _ ≫ _ = 𝟙 _ ≫ _; rfl)
          naturality := by
            intro A B f
            apply Arrow.hom_ext
            · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left
              simp
            · change f.left ≫ B.hom = A.hom ≫ f.right
              exact Arrow.w f }
      left_triangle := by
        apply NatTrans.ext
        funext X
        apply Arrow.hom_ext <;> change 𝟙 X ≫ 𝟙 X ≫ 𝟙 X = 𝟙 X <;> simp
      right_triangle := by
        apply NatTrans.ext
        funext X
        change 𝟙 X.left ≫ 𝟙 X.left ≫ 𝟙 X.left = 𝟙 X.left
        simp }

def rightToIdentity : Arrow.rightFunc ⊣ identityArrow C :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app A := Arrow.homMk A.hom (𝟙 A.right) (by change _ ≫ 𝟙 _ = _ ≫ 𝟙 _; rfl)
          naturality := by
            intro A B f
            apply Arrow.hom_ext
            · change f.left ≫ B.hom = A.hom ≫ f.right
              exact Arrow.w f
            · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right
              simp }
      counit := 𝟙 _
      left_triangle := by
        apply NatTrans.ext
        funext X
        change 𝟙 X.right ≫ 𝟙 X.right ≫ 𝟙 X.right = 𝟙 X.right
        simp
      right_triangle := by
        apply NatTrans.ext
        funext X
        apply Arrow.hom_ext <;> change 𝟙 X ≫ 𝟙 X ≫ 𝟙 X = 𝟙 X <;> simp }

instance identityLeftAdjoint : (identityArrow C).IsLeftAdjoint :=
  (identityToLeft C).isLeftAdjoint

theorem right_presentable (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (A : Arrow C) [IsCardinalPresentable A κ] : IsCardinalPresentable A.right κ := by
  have : (identityArrow C).IsCardinalAccessible κ := inferInstance
  exact (rightToIdentity C).isCardinalPresentable_leftAdjoint_obj κ A

variable [HasTerminal C]

def leftToTerminal : Arrow.leftFunc ⊣ toTerminalArrow C :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app A := Arrow.homMk (𝟙 A.left) (terminal.from A.right)
            (terminalIsTerminal.hom_ext _ _)
          naturality := by
            intro A B f
            apply Arrow.hom_ext
            · simp [toTerminalArrow]
            · exact terminalIsTerminal.hom_ext _ _ }
      counit := 𝟙 _
      left_triangle := by
        apply NatTrans.ext
        funext X
        change 𝟙 X.left ≫ 𝟙 X.left ≫ 𝟙 X.left = 𝟙 X.left
        simp
      right_triangle := by
        apply NatTrans.ext
        funext X
        apply Arrow.hom_ext
        · change 𝟙 X ≫ 𝟙 X ≫ 𝟙 X = 𝟙 X
          simp
        · exact terminalIsTerminal.hom_ext _ _ }

theorem left_presentable [HasColimitsOfSize.{u, u} C] (κ : Cardinal.{u})
    [hκ : Fact κ.IsRegular] (A : Arrow C) [IsCardinalPresentable A κ] :
    IsCardinalPresentable A.left κ := by
  have : (toTerminalArrow C).IsCardinalAccessible κ :=
    (toTerminalArrow C).isCardinalAccessible_of_le (κ := Cardinal.aleph0.{u}) hκ.out.aleph0_le
  exact (leftToTerminal C).isCardinalPresentable_leftAdjoint_obj κ A

end
end DaggerArrowEndpointPresentability
