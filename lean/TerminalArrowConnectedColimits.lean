import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Connected colimits and finite accessibility of the terminal-arrow functor

Use Mathlib's componentwise comma colimit and the colimit of a constant
connected diagram. The terminal object in the codomain is kept fixed.
-/
set_option autoImplicit false
open CategoryTheory Limits
universe w v u
namespace DaggerTerminalArrowConnectedColimits
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
variable (C : Type u) [Category.{v} C] [HasTerminal C]

def toTerminalArrow : C ⥤ Arrow C where
  obj X := Arrow.mk (terminal.from X)
  map f := Arrow.homMk f (𝟙 _) (terminalIsTerminal.hom_ext _ _)

def mapCoconeIsColimit {J : Type w} [SmallCategory J] [IsConnected J]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((toTerminalArrow C).mapCocone c) := by
  let G := F ⋙ toTerminalArrow C
  let c₂ : Cocone (G ⋙ Comma.snd (𝟭 C) (𝟭 C)) := constCocone J (⊤_ C)
  let c' := Comma.coconeOfPreserves G hc c₂
  have hc' : IsColimit c' :=
    Comma.coconeOfPreservesIsColimit G hc (isColimitConstCocone J (⊤_ C))
  apply IsColimit.ofIsoColimit hc'
  refine Cocones.ext
    (Arrow.isoMk (Iso.refl c.pt) (Iso.refl (⊤_ C)) (terminalIsTerminal.hom_ext _ _)) ?_
  intro j
  apply Arrow.hom_ext
  · simp [c', Comma.coconeOfPreserves, toTerminalArrow]
  · simp [c', Comma.coconeOfPreserves, c₂, toTerminalArrow]

instance preservesConnected [HasColimitsOfSize.{w, w} C]
    (J : Type w) [SmallCategory J] [IsConnected J] :
    PreservesColimitsOfShape J (toTerminalArrow C) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (colimit.isColimit F) (mapCoconeIsColimit C (colimit.isColimit F))

instance finitelyAccessible [HasColimitsOfSize.{w, w} C] :
    (toTerminalArrow C).IsCardinalAccessible Cardinal.aleph0.{w} where
  preservesColimitOfShape J _ _ := by
    have : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0.{w}
    have : IsConnected J := IsFiltered.isConnected J
    infer_instance

end
end DaggerTerminalArrowConnectedColimits
