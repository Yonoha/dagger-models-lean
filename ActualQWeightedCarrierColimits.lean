import ActualQWeightedResolutionFunctor

/-! Colimits of the complete Q-weighted cell coordinates, using native evaluation colimits. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite
open DaggerActualQWeightedResolutionCells DaggerOriginalCounitRightConeQFunctor
universe u
namespace DaggerActualQWeightedCarrierColimits
noncomputable section

/-- This coordinate functor retains the entire degree chain and entire Q parameter. -/
def carrier (q k : SimplexCategoryᵒᵖ) : SSet.{u} ⥤ Type u where
  obj X := FlatCells X q k
  map f := flatMap f q k
  map_id X := by funext x; rcases x with ⟨A, x, t⟩; rfl
  map_comp _ _ := rfl

variable (q k : SimplexCategoryᵒᵖ)
variable {J : Type u} [Category.{u} J] (D : J ⥤ SSet.{u})

/-- Fix a whole chain and Q parameter to obtain an ordinary evaluated cocone. -/
def componentCocone (s : Cocone (D ⋙ carrier q k)) (A : DegreeChain q)
    (t : (QFunctor.{u}.obj (A.obj 0)).obj k) :
    Cocone (D ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj
      (op (A.obj (Fin.last q.unop.len)))) where
  pt := s.pt
  ι :=
    { app j x := s.ι.app j ⟨A, x, t⟩
      naturality {_i _j} f := by
        funext x
        exact congrFun (s.ι.naturality f) ⟨A, x, t⟩ }

/-- Descend each entire chain/parameter component through the existing evaluated colimit. -/
def mapCoconeIsColimit {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((carrier q k).mapCocone c) where
  desc s z :=
    (isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ (Type u)).obj
      (op (z.1.obj (Fin.last q.unop.len)))) hc).desc
        (componentCocone q k D s z.1 z.2.2) z.2.1
  fac s j := by
    funext z
    rcases z with ⟨A, x, t⟩
    exact congrFun
      ((isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ (Type u)).obj
        (op (A.obj (Fin.last q.unop.len)))) hc).fac (componentCocone q k D s A t) j) x
  uniq s m hm := by
    funext z
    rcases z with ⟨A, x, t⟩
    have he := (isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ (Type u)).obj
      (op (A.obj (Fin.last q.unop.len)))) hc).uniq (componentCocone q k D s A t)
        (fun x ↦ m ⟨A, x, t⟩) (by
          intro j
          funext x
          exact congrFun (hm j) ⟨A, x, t⟩)
    exact congrFun he x

/-- Every original diagram has its colimit preserved by the complete coordinate functor. -/
instance carrier_preservesColimit : PreservesColimit D (carrier q k) :=
  preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
    (mapCoconeIsColimit q k D (colimit.isColimit D))

/-- The same preservation holds for all shapes of the original simplicial-set universe. -/
instance carrier_preservesColimits : PreservesColimitsOfSize.{u, u} (carrier.{u} q k) where
  preservesColimitsOfShape := by
    intro J hJ
    constructor
    intro D
    infer_instance

end
end DaggerActualQWeightedCarrierColimits
