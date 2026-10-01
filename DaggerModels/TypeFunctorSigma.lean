import DaggerModels.DaggerGraphPresentable
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Indexed sums of Type-valued accessible functors

The literal indexed sum preserves every small colimit shape preserved by all
summands. In particular, a sum of finitely accessible functors is finitely
accessible.
-/

open CategoryTheory Limits

universe u i v w

namespace DaggerModels.TypeFunctorSigma

variable {C : Type v} [Category.{w} C] {ι : Type i} (F : ι → C ⥤ Type (max u i))

def functor : C ⥤ Type (max u i) where
  obj X := Σ j, (F j).obj X
  map f e := ⟨e.1, (F e.1).map f e.2⟩
  map_id X := by funext e; simp
  map_comp f g := by funext e; simp

def family : C ⥤ Discrete ι ⥤ Type (max u i) where
  obj X := Discrete.functor (fun j ↦ (F j).obj X)
  map f := Discrete.natTrans (fun j ↦ (F j.as).map f)
  map_id X := by ext j x; simp [Discrete.natTrans]
  map_comp f g := by ext j x; simp [Discrete.natTrans]

noncomputable def colimitIso : family F ⋙ colim ≅ functor F :=
  NatIso.ofComponents (fun X ↦ Types.coproductIso (fun j ↦ (F j).obj X)) (by
    intro X Y f
    apply colimit.hom_ext
    intro j
    change colimit.ι _ j ≫ colim.map _ ≫ _ = colimit.ι _ j ≫ _ ≫ _
    rw [colimit.ι_map_assoc]
    change (F j.as).map f ≫ Sigma.ι (fun j ↦ (F j).obj Y) j.as ≫
        (Types.coproductIso _).hom =
      Sigma.ι (fun j ↦ (F j).obj X) j.as ≫ (Types.coproductIso _).hom ≫ _
    rw [Types.coproductIso_ι_comp_hom, ← Category.assoc,
      Types.coproductIso_ι_comp_hom]
    rfl)

theorem preservesColimitsOfShape (J : Type (max u i)) [SmallCategory J]
    [∀ j, PreservesColimitsOfShape J (F j)] : PreservesColimitsOfShape J (functor F) := by
  letI : PreservesColimitsOfShape J (family F) :=
    preservesColimitsOfShape_of_evaluation _ _ (fun j ↦ by
      exact inferInstanceAs (PreservesColimitsOfShape J (F j.as)))
  exact preservesColimitsOfShape_of_natIso (colimitIso F)

attribute [local instance] Cardinal.fact_isRegular_aleph0

theorem isCardinalAccessible
    [∀ j, (F j).IsCardinalAccessible Cardinal.aleph0.{max u i}] :
    (functor F).IsCardinalAccessible Cardinal.aleph0.{max u i} where
  preservesColimitOfShape {J _ _} := by
    letI := fun j ↦ Functor.preservesColimitsOfShape_of_isCardinalAccessible
      (F j) Cardinal.aleph0 J
    exact preservesColimitsOfShape F J

end DaggerModels.TypeFunctorSigma
