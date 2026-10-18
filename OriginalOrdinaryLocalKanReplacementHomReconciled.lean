import OriginalOrdinaryHornLeftClassAnodyneReconciled
import OriginalOrdinaryLocalKanReplacement

/-!
# Original Hom maps of the chosen ordinary local Kan replacement unit

The already chosen natural unit is in the literal horn left class. Its
original Hom maps are therefore anodyne, monic, and geometrically weakly
equivalent. The previously proved object bijection and local Kan output are
retained on their actual source and target object types.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels

universe u

namespace DaggerModels.OriginalOrdinaryLocalKanReplacementHom

open OriginalOrdinaryLocalKanReplacement

noncomputable section

/-- Every original Hom map of the chosen unit is anodyne. -/
theorem unit_hom_anodyne (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    SSet.anodyneExtensions ((unit.app C).map x y) :=
  OriginalOrdinaryHornLeftClassAnodyne.hornLeft_hom_anodyne
    (unit.app C) (unit_left C) x y

/-- Every original Hom map of the chosen unit is a monomorphism. -/
theorem unit_hom_mono (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    Mono ((unit.app C).map x y) :=
  OriginalOrdinaryHornLeftClassAnodyne.hornLeft_hom_mono
    (unit.app C) (unit_left C) x y

/-- Every original Hom map of the chosen unit has the exact geometric predicate. -/
theorem unit_hom_geometric (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map ((unit.app C).map x y))) :=
  OriginalOrdinaryHornLeftClassAnodyne.hornLeft_hom_geometric
    (unit.app C) (unit_left C) x y

/-- The original unit and output retain all five stated properties. -/
theorem unit_and_replacement_properties (C : SimplicialCat.{u, u}) :
    Function.Bijective (unit.app C).obj ∧
      (∀ x y : C.Obj, SSet.anodyneExtensions ((unit.app C).map x y)) ∧
      (∀ x y : C.Obj, Mono ((unit.app C).map x y)) ∧
      (∀ x y : C.Obj,
        SSet.KanComplex.W
          (TopCat.toSSet.map (SSet.toTop.map ((unit.app C).map x y)))) ∧
      (∀ x y : (replacement.obj C).Obj, SSet.KanComplex (x ⟶[SSet.{u}] y)) :=
  ⟨unit_obj_bijective C, unit_hom_anodyne C, unit_hom_mono C,
    unit_hom_geometric C, replacement_locallyKan C⟩

end

end DaggerModels.OriginalOrdinaryLocalKanReplacementHom
