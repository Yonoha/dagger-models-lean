import ChosenNecklaceIntervalFactor
import ChosenNecklacesOver
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode

variable (T : NecklaceCode) (a b : Fin (T.len + 1)) (hab : a ≤ b)

/-- The actual cut necklace over the original target, with its specified endpoints. -/
def intervalOver : NecklacesOver (toSSet.{u} T)
    (T.verticesEquiv.symm (ULift.up a)) (T.verticesEquiv.symm (ULift.up b)) where
  code := intervalCode T a b hab
  map := intervalι T a b hab
  first := intervalι_first T a b hab
  last := intervalι_last T a b hab

variable (P : NecklacesOver (toSSet.{u} T)
    (T.verticesEquiv.symm (ULift.up a)) (T.verticesEquiv.symm (ULift.up b)))

theorem over_orderMap_first : orderMap P.map 0 = a := by
  change (T.verticesEquiv (P.map.app _ P.code.first)).down = a
  rw [P.first, T.verticesEquiv.apply_symm_apply]

theorem over_orderMap_last : orderMap P.map (Fin.last P.code.len) = b := by
  change (T.verticesEquiv (P.map.app _ P.code.last)).down = b
  rw [P.last, T.verticesEquiv.apply_symm_apply]

theorem over_vertex_bounds (x : P.code.toSSet.obj (op ⦋0⦌)) :
    a ≤ T.inclusion.app _ (P.map.app _ x) 0 ∧
      T.inclusion.app _ (P.map.app _ x) 0 ≤ b := by
  let v := (P.code.verticesEquiv x).down
  have hl := (orderMap P.map).monotone (Fin.zero_le v)
  have hr := (orderMap P.map).monotone (Fin.le_last v)
  rw [over_orderMap_first T a b P] at hl
  rw [over_orderMap_last T a b P] at hr
  have he : orderMap P.map v = T.inclusion.app _ (P.map.app _ x) 0 := by
    dsimp [v, orderMap, mapVertices]
    rw [P.code.verticesEquiv.symm_apply_apply]
    rfl
  rw [he] at hl hr
  exact ⟨hl, hr⟩

/-- Every original over-target map factors through this same cut, not through all of T. -/
def toInterval : P ⟶ intervalOver.{u} T a b hab where
  hom :=
    { map := intervalFactor T a b hab P.map (over_vertex_bounds T a b P)
      first := by
        apply intervalι_injective T a b hab
        exact (intervalFactorApp_fac T a b hab P.map (over_vertex_bounds T a b P)
          _ P.code.first).trans (P.first.trans (intervalι_first T a b hab).symm)
      last := by
        apply intervalι_injective T a b hab
        exact (intervalFactorApp_fac T a b hab P.map (over_vertex_bounds T a b P)
          _ P.code.last).trans (P.last.trans (intervalι_last T a b hab).symm) }
  w := intervalFactor_fac T a b hab P.map (over_vertex_bounds T a b P)

theorem toInterval_original :
    (toInterval T a b hab P).hom.map ≫ intervalι T a b hab = P.map :=
  (toInterval T a b hab P).w

theorem toInterval_uniq (k : P ⟶ intervalOver.{u} T a b hab) :
    k = toInterval T a b hab P := by
  apply NecklacesOver.Hom.ext
  apply NecklaceCode.Hom.ext
  exact intervalFactor_uniq T a b hab P.map (over_vertex_bounds T a b P) k.hom.map k.w

/-- Full arbitrary-target terminal UP for every ordered pair, including coincident endpoints. -/
def intervalIsTerminal : IsTerminal (intervalOver.{u} T a b hab) :=
  IsTerminal.ofUniqueHom (toInterval T a b hab) (toInterval_uniq T a b hab)

include P in
/-- Reversed endpoints admit no necklace map to the actual original target. -/
theorem over_endpoints_le : a ≤ b := by
  have h := (orderMap P.map).monotone (Fin.zero_le (Fin.last P.code.len))
  rw [over_orderMap_first T a b P, over_orderMap_last T a b P] at h
  exact h

instance reverse_over_isEmpty (h : ¬a ≤ b) :
    IsEmpty (NecklacesOver (toSSet.{u} T)
      (T.verticesEquiv.symm (ULift.up a)) (T.verticesEquiv.symm (ULift.up b))) :=
  ⟨fun P ↦ h (over_endpoints_le T a b P)⟩

end

end DaggerChosenRigidificationNecklace
