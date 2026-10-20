import NativeWalkingTwoSidedMappingEquivalence
import NativeBoundaryCategoricalCylinder

/-!
# The full original categorical cylinder relative to any native subcomplex

The union contains all of S times J and all of X at the zero endpoint.
Both entire J-cylinders are retained, including every original simplex operator.
-/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualWalkingIsoCategoricalCylinder
open DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeBoundaryCategoricalCylinder
open DaggerOriginalNerveProduct
universe u
namespace DaggerNativeWalkingSubcomplexCylinder
noncomputable section

theorem productInverse_obj (q : SimplexCategoryᵒᵖ) (t s : J.{u}.obj q)
    (i : Fin (q.unop.len + 1)) :
    ((nerveProductIso walkingIso walkingIso).inv.app q (t, s)).obj i =
      (t.obj i, s.obj i) := by
  apply Prod.ext
  · exact congrArg (fun F ↦ F.obj i)
      (congrFun (NatTrans.congr_app (nerveProductIso_inv_fst walkingIso walkingIso) q) (t, s))
  · exact congrArg (fun F ↦ F.obj i)
      (congrFun (NatTrans.congr_app (nerveProductIso_inv_snd walkingIso walkingIso) q) (t, s))

theorem cylinder_obj (q : SimplexCategoryᵒᵖ) (t s : J.{u}.obj q)
    (i : Fin (q.unop.len + 1)) :
    (cylinder.app q (t, s)).obj i =
      if (ULift.down (s.obj i)).as then t.obj i else walkingZero := by
  change contractionFunctor.obj
    (((nerveProductIso walkingIso walkingIso).inv.app q (t, s)).obj i) = _
  rw [productInverse_obj]
  rfl

theorem time_obj (q : SimplexCategoryᵒᵖ) (b : Bool) (i : Fin (q.unop.len + 1)) :
    (time.{u} q b).obj i = parameterObject b := rfl

theorem cylinder_zero_left (q : SimplexCategoryᵒᵖ) (t : J.{u}.obj q) :
    cylinder.app q (time q false, t) = time q false := by
  apply CategoryTheory.Functor.ext (fun i ↦ ?_)
  rw [cylinder_obj, time_obj]
  split_ifs <;> rfl

theorem cylinder_zero_right (q : SimplexCategoryᵒᵖ) (t : J.{u}.obj q) :
    cylinder.app q (t, time q false) = time q false := by
  apply CategoryTheory.Functor.ext (fun i ↦ ?_)
  rw [cylinder_obj, time_obj]
  rfl

theorem cylinder_one_right (q : SimplexCategoryᵒᵖ) (t : J.{u}.obj q) :
    cylinder.app q (t, time q true) = t := by
  apply CategoryTheory.Functor.ext (fun i ↦ ?_)
  rw [cylinder_obj, time_obj]
  rfl

def union {X : SSet.{u}} (S : X.Subcomplex) : (X ⊗ J.{u}).Subcomplex where
  obj q := {p | p.1 ∈ S.obj q ∨ p.2 = time q false}
  map {q k} α := by
    intro p hp
    rcases hp with h | h
    · exact Or.inl (S.map α h)
    · exact Or.inr (by
        change J.map α p.2 = time k false
        rw [h, time_map])

def inverse {X : SSet.{u}} (S : X.Subcomplex) : X ⊗ J.{u} ⟶ (union S).toSSet where
  app q p := ⟨(p.1, time q false), Or.inr rfl⟩
  naturality q k α := by
    funext p
    apply Subtype.ext
    exact Prod.ext rfl (time_map α false).symm

def ambientCylinder (X : SSet.{u}) : (X ⊗ J.{u}) ⊗ J.{u} ⟶ X ⊗ J.{u} where
  app q p := (p.1.1, cylinder.app q (p.1.2, p.2))
  naturality q k α := by
    funext p
    exact Prod.ext rfl (congrFun (cylinder.naturality α) (p.1.2, p.2))

def relativeCylinder {X : SSet.{u}} (S : X.Subcomplex) :
    (union S).toSSet ⊗ J.{u} ⟶ (union S).toSSet where
  app q p := ⟨(p.1.val.1, cylinder.app q (p.1.val.2, p.2)), by
    rcases p.1.property with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, cylinder_zero_left])⟩
  naturality q k α := by
    funext p
    apply Subtype.ext
    exact Prod.ext rfl (congrFun (cylinder.naturality α) (p.1.val.2, p.2))

theorem ambient_zero {X : SSet.{u}} (S : X.Subcomplex) :
    intervalEndpoint (X ⊗ J.{u}) false ≫ ambientCylinder X = inverse S ≫ (union S).ι := by
  apply NatTrans.ext
  funext q p
  change (p.1, cylinder.app q (p.2, time q false)) = (p.1, time q false)
  exact Prod.ext rfl (cylinder_zero_right q p.2)

theorem ambient_one (X : SSet.{u}) :
    intervalEndpoint (X ⊗ J.{u}) true ≫ ambientCylinder X = 𝟙 _ := by
  apply NatTrans.ext
  funext q p
  change (p.1, cylinder.app q (p.2, time q true)) = p
  exact Prod.ext rfl (cylinder_one_right q p.2)

theorem relative_zero {X : SSet.{u}} (S : X.Subcomplex) :
    intervalEndpoint (union S).toSSet false ≫ relativeCylinder S = (union S).ι ≫ inverse S := by
  apply NatTrans.ext
  funext q p
  apply Subtype.ext
  change (p.val.1, cylinder.app q (p.val.2, time q false)) = (p.val.1, time q false)
  exact Prod.ext rfl (cylinder_zero_right q p.val.2)

theorem relative_one {X : SSet.{u}} (S : X.Subcomplex) :
    intervalEndpoint (union S).toSSet true ≫ relativeCylinder S = 𝟙 _ := by
  apply NatTrans.ext
  funext q p
  apply Subtype.ext
  change (p.val.1, cylinder.app q (p.val.2, time q true)) = p.val
  exact Prod.ext rfl (cylinder_one_right q p.val.2)

theorem union_inclusion_weak {X : SSet.{u}} (S : X.Subcomplex) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences (union S).ι :=
  DaggerNativeWalkingTwoSidedMappingEquivalence.weak (union S).ι (inverse S)
    (relativeCylinder S) (ambientCylinder X)
    (relative_zero S) (relative_one S) (ambient_zero S) (ambient_one X)

end
end DaggerNativeWalkingSubcomplexCylinder
