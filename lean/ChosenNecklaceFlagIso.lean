import ChosenNecklaceFlagInverse

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode)

theorem necklaceFlagEvaluation_transport
    {x y x' y' : (toSSet.{u} T).obj (op ⦋0⦌)} (hx : x = x') (hy : y = y') :
    eqToHom (show flagHom (toSSet T) x y = flagHom (toSSet T) x' y' by rw [hx, hy]) ≫
        necklaceFlagEvaluation (x := x') (y := y') T =
      necklaceFlagEvaluation (x := x) (y := y) T ≫
        eqToHom (show nerve (JointPath (T.verticesEquiv x) (T.verticesEquiv y)) =
          nerve (JointPath (T.verticesEquiv x') (T.verticesEquiv y')) by rw [hx, hy]) := by
  cases hx
  cases hy
  rfl

theorem necklaceInverseHomIso_hom_transport
    (x y : (toSSet.{u} T).obj (op ⦋0⦌)) :
    (necklaceInverseHomIso T ⟨T.verticesEquiv x⟩ ⟨T.verticesEquiv y⟩).hom =
      eqToHom (show flagHom (toSSet T) (T.verticesEquiv.symm (T.verticesEquiv x))
        (T.verticesEquiv.symm (T.verticesEquiv y)) = flagHom (toSSet T) x y by
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]) ≫
        necklaceFlagEvaluation T :=
  (necklaceFlagEvaluation_transport T (T.verticesEquiv.symm_apply_apply x)
    (T.verticesEquiv.symm_apply_apply y)).symm

theorem necklaceFlagInverse_forward : necklaceFlagInverse.{u} T ≫ necklaceFlagFunctor T =
    𝟙 (NC.{u} T) := by
  have ho : ∀ a : (NC.{u} T).Obj,
      (necklaceFlagInverse T ≫ necklaceFlagFunctor T).obj a = a :=
    fun a ↦ congrArg NecklaceThickening.mk (T.verticesEquiv.apply_symm_apply a.as)
  apply EnrichedFunctor.ext SSet ho
  intro a b
  change (necklaceInverseHomIso T a b).inv ≫ (necklaceInverseHomIso T a b).hom = 𝟙 _
  exact Iso.inv_hom_id _

theorem necklaceFlagFunctor_inverse : necklaceFlagFunctor.{u} T ≫ necklaceFlagInverse T =
    𝟙 (E (toSSet.{u} T)) := by
  have ho : ∀ x : (E (toSSet.{u} T)).Obj,
      (necklaceFlagFunctor T ≫ necklaceFlagInverse T).obj x = x :=
    fun x ↦ T.verticesEquiv.symm_apply_apply x
  apply EnrichedFunctor.ext SSet ho
  intro x y
  apply (cancel_mono (necklaceFlagEvaluation (x := x) (y := y) T)).mp
  change (necklaceFlagEvaluation T ≫
      (necklaceInverseHomIso T ⟨T.verticesEquiv x⟩ ⟨T.verticesEquiv y⟩).inv ≫
      eqToHom (show flagHom (toSSet T) (T.verticesEquiv.symm (T.verticesEquiv x))
        (T.verticesEquiv.symm (T.verticesEquiv y)) = flagHom (toSSet T) x y by
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply])) ≫ necklaceFlagEvaluation T =
      𝟙 _ ≫ necklaceFlagEvaluation T
  rw [Category.assoc, Category.assoc, ← necklaceInverseHomIso_hom_transport,
    Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- Whole enriched iso, on every endpoint and every map, before any comparison with chosen C. -/
def necklaceFlagIso : E (toSSet.{u} T) ≅ NC.{u} T where
  hom := necklaceFlagFunctor T
  inv := necklaceFlagInverse T
  hom_inv_id := necklaceFlagFunctor_inverse T
  inv_hom_id := necklaceFlagInverse_forward T

end

end DaggerChosenRigidificationNecklace
