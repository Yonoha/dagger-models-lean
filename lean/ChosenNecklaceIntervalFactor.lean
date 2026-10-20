import ChosenNecklaceIntervalPreimage

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode) (a b : Fin (T.len + 1)) (hab : a ≤ b)

theorem intervalι_injective {n : ℕ} :
    Function.Injective ((intervalι.{u} T a b hab).app (op ⦋n⦌)) := by
  intro x y h
  apply necklace_simplex_ext
  intro i
  have hh := congrArg (fun z ↦ T.inclusion.app (op ⦋n⦌) z i) h
  dsimp only at hh
  rw [intervalι_apply, intervalι_apply] at hh
  exact (intervalEmbedding T a b hab).injective hh

theorem intervalι_injective_app (q : SimplexCategoryᵒᵖ) :
    Function.Injective ((intervalι.{u} T a b hab).app q) := by
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  exact intervalι_injective T a b hab

instance intervalι_mono : Mono (intervalι.{u} T a b hab) := by
  letI : ∀ q, Mono ((intervalι.{u} T a b hab).app q) :=
    fun q ↦ (mono_iff_injective _).mpr (intervalι_injective_app T a b hab q)
  exact NatTrans.mono_of_mono_app _

variable {X : SSet.{u}} (f : X ⟶ toSSet.{u} T)
  (hf : ∀ x : X.obj (op ⦋0⦌), a ≤ T.inclusion.app _ (f.app _ x) 0 ∧
    T.inclusion.app _ (f.app _ x) 0 ≤ b)

include hf in
theorem intervalFactor_bounds {n : ℕ} (x : X.obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    a ≤ T.inclusion.app _ (f.app _ x) i ∧ T.inclusion.app _ (f.app _ x) i ≤ b := by
  change a ≤ (f ≫ T.inclusion).app _ x i ∧ (f ≫ T.inclusion).app _ x i ≤ b
  rw [stdSimplex_vertex_naturality (f ≫ T.inclusion) x i]
  exact hf (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x)

def intervalFactorApp (q : SimplexCategoryᵒᵖ) (x : X.obj q) :
    (toSSet.{u} (intervalCode T a b hab)).obj q := by
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  exact intervalLiftSimplex T a b hab (f.app _ x) (intervalFactor_bounds T a b f hf x)

theorem intervalFactorApp_fac (q : SimplexCategoryᵒᵖ) (x : X.obj q) :
    (intervalι T a b hab).app q (intervalFactorApp T a b hab f hf q x) = f.app q x := by
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  exact intervalι_lift _ _ _ _ _ _

/-- The original full map factors uniquely through its actual bounded interval necklace. -/
def intervalFactor : X ⟶ toSSet.{u} (intervalCode T a b hab) where
  app := intervalFactorApp T a b hab f hf
  naturality q k α := by
    funext x
    apply intervalι_injective_app T a b hab k
    change (intervalι T a b hab).app k
        (intervalFactorApp T a b hab f hf k (X.map α x)) =
      (intervalι T a b hab).app k
        ((toSSet (intervalCode T a b hab)).map α (intervalFactorApp T a b hab f hf q x))
    rw [intervalFactorApp_fac]
    calc
      f.app k (X.map α x) = (toSSet T).map α (f.app q x) := congrFun (f.naturality α) x
      _ = (toSSet T).map α
          ((intervalι T a b hab).app q (intervalFactorApp T a b hab f hf q x)) := by
            rw [intervalFactorApp_fac]
      _ = (intervalι T a b hab).app k
          ((toSSet (intervalCode T a b hab)).map α (intervalFactorApp T a b hab f hf q x)) :=
            (congrFun ((intervalι T a b hab).naturality α)
              (intervalFactorApp T a b hab f hf q x)).symm

theorem intervalFactor_fac : intervalFactor T a b hab f hf ≫ intervalι T a b hab = f := by
  ext q x
  exact intervalFactorApp_fac T a b hab f hf q x

theorem intervalFactor_uniq (k : X ⟶ toSSet.{u} (intervalCode T a b hab))
    (hk : k ≫ intervalι T a b hab = f) : k = intervalFactor T a b hab f hf := by
  apply (cancel_mono (intervalι T a b hab)).mp
  exact hk.trans (intervalFactor_fac T a b hab f hf).symm

end

end DaggerChosenRigidificationNecklace.NecklaceCode
