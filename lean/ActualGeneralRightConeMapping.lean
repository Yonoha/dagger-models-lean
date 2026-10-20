import OriginalCounitRightConeFunctor

/-! Literal original cone mapping spaces for arbitrary simplicial sets, retaining BOTH endpoints. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerModels OrdinaryRigidification
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
universe u
namespace DaggerActualGeneralRightConeMapping
noncomputable section

theorem alpha_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    (coneMap.{u} f).app (op ⦋0⦌) (alpha.{u} m.len) = alpha.{u} n.len := by
  have h := congrArg (fun g : (Δ[0] : SSet.{u}) ⟶ cone.{u} n.len ↦
    g.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (alphaMap_naturality f)
  simpa only [alpha, NatTrans.comp_app, types_comp_apply] using h

theorem omega_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    (coneMap.{u} f).app (op ⦋0⦌) (omega.{u} m.len) = omega.{u} n.len := by
  have h := congrArg (fun g : (Δ[0] : SSet.{u}) ⟶ cone.{u} n.len ↦
    g.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (omegaMap_naturality f)
  simpa only [omega, NatTrans.comp_app, types_comp_apply] using h

def rightMapping (X : SSet.{u})
    (v w : X.obj (op ⦋0⦌)) : SSet.{u} where
  obj q := {σ : cone.{u} q.unop.len ⟶ X //
    σ.app (op ⦋0⦌) (alpha.{u} q.unop.len) = v ∧
      σ.app (op ⦋0⦌) (omega.{u} q.unop.len) = w}
  map {q r} f σ := ⟨coneMap.{u} f.unop ≫ σ.1, by
    constructor
    · calc
        (coneMap.{u} f.unop ≫ σ.1).app (op ⦋0⦌) (alpha.{u} r.unop.len) =
            σ.1.app (op ⦋0⦌)
              ((coneMap.{u} f.unop).app (op ⦋0⦌) (alpha.{u} r.unop.len)) := rfl
        _ = σ.1.app (op ⦋0⦌) (alpha.{u} q.unop.len) :=
          congrArg (σ.1.app (op ⦋0⦌)) (alpha_naturality.{u} f.unop)
        _ = v := σ.2.1
    · calc
        (coneMap.{u} f.unop ≫ σ.1).app (op ⦋0⦌) (omega.{u} r.unop.len) =
            σ.1.app (op ⦋0⦌)
              ((coneMap.{u} f.unop).app (op ⦋0⦌) (omega.{u} r.unop.len)) := rfl
        _ = σ.1.app (op ⦋0⦌) (omega.{u} q.unop.len) :=
          congrArg (σ.1.app (op ⦋0⦌)) (omega_naturality.{u} f.unop)
        _ = w := σ.2.2⟩
  map_id q := by
    funext σ
    apply Subtype.ext
    change coneMap.{u} (𝟙 q.unop) ≫ σ.1 = σ.1
    rw [show coneMap.{u} (𝟙 q.unop) = 𝟙 (cone.{u} q.unop.len) from
      coneFunctor.{u}.map_id q.unop]
    exact Category.id_comp _
  map_comp {q r s} f g := by
    funext σ
    apply Subtype.ext
    change coneMap.{u} (g.unop ≫ f.unop) ≫ σ.1 =
      (coneMap.{u} g.unop ≫ coneMap.{u} f.unop) ≫ σ.1
    exact congrArg (fun h ↦ h ≫ σ.1) (coneFunctor.{u}.map_comp g.unop f.unop)


def map {X Y : SSet.{u}} (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌)) :
    rightMapping X a b ⟶ rightMapping Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) where
  app q s := ⟨s.val ≫ f, by
    constructor
    · exact congrArg (f.app (op ⦋0⦌)) s.property.1
    · exact congrArg (f.app (op ⦋0⦌)) s.property.2⟩
  naturality q r α := by
    funext s
    apply Subtype.ext
    exact Category.assoc _ _ _

theorem map_id (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    map (𝟙 X) a b = 𝟙 (rightMapping X a b) := by
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  exact Category.comp_id s.val

theorem map_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a b : X.obj (op ⦋0⦌)) :
    map (f ≫ g) a b = map f a b ≫ map g (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) := by
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

end
end DaggerActualGeneralRightConeMapping
