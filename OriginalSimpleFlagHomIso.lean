import OriginalSimpleNecklaceLift
import ChosenFlagHomMaps

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {A X : SSet.{u}} (j : A ⟶ X) (hj : NecklaceSimple j) [Mono j]
  {a b : A.obj (op ⦋0⦌)}

/-- The lifted diagram retains every original flag and its full colimit cocone equation. -/
def simpleFlagCocone : Cocone (NecklacesOver.flagDiagram X (j.app _ a) (j.app _ b)) where
  pt := flagHom A a b
  ι :=
    { app := fun P ↦ flagLeg A a b (simpleLiftObj j hj P)
      naturality _ _ h := (flagCocone A a b).ι.naturality (simpleLiftHom j hj h) }

def simpleFlagInverse : flagHom X (j.app _ a) (j.app _ b) ⟶ flagHom A a b :=
  flagDesc X (j.app _ a) (j.app _ b) (simpleFlagCocone j hj)

theorem simpleFlagHom_hom_inv :
    flagHomMap (a := a) (b := b) j ≫ simpleFlagInverse j hj = 𝟙 _ := by
  ext q t
  induction t using Quot.ind with
  | _ p =>
    change Quot.mk _ ⟨simpleLiftObj j hj ((NecklacesOver.postcomp j).obj p.1), p.2⟩ =
      Quot.mk _ p
    apply Quot.sound
    refine ⟨simpleLiftPostcompHom j hj p.1, ?_⟩
    exact (NecklaceCode.Flag.map_id p.2).symm

theorem simpleFlagHom_inv_hom :
    simpleFlagInverse (a := a) (b := b) j hj ≫ flagHomMap j = 𝟙 _ := by
  ext q t
  induction t using Quot.ind with
  | _ p =>
    change Quot.mk _ ⟨(NecklacesOver.postcomp j).obj (simpleLiftObj j hj p.1), p.2⟩ =
      Quot.mk _ p
    apply Quot.sound
    refine ⟨simplePostcompLiftHom j hj p.1, ?_⟩
    exact (NecklaceCode.Flag.map_id p.2).symm

/-- The forward map is precisely the existing flagHomMap of the supplied inclusion. -/
def simpleFlagHomIso : flagHom A a b ≅ flagHom X (j.app _ a) (j.app _ b) where
  hom := flagHomMap j
  inv := simpleFlagInverse j hj
  hom_inv_id := simpleFlagHom_hom_inv j hj
  inv_hom_id := simpleFlagHom_inv_hom j hj

theorem simpleFlagHomIso_hom : (simpleFlagHomIso (a := a) (b := b) j hj).hom =
    flagHomMap j := rfl

end

end DaggerOriginalProductGadget
