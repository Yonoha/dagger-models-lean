import ChosenFlagIdentityLeg

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode

/-- Every actual raw class, rather than only finite/outer-endpoint objects, is detected. -/
theorem flagEndomorphism_eq_id (X : SSet.{u}) (F : E X ⟶ E X)
    (ho : ∀ x, F.obj x = x)
    (hP : ∀ {a b} (P : NecklacesOver X a b), EMap P.map ≫ F = EMap P.map) : F = 𝟙 (E X) := by
  apply EnrichedFunctor.ext SSet ho
  intro a b
  apply NatTrans.ext
  funext q t
  induction t using Quot.ind with | _ p
  have H := enrichedFunctor_hom_congr_to_fixed (hP p.1)
    p.1.code.first p.1.code.last a b
    ((congrArg F.obj p.1.first).trans (ho a))
    ((congrArg F.obj p.1.last).trans (ho b)) p.1.first p.1.last
  have Hleg : flagLeg X a b p.1 ≫ F.map a b ≫ targetHomTransport (ho a) (ho b) =
      flagLeg X a b p.1 := by
    rw [← flagLeg_reproduction p.1]
    simp only [Category.assoc]
    rw [← Category.assoc (targetHomTransport p.1.first p.1.last),
      enriched_map_endpoint_transport]
    simp only [Category.assoc]
    rw [targetHomTransport_trans]
    change flagLeg p.1.code.toSSet p.1.code.first p.1.code.last (identityOver p.1.code) ≫
      ((EMap p.1.map ≫ F).map p.1.code.first p.1.code.last ≫
        targetHomTransport ((congrArg F.obj p.1.first).trans (ho a))
          ((congrArg F.obj p.1.last).trans (ho b))) = _
    rw [H]
  exact congrFun (NatTrans.congr_app Hleg q) p.2

end

end DaggerChosenRigidificationNecklace
