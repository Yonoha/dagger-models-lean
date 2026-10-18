import ChosenNecklaceGeneralNCMap
import ChosenNecklaceFlagIso
import ChosenFlagFunctor

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

theorem necklaceFlagFunctor_general_naturality {T U : NecklaceCode}
    (f : toSSet.{u} T ⟶ toSSet.{u} U) :
    EMap f ≫ necklaceFlagFunctor U = necklaceFlagFunctor T ≫ generalNCMap f := by
  have ho : ∀ x : (E (toSSet.{u} T)).Obj,
      (EMap f ≫ necklaceFlagFunctor U).obj x =
        (necklaceFlagFunctor T ≫ generalNCMap f).obj x := by
    intro x
    apply congrArg NecklaceThickening.mk
    change U.verticesEquiv (f.app _ x) = mapVertices f (T.verticesEquiv x)
    simp only [mapVertices, Equiv.symm_apply_apply]
  apply EnrichedFunctor.ext SSet ho
  intro x y
  apply NatTrans.ext
  funext q F
  induction F using Quot.ind with | _ p
  refine CategoryTheory.Functor.ext (fun i ↦ JointPath.ext ?_)
  change (((eqToHom (show
      ((EMap f ≫ necklaceFlagFunctor U).obj x ⟶[SSet.{u}]
        (EMap f ≫ necklaceFlagFunctor U).obj y) =
      ((necklaceFlagFunctor T ≫ generalNCMap f).obj x ⟶[SSet.{u}]
        (necklaceFlagFunctor T ≫ generalNCMap f).obj y) by rw [ho x, ho y])).app q
      ((necklaceFlagEvaluation U).app q (Quot.mk _
        ⟨(NecklacesOver.postcomp f).obj p.1, p.2⟩))).obj i).I =
    (generalMapPath f (((necklaceFlagEvaluation T).app q (Quot.mk _ p)).obj i)).I
  rw [pathHom_eqToHom_I (ho x) (ho y)]
  change mapVertices (p.1.map ≫ f) '' p.2.chain i =
    generalOrderMap f '' (mapVertices p.1.map '' p.2.chain i)
  rw [mapVertices_comp, Set.image_image]
  rfl

end

end DaggerChosenRigidificationNecklace
