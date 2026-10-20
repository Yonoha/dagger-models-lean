import OriginalCrossingArrowLift

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerChosenRigidificationNecklace.NecklaceThickening

universe u

namespace DaggerOriginalProductGadget

noncomputable section

theorem intervalOuterHomIso_image (T : NecklaceCode) (a b : Fin (T.len + 1))
    (hab : a ≤ b) {n : ℕ} (F : Flag.{u} (intervalCode T a b hab) n) (i : Fin (n + 1)) :
    (((intervalOuterHomIso T a b hab).hom.app (op ⦋n⦌) F).obj i).I =
      mapVertices (intervalι T a b hab) '' F.chain i := by
  rw [intervalOuterHomIso_I]
  congr 1
  exact (funext (intervalι_vertices T a b hab)).symm

variable (T : NecklaceCode) (a k b : Fin (T.len + 1)) (hak : a ≤ k) (hkb : k ≤ b)

/-- Compose the actual interval flags via the existing interval path isomorphisms. -/
def intervalFlagCompose :
    flagSSet.{u} (intervalCode T a k hak) ⊗ flagSSet (intervalCode T k b hkb) ⟶
      flagSSet (intervalCode T a b (hak.trans hkb)) :=
  ((intervalOuterHomIso T a k hak).hom ⊗ₘ (intervalOuterHomIso T k b hkb).hom) ≫
    pathComp (⟨ULift.up a⟩ : NecklaceThickening T) ⟨ULift.up k⟩ ⟨ULift.up b⟩ ≫
      (intervalOuterHomIso T a b (hak.trans hkb)).inv

/-- Its literal vertex image is the union of the two original interval vertex images. -/
theorem intervalFlagCompose_image {n : ℕ}
    (F : Flag.{u} (intervalCode T a k hak) n)
    (G : Flag.{u} (intervalCode T k b hkb) n) (i : Fin (n + 1)) :
    mapVertices (intervalι T a b (hak.trans hkb)) ''
        (((intervalFlagCompose T a k b hak hkb).app (op ⦋n⦌) (F, G)).chain i) =
      mapVertices (intervalι T a k hak) '' F.chain i ∪
        mapVertices (intervalι T k b hkb) '' G.chain i := by
  have he : intervalFlagCompose.{u} T a k b hak hkb ≫
        (intervalOuterHomIso T a b (hak.trans hkb)).hom =
      ((intervalOuterHomIso T a k hak).hom ⊗ₘ (intervalOuterHomIso T k b hkb).hom) ≫
        pathComp (⟨ULift.up a⟩ : NecklaceThickening T) ⟨ULift.up k⟩ ⟨ULift.up b⟩ := by
    simp [intervalFlagCompose, Category.assoc]
  have hh := congrArg (fun m ↦ ((m.app (op ⦋n⦌) (F, G)).obj i).I) he
  change (((intervalOuterHomIso T a b (hak.trans hkb)).hom.app (op ⦋n⦌)
      ((intervalFlagCompose T a k b hak hkb).app (op ⦋n⦌) (F, G))).obj i).I =
    (((intervalOuterHomIso T a k hak).hom.app (op ⦋n⦌) F).obj i).I ∪
      (((intervalOuterHomIso T k b hkb).hom.app (op ⦋n⦌) G).obj i).I at hh
  rw [intervalOuterHomIso_image, intervalOuterHomIso_image, intervalOuterHomIso_image] at hh
  exact hh

/-- This operation agrees with the original flag quotient composition on the original necklace. -/
theorem intervalFlagCompose_original {n : ℕ}
    (F : Flag.{u} (intervalCode T a k hak) n)
    (G : Flag.{u} (intervalCode T k b hkb) n) :
    flagCompApp
        (Quot.mk _ (⟨intervalOver T a k hak, F⟩ : RawFlag _ _ _ (op ⦋n⦌)))
        (Quot.mk _ (⟨intervalOver T k b hkb, G⟩ : RawFlag _ _ _ (op ⦋n⦌))) =
      Quot.mk _ (⟨intervalOver T a b (hak.trans hkb),
        (intervalFlagCompose T a k b hak hkb).app (op ⦋n⦌) (F, G)⟩ :
          RawFlag _ _ _ (op ⦋n⦌)) := by
  have : IsIso (necklaceFlagEvaluation.{u}
      (x := T.verticesEquiv.symm (ULift.up a))
      (y := T.verticesEquiv.symm (ULift.up b)) T) :=
    necklaceFlagEvaluation_isIso T a b (hak.trans hkb)
  apply ((asIso (necklaceFlagEvaluation.{u}
    (x := T.verticesEquiv.symm (ULift.up a))
    (y := T.verticesEquiv.symm (ULift.up b)) T)).app (op ⦋n⦌)).toEquiv.injective
  have he := congrArg (fun m ↦ m.app (op ⦋n⦌)
      (Quot.mk _ (⟨intervalOver T a k hak, F⟩ : RawFlag _ _ _ (op ⦋n⦌)),
        Quot.mk _ (⟨intervalOver T k b hkb, G⟩ : RawFlag _ _ _ (op ⦋n⦌))))
    (necklaceFlagEvaluation_composition T _ _ _)
  refine he.trans ?_
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext
    (intervalFlagCompose_image T a k b hak hkb F G i).symm)

end

end DaggerOriginalProductGadget
