import RigidificationCofDoubleCuts

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A : SC.{u}}

abbrev evaluateProper (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (i j : Fin (n + 2)) (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1)))
    (q : SimplexCategoryᵒᵖ) (γ : (hom (ULift.up i) (ULift.up j)).obj q) :=
  (properMap a i j hp).app q γ

theorem evaluateProper_comp (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (i j k : Fin (n + 2)) (hij : i ≤ j) (hjk : j ≤ k)
    (hpik : ¬ (i = 0 ∧ k = Fin.last (n + 1)))
    (hpij : ¬ (i = 0 ∧ j = Fin.last (n + 1)))
    (hpjk : ¬ (j = 0 ∧ k = Fin.last (n + 1)))
    (q : SimplexCategoryᵒᵖ) (γ : (hom (ULift.up i) (ULift.up j)).obj q)
    (δ : (hom (ULift.up j) (ULift.up k)).obj q) :
    evaluateProper a i k hpik q ((compose (ULift.up i) (ULift.up j) (ULift.up k)).app q
      (γ, δ)) = elementComp q (evaluateProper a i j hpij q γ)
        (evaluateProper a j k hpjk q δ) :=
  congrFun (congrArg (fun f => f.app q)
    (properMap_comp_forward a i j k hij hjk hpik hpij hpjk)) (γ, δ)

theorem cutEvaluation_app (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k : interior n) (q : SimplexCategoryᵒᵖ) (γ : (extremeCut.{u} n k).toSSet.obj q) :
    (cutEvaluation a k).app q γ =
      elementComp q (evaluateProper a 0 k.val (leftProper k) q (splitChainLeft γ))
        (evaluateProper a k.val (Fin.last (n + 1)) (rightProper k) q
          (splitChainRight γ)) := rfl

theorem middleProper (k l : interior n) :
    ¬ (k.val = 0 ∧ l.val = Fin.last (n + 1)) := fun h => (ne_of_gt k.property.1) h.1

/-- Both cuts evaluate the SAME original three intervals with original associativity. -/
theorem cut_overlap_component_lt (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k l : interior n) (hkl : k.val < l.val) (q : SimplexCategoryᵒᵖ)
    (γ : (extremeHom.{u} n).obj q) (hk : ∀ t, ULift.up k.val ∈ (γ.obj t).I)
    (hl : ∀ t, ULift.up l.val ∈ (γ.obj t).I) :
    (cutEvaluation a k).app q ⟨γ, hk⟩ = (cutEvaluation a l).app q ⟨γ, hl⟩ := by
  rw [cutEvaluation_app, cutEvaluation_app,
    splitRight_double γ hk hl (show ULift.up.{u} k.val ≤ ULift.up l.val from hkl.le),
    splitLeft_double γ hk hl (show ULift.up.{u} k.val ≤ ULift.up l.val from hkl.le)]
  rw [evaluateProper_comp a k.val l.val (Fin.last (n + 1)) hkl.le (Fin.le_last _)
      (rightProper k) (middleProper k l) (rightProper l),
    evaluateProper_comp a 0 k.val l.val (Fin.zero_le _) hkl.le
      (leftProper l) (leftProper k) (middleProper k l)]
  exact (element_assoc q _ _ _).symm

/-- Cut/cut agreement on the WHOLE intersection, including coincident cuts. -/
theorem cut_overlap (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k l : interior n) :
    SSet.Subcomplex.homOfLE (inf_le_left : extremeCut n k ⊓ extremeCut n l ≤ _)
        ≫ cutEvaluation a k =
      SSet.Subcomplex.homOfLE (inf_le_right : extremeCut n k ⊓ extremeCut n l ≤ _)
        ≫ cutEvaluation a l := by
  apply NatTrans.ext
  funext q γ
  rcases lt_trichotomy k.val l.val with h | h | h
  · exact cut_overlap_component_lt a k l h q γ.val γ.property.1 γ.property.2
  · have e : k = l := Subtype.ext h
    cases e
    rfl
  · exact (cut_overlap_component_lt a l k h q γ.val γ.property.2 γ.property.1).symm

end

end DaggerOrdinaryRigidificationCof.BoundaryData
