import AmalgamPresentation

/-! Exact original object embeddings, intersection and shared glued identity. -/

open CategoryTheory Limits MonoidalCategory DaggerModels

universe u

namespace DaggerAmalgamPresentation

noncomputable section

variable (B B' : SimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)

theorem selectLeft_injective : Function.Injective (selectLeft B b) :=
  fun _ _ _ ↦ Subsingleton.elim _ _

theorem leftObj_injective : Function.Injective (leftObj B B' b b') := by
  have : Mono (selectLeft B b) := (mono_iff_injective _).2 (selectLeft_injective B b)
  intro x y h
  have hh := (Types.Pushout.quot_mk_eq_iff (selectLeft B b) (selectRight B' b')
    (Sum.inl x) (Sum.inl y)).1 h
  rw [Types.Pushout.inl_rel'_inl_iff] at hh
  rcases hh with hh | ⟨s, t, hs, hx, hy⟩
  · exact hh
  · exact hx.trans hy.symm

theorem rightObj_injective : Function.Injective (rightObj B B' b b') := by
  have : Mono (selectLeft B b) := (mono_iff_injective _).2 (selectLeft_injective B b)
  intro x y h
  exact (Types.Pushout.inr_rel'_inr_iff _ _ x y).1
    ((Types.Pushout.quot_mk_eq_iff (selectLeft B b) (selectRight B' b')
      (Sum.inr x) (Sum.inr y)).1 h)

/-- The only intersection is the two originally selected objects. -/
theorem leftObj_eq_rightObj_iff (x : B.Obj) (y : B'.Obj) :
    leftObj B B' b b' x = rightObj B B' b b' y ↔ x = b ∧ y = b' := by
  have : Mono (selectLeft B b) := (mono_iff_injective _).2 (selectLeft_injective B b)
  rw [leftObj, rightObj, Types.Pushout.inl_eq_inr_iff]
  constructor
  · rintro ⟨s, hx, hy⟩
    exact ⟨hx.symm, hy.symm⟩
  · rintro ⟨hx, hy⟩
    exact ⟨PUnit.unit, hx.symm, hy.symm⟩

theorem label_injective (c : Bool) : Function.Injective (label B B' b b' c) := by
  cases c
  · exact leftObj_injective B B' b b'
  · exact rightObj_injective B B' b b'

theorem factor_identity_nil (c : Bool) (q : SimplexCategoryᵒᵖ) (x : (factor B B' c).Obj) :
    ((leg B B' b b' c).map x x).app q ((eId SSet x).app q PUnit.unit) =
      SimplicialCat.HomQuotient.mk (relations B B' b b') q .nil :=
  SimplicialCat.HomQuotient.sound _ q (Rel.factorId c x)

theorem nil_transport (q : SimplexCategoryᵒᵖ) {a z : Objects B B' b b'} (h : a = z) :
    (eqToHom (by rw [h]) :
      SimplicialCat.HomQuotient.hom (relations B B' b b') a a ⟶
        SimplicialCat.HomQuotient.hom (relations B B' b b') z z).app q
      (SimplicialCat.HomQuotient.mk (relations B B' b b') q .nil) =
        SimplicialCat.HomQuotient.mk (relations B B' b b') q .nil := by
  cases h
  rfl

/-- Both originally selected factor identities become the SAME transported nil. -/
theorem glued_factor_identities (q : SimplexCategoryᵒᵖ) :
    (eqToHom (by rw [glued B B' b b']) :
      SimplicialCat.HomQuotient.hom (relations B B' b b') (leftObj B B' b b' b)
        (leftObj B B' b b' b) ⟶
      SimplicialCat.HomQuotient.hom (relations B B' b b') (rightObj B B' b b' b')
        (rightObj B B' b b' b')).app q
      (((leftLeg B B' b b').map b b).app q ((eId SSet b).app q PUnit.unit)) =
        ((rightLeg B B' b b').map b' b').app q ((eId SSet b').app q PUnit.unit) := by
  rw [factor_identity_nil, factor_identity_nil]
  exact nil_transport B B' b b' q (glued B B' b b')

variable {P : SimplicialCat.{u, u}} (i : B ⟶ P) (i' : B' ⟶ P)
  (sq : IsPushout (leftSelector B b) (rightSelector B' b') i i')

/-- The complete ordinary enriched iso with any original ordinary pushout apex. -/
def ordinaryOriginalIso : Q B B' b b' ≅ P :=
  (isPushout B B' b b').isoIsPushout B B' sq

theorem ordinary_left_iso_hom : leftLeg B B' b b' ≫
    (ordinaryOriginalIso B B' b b' i i' sq).hom = i :=
  IsPushout.inl_isoIsPushout_hom B B' (isPushout B B' b b') sq

theorem ordinary_right_iso_hom : rightLeg B B' b b' ≫
    (ordinaryOriginalIso B B' b b' i i' sq).hom = i' :=
  IsPushout.inr_isoIsPushout_hom B B' (isPushout B B' b b') sq

theorem ordinary_left_iso_inv : i ≫ (ordinaryOriginalIso B B' b b' i i' sq).inv =
    leftLeg B B' b b' :=
  IsPushout.inl_isoIsPushout_inv B B' (isPushout B B' b b') sq

theorem ordinary_right_iso_inv : i' ≫ (ordinaryOriginalIso B B' b b' i i' sq).inv =
    rightLeg B B' b b' :=
  IsPushout.inr_isoIsPushout_inv B B' (isPushout B B' b b') sq

end
end DaggerAmalgamPresentation
