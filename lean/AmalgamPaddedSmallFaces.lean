import AmalgamPaddedFaceParsing

/-! The exceptional first faces are the SAME original C/B endpoint compositions. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem UnitFaceData.triple_composition {q : SimplexCategoryᵒᵖ}
    {s t : Objects C B x b} {p : Path C B x b q s t} {unit : Edge C B q}
    (fd : UnitFaceData C B x b p unit) (left right comp : Edge C B q)
    (he : encode C B x b p = [left, unit, right]) (hm : Merge C B q right left comp) :
    encode C B x b fd.face = [comp] := by
  have hc := fd.original_encode
  rw [he] at hc
  have hl := congrArg List.length hc
  simp only [List.length_cons, List.length_nil, List.length_append] at hl
  have hp : fd.pre = [] := List.eq_nil_of_length_eq_zero (by omega)
  have ht : fd.post = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [hp, ht, List.nil_append, List.cons.injEq] at hc
  have hh : fd.composed = comp := merge_unique C B q
    (by simpa only [← hc.1, ← hc.2.2.1] using fd.neighbors_composition) hm
  rw [fd.face_encode, hp, ht, hh]
  rfl

theorem rawFaceOO_one_composition (q : SimplexCategoryᵒᵖ) (a d : C.Obj)
    (h : RawOO C B x b q a d 1)
    (fd : UnitFaceData C B x b (decodeOO C B x b q a d 1 h)
      (tag C B q true (h.2.1 0))) :
    rawFaceOO C B x b q a d 0 h _ fd =
      (eComp SSet a x d).app q (h.1, h.2.2.2) := by
  have he : encode C B x b fd.face = [tag C B q false (h.1 ≫ h.2.2.2)] :=
    fd.triple_composition C B x b _ _ _ (by simp [decodeOO, zig, encode_bLoop]) (.intro false _ _)
  have hd := congrArg (encode C B x b) (rawFaceOO_decode C B x b q a d 0 h _ fd)
  rw [he] at hd
  exact tag_injective C B q false a d (List.cons.inj hd).1

theorem rawFaceNN_one_composition (q : SimplexCategoryᵒᵖ) (z w : B.Obj)
    (h : RawNN C B x b q z w 1)
    (fd : UnitFaceData C B x b (decodeNN C B x b q z w 1 h)
      (tag C B q false (h.2.1 0))) :
    rawFaceNN C B x b q z w 0 h _ fd =
      (eComp SSet z b w).app q (h.1, h.2.2.2) := by
  have he : encode C B x b fd.face = [tag C B q true (h.1 ≫ h.2.2.2)] :=
    fd.triple_composition C B x b _ _ _ 
      (by simp [decodeNN, zag, encode_bStart, encode_bEnd]) (.intro true _ _)
  have hd := congrArg (encode C B x b) (rawFaceNN_decode C B x b q z w 0 h _ fd)
  rw [he] at hd
  exact tag_injective C B q true z w (List.cons.inj hd).1

end
end DaggerAmalgamPaddedClassifier
