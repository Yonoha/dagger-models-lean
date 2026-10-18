import AmalgamListReduction

/-! Exact one-step correspondence between tagged lists and the original dependent paths. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation

universe u

namespace DaggerAmalgamReduction

variable (B B' : SimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)
variable {q : SimplexCategoryᵒᵖ}

/-- Every original edge, in snoc-reversed order, retaining color and both endpoints. -/
def encode {a z : Objects B B' b b'} : Path B B' b b' q a z → List (Edge B B' q)
  | .nil => []
  | .cons p e => e.val :: encode p

@[simp] theorem encode_nil (a : Objects B B' b b') :
    encode B B' b b' (.nil : Path B B' b b' q a a) = [] := rfl

@[simp] theorem encode_cons {a z t : Objects B B' b b'}
    (p : Path B B' b b' q a z) (e : (graph B B' b b').Hom z t |>.obj q) :
    encode B B' b b' (p.cons e) = e.val :: encode B B' b b' p := rfl

@[simp] theorem encode_comp {a z t : Objects B B' b b'}
    (p : Path B B' b b' q a z) (v : Path B B' b b' q z t) :
    encode B B' b b' (p.comp v) = encode B B' b b' v ++ encode B B' b b' p := by
  induction v with
  | nil => rfl
  | cons v e ih => simpa only [encode, List.cons_append] using congrArg (e.val :: ·) ih

@[simp] theorem encode_factorPath (c : Bool) {x y : At B B' q c} (h : x ⟶ y) :
    encode B B' b b' (factorPath B B' b b' c q h) = [tag B B' q c h] := rfl

theorem encode_injective {a z : Objects B B' b b'} :
    Function.Injective (encode B B' b b' : Path B B' b b' q a z → _) := by
  intro p
  induction p with
  | nil =>
    intro p' h
    cases p' with
    | nil => rfl
    | cons p' e => cases h
  | cons p e ih =>
    intro p' h
    cases p' with
    | nil => simp only [encode, List.cons_ne_nil] at h
    | cons p' e' =>
      simp only [encode, List.cons.injEq] at h
      rcases e with ⟨e, hs, ht⟩
      rcases e' with ⟨e', hs', ht'⟩
      obtain rfl := h.1
      obtain rfl := hs.symm.trans hs'
      congr 1
      exact ih h.2

theorem listRed_append_left {α : Type*} {I : α → Prop} {M : α → α → α → Prop}
    (l : List α) {s t : List α} (h : ListRed I M s t) : ListRed I M (l ++ s) (l ++ t) := by
  induction l with
  | nil => exact h
  | cons a l ih => exact .cons a ih

theorem listRed_append_right {α : Type*} {I : α → Prop} {M : α → α → α → Prop}
    {s t : List α} (h : ListRed I M s t) (l : List α) : ListRed I M (s ++ l) (t ++ l) := by
  induction h with
  | delete a s hi => exact .delete a (s ++ l) hi
  | merge a d e s hm => exact .merge a d e (s ++ l) hm
  | cons a h ih => exact .cons a ih

theorem red_encode {a z : Objects B B' b b'} {p p' : Path B B' b b' q a z}
    (h : Red B B' b b' q a z p p') :
    ReverseEncodedRed B B' q (encode B B' b b' p) (encode B B' b b' p') := by
  rcases h with ⟨s, t, l, r, r', v, h⟩
  change ReverseEncodedRed B B' q
    (encode B B' b b' (l.comp (r.comp v))) (encode B B' b b' (l.comp (r'.comp v)))
  simp only [encode_comp]
  rw [List.append_assoc, List.append_assoc]
  apply listRed_append_left
  apply listRed_append_right
  cases h with
  | factorId c x => exact .delete _ [] (.intro c x)
  | factorComp c h k => exact .merge _ _ _ [] (.intro c h k)

theorem red_prefix {a s t : Objects B B' b b'} (l : Path B B' b b' q a s)
    {p p' : Path B B' b b' q s t} (h : Red B B' b b' q s t p p') :
    Red B B' b b' q a t (l.comp p) (l.comp p') :=
  HomRel.comp_left (r := HomRel.CompClosure
    (SimplicialCat.HomQuotient.degreeRel (relations B B' b b') q)) l h

theorem red_cons {a s t : Objects B B' b b'} {p p' : Path B B' b b' q a s}
    (h : Red B B' b b' q a s p p') (e : (graph B B' b b').Hom s t |>.obj q) :
    Red B B' b b' q a t (p.cons e) (p'.cons e) := by
  exact HomRel.comp_right (r := HomRel.CompClosure
    (SimplicialCat.HomQuotient.degreeRel (relations B B' b b') q))
      (@Quiver.Hom.toPath (SimplicialColimitsFree.Paths.At (graph B B' b b') q)
        (SimplicialColimitsFree.Paths.quiverAt (graph B B' b b') q) _ _ e) h

/-- Every encoded one-step join lifts to the SAME contextual relation and endpoints. -/
theorem lift_encoded {s t : List (Edge B B' q)} (h : ReverseEncodedRed B B' q s t)
    {a z : Objects B B' b b'} (p : Path B B' b b' q a z)
    (hp : encode B B' b b' p = s) :
    ∃ p' : Path B B' b b' q a z, Red B B' b b' q a z p p' ∧
      encode B B' b b' p' = t := by
  induction h generalizing a z with
  | delete e l hi =>
    cases p with
    | nil => cases hp
    | cons p e =>
      simp only [encode, List.cons.injEq] at hp
      cases hi with
      | intro c x =>
        rcases e with ⟨e, hs, ht⟩
        obtain rfl := hp.1
        obtain rfl := hs
        obtain rfl := ht
        refine ⟨p, ?_, hp.2⟩
        exact red_prefix B B' b b' p
          (HomRel.CompClosure.of (@Rel.factorId B B' b b' q c x))
  | merge e d f l hm =>
    cases p with
    | nil => cases hp
    | cons p k =>
      cases p with
      | nil => cases hp
      | cons p h =>
        simp only [encode, List.cons.injEq] at hp
        cases hm with
        | @intro c x y z h₀ k₀ =>
          rcases k with ⟨k, hks, hkt⟩
          rcases h with ⟨h, hhs, hht⟩
          obtain rfl := hp.1
          obtain rfl := hp.2.1
          obtain rfl := hhs
          obtain rfl := hht
          obtain rfl := hkt
          let v := factorPath B B' b b' c q (h₀ ≫ k₀)
          refine ⟨Quiver.Path.comp p v, ?_, ?_⟩
          · exact red_prefix B B' b b' p
              (HomRel.CompClosure.of (@Rel.factorComp B B' b b' q c _ _ _ h₀ k₀))
          · simp [v, hp.2.2]
  | cons e ht ih =>
    cases p with
    | nil => cases hp
    | cons p e =>
      simp only [encode, List.cons.injEq] at hp
      obtain ⟨p', hh, he⟩ := ih p hp.2
      exact ⟨p'.cons e, red_cons B B' b b' hh e, by simp [he, hp.1]⟩

theorem red_iff_encoded {a z : Objects B B' b b'} {p p' : Path B B' b b' q a z} :
    Red B B' b b' q a z p p' ↔
      ReverseEncodedRed B B' q (encode B B' b b' p) (encode B B' b b' p') := by
  refine ⟨red_encode B B' b b', fun h ↦ ?_⟩
  obtain ⟨v, hv, he⟩ := lift_encoded B B' b b' h p rfl
  obtain rfl := encode_injective B B' b b' he
  exact hv

end DaggerAmalgamReduction
