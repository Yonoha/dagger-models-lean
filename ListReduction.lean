import Mathlib.Logic.Relation

/-! A one-step list encoding helper. The actual typed relation is not replaced by it. -/

universe u

namespace DaggerAmalgamReduction

variable {α : Type u} (I : α → Prop) (M : α → α → α → Prop)

inductive ListRed : List α → List α → Prop
  | delete (a : α) (l : List α) (h : I a) : ListRed (a :: l) l
  | merge (a b c : α) (l : List α) (h : M a b c) :
      ListRed (a :: b :: l) (c :: l)
  | cons (a : α) {l l' : List α} (h : ListRed l l') : ListRed (a :: l) (a :: l')

theorem listRed_diamond
    (left_unit : ∀ {a b c}, I a → M a b c → c = b)
    (right_unit : ∀ {a b c}, I b → M a b c → c = a)
    (unique : ∀ {a b c d}, M a b c → M a b d → c = d)
    (assoc : ∀ {a b c d e}, M a b c → M b d e → ∃ f, M c d f ∧ M a e f)
    {l l₁ l₂ : List α} (h₁ : ListRed I M l l₁) (h₂ : ListRed I M l l₂) :
    ∃ d, Relation.ReflGen (ListRed I M) l₁ d ∧
      Relation.ReflGen (ListRed I M) l₂ d := by
  induction h₁ generalizing l₂ with
  | delete a l hi =>
    cases h₂ with
    | delete _ _ _ => exact ⟨l, .refl, .refl⟩
    | merge _ b c _ hm =>
      obtain rfl := left_unit hi hm
      exact ⟨_, .refl, .refl⟩
    | cons _ ht => exact ⟨_, .single ht, .single (.delete _ _ hi)⟩
  | merge a b c l hm =>
    cases h₂ with
    | delete _ _ hi =>
      obtain rfl := left_unit hi hm
      exact ⟨_, .refl, .refl⟩
    | merge _ _ d _ hm' =>
      obtain rfl := unique hm hm'
      exact ⟨_, .refl, .refl⟩
    | cons _ ht =>
      cases ht with
      | delete _ _ hi =>
        obtain rfl := right_unit hi hm
        exact ⟨_, .refl, .refl⟩
      | merge _ d e l' hm' =>
        obtain ⟨f, hf, hf'⟩ := assoc hm hm'
        exact ⟨f :: l', .single (.merge _ _ _ _ hf), .single (.merge _ _ _ _ hf')⟩
      | cons _ ht' =>
        exact ⟨_, .single (.cons _ ht'), .single (.merge _ _ _ _ hm)⟩
  | cons a ht ih =>
    cases h₂ with
    | delete _ _ hi => exact ⟨_, .single (.delete _ _ hi), .single ht⟩
    | merge _ b c l hm =>
      cases ht with
      | delete _ _ hi =>
        obtain rfl := right_unit hi hm
        exact ⟨_, .refl, .refl⟩
      | merge _ d e l' hm' =>
        obtain ⟨f, hf, hf'⟩ := assoc hm hm'
        exact ⟨f :: l', .single (.merge _ _ _ _ hf'), .single (.merge _ _ _ _ hf)⟩
      | cons _ ht' =>
        exact ⟨_, .single (.merge _ _ _ _ hm), .single (.cons _ ht')⟩
    | cons _ ht' =>
      obtain ⟨d, hd, hd'⟩ := ih ht'
      refine ⟨a :: d, ?_, ?_⟩
      · cases hd with
        | refl => exact .refl
        | single h => exact .single (.cons _ h)
      · cases hd' with
        | refl => exact .refl
        | single h => exact .single (.cons _ h)

end DaggerAmalgamReduction
