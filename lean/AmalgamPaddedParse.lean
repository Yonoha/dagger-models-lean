import AmalgamPaddedAppend

/-! Parsing alternating actual dependent paths into their complete original raw tuples.
Endpoint labels and the original reversed-snoc encoding are retained throughout. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def firstColor {q : SimplexCategoryᵒᵖ} : List (Edge C B q) → Option Bool
  | [] => none
  | e :: [] => some e.1
  | _ :: d :: l => firstColor (d :: l)

def Starts {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) (c : Bool) : Prop :=
  firstColor C B (encode C B x b p) = some c

def Ends {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) (c : Bool) : Prop :=
  (encode C B x b p).head?.map (fun e ↦ e.1) = some c

/-- The complete tuple exists for every literally alternating path with the stated end colors. -/
theorem exists_raw_alternating {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) (ha : Alternating C B (encode C B x b p)) :
    ∀ (c d : Bool) (a : At C B q c) (z : At C B q d)
      (_hs : label C B x b c a = s) (_ht : label C B x b d z = t),
      Starts C B x b p c → Ends C B x b p d →
        ∃ (r : ℕ) (h : RawFamily C B x b q c d a z r),
          encode C B x b (decodeFamily C B x b q c d a z r h) = encode C B x b p := by
  letI : Quiver (Objects C B x b) :=
    SimplicialColimitsFree.Paths.quiverAt (graph C B x b) q
  induction p with
  | nil =>
    intro c d a z hs ht hstart hend
    simp [Starts, encode, firstColor] at hstart
  | @cons v t p e ih =>
    intro c d a z hs ht hstart hend
    rcases e with ⟨⟨cd, u, z', k⟩, heS, heT⟩
    have hd : cd = d := by simpa [Ends, encode] using hend
    cases hd
    have hz : z' = z := label_injective C B x b d (heT.trans ht.symm)
    cases hz
    cases p with
    | nil =>
      have hc : d = c := by simpa [Starts, encode, firstColor] using hstart
      cases hc
      have hu : u = a := label_injective C B x b c (heS.trans hs.symm)
      cases hu
      cases c
      · exact ⟨0, k, rfl⟩
      · exact ⟨0, k, rfl⟩
    | @cons v' _ p f =>
      rcases f with ⟨⟨cp, u', z'', k'⟩, hfS, hfT⟩
      have hdiff : d ≠ cp := ha.1
      let prev : Path C B x b q s v := p.cons ⟨⟨cp, u', z'', k'⟩, hfS, hfT⟩
      have hp : Starts C B x b prev c := hstart
      have hpa : Alternating C B (encode C B x b prev) := ha.2
      have heq := hfT.trans heS.symm
      cases d <;> cases cp
      · exact False.elim (hdiff rfl)
      · have hcross := (leftObj_eq_rightObj_iff C B x b u z'').1 heq.symm
        rcases hcross with ⟨hu, hz⟩
        cases hu
        cases hz
        obtain ⟨r, h, hh⟩ := ih hpa c true a b hs hfT hp rfl
        let out := appendFamily C B x b q c false a z ⟨r, h⟩ k
        refine ⟨out.1, out.2, ?_⟩
        rw [encode_appendFamily]
        simpa only [Bool.not, glueAt, encode] using congrArg (List.cons (tag C B q _ k)) hh
      · have hcross := (leftObj_eq_rightObj_iff C B x b z'' u).1 heq
        rcases hcross with ⟨hz, hu⟩
        cases hu
        cases hz
        obtain ⟨r, h, hh⟩ := ih hpa c false a x hs hfT hp rfl
        let out := appendFamily C B x b q c true a z ⟨r, h⟩ k
        refine ⟨out.1, out.2, ?_⟩
        rw [encode_appendFamily]
        simpa only [Bool.not, glueAt, encode] using congrArg (List.cons (tag C B q _ k)) hh
      · exact False.elim (hdiff rfl)

/-- Whole dependent-path equality, not only equality of colors or quotient classes. -/
theorem exists_raw_path {q : SimplexCategoryᵒᵖ} (c d : Bool)
    (a : At C B q c) (z : At C B q d)
    (p : Path C B x b q (label C B x b c a) (label C B x b d z))
    (ha : Alternating C B (encode C B x b p))
    (hs : Starts C B x b p c) (ht : Ends C B x b p d) :
    ∃ (r : ℕ) (h : RawFamily C B x b q c d a z r),
      decodeFamily C B x b q c d a z r h = p := by
  obtain ⟨r, h, he⟩ := exists_raw_alternating C B x b p ha c d a z rfl rfl hs ht
  exact ⟨r, h, encode_injective C B x b he⟩

end
end DaggerAmalgamPaddedClassifier
