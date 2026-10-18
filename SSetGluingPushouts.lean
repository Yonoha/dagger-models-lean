import IinjBridge
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u
namespace DaggerSSetGluing
noncomputable section
set_option autoImplicit false

/-- Literal geometric weak equivalence, with no Kan premise. -/
def GW {Y Y' : SSet.{u}} (f : Y ⟶ Y') : Prop :=
  SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f))

theorem weakEquivalence_iff_GW {Y Y' : SSet.{u}} (f : Y ⟶ Y') :
    WeakEquivalence f ↔ GW f := DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric f

/-- The left relative comparison is the cobase change of the ORIGINAL right k'. -/
theorem relative_left_isPushout {A A' X X' M T Q : SSet.{u}}
    (k : A ⟶ X) (k' : A' ⟶ X') (a : A ⟶ M) (a' : A' ⟶ M)
    (j : A ⨿ A' ⟶ M) (TX : X ⨿ X' ⟶ T) (TM : M ⟶ T)
    (hjl : coprod.inl ≫ j = a) (hjr : coprod.inr ≫ j = a')
    (hT : IsPushout (coprod.map k k') j TX TM)
    (l : X ⟶ Q) (m : M ⟶ Q) (hQ : IsPushout k a l m) (rho : Q ⟶ T)
    (hrl : l ≫ rho = coprod.inl ≫ TX) (hrm : m ≫ rho = TM) :
    IsPushout k' (a' ≫ m) (coprod.inr ≫ TX) rho := by
  have w : k' ≫ (coprod.inr ≫ TX) = (a' ≫ m) ≫ rho := by
    have hw := congrArg (fun f ↦ coprod.inr ≫ f) hT.w
    simpa [Category.assoc, reassoc_of% hjr, hrm] using hw
  refine { w := w, isColimit' := ⟨?_⟩ }
  refine PushoutCocone.isColimitAux' _ ?_
  intro t
  let delta : T ⟶ t.pt := hT.desc (coprod.desc (l ≫ t.inr) t.inl) (m ≫ t.inr) (by
    apply coprod.hom_ext
    · simpa [Category.assoc, reassoc_of% hjl] using congrArg (fun f ↦ f ≫ t.inr) hQ.w
    · simpa [Category.assoc, reassoc_of% hjr] using t.condition)
  refine ⟨delta, ?_, ?_, ?_⟩
  · simp [delta, Category.assoc]
  · change rho ≫ delta = t.inr
    apply hQ.hom_ext
    · rw [← Category.assoc, hrl, Category.assoc]
      simp [delta]
    · rw [← Category.assoc, hrm]
      simp [delta]
  · intro f hf1 hf2
    change rho ≫ f = t.inr at hf2
    apply hT.hom_ext
    · simp only [delta, hT.inl_desc]
      apply coprod.hom_ext
      · simp only [coprod.inl_desc]
        rw [← Category.assoc, ← hrl, Category.assoc, hf2]
      · simpa [Category.assoc] using hf1
    · simp only [delta, hT.inr_desc]
      rw [← hrm, Category.assoc, hf2]

/-- The right relative comparison is the cobase change of the ORIGINAL left k. -/
theorem relative_right_isPushout {A A' X X' M T Q : SSet.{u}}
    (k : A ⟶ X) (k' : A' ⟶ X') (a : A ⟶ M) (a' : A' ⟶ M)
    (j : A ⨿ A' ⟶ M) (TX : X ⨿ X' ⟶ T) (TM : M ⟶ T)
    (hjl : coprod.inl ≫ j = a) (hjr : coprod.inr ≫ j = a')
    (hT : IsPushout (coprod.map k k') j TX TM)
    (l : X' ⟶ Q) (m : M ⟶ Q) (hQ : IsPushout k' a' l m) (rho : Q ⟶ T)
    (hrl : l ≫ rho = coprod.inr ≫ TX) (hrm : m ≫ rho = TM) :
    IsPushout k (a ≫ m) (coprod.inl ≫ TX) rho := by
  have w : k ≫ (coprod.inl ≫ TX) = (a ≫ m) ≫ rho := by
    have hw := congrArg (fun f ↦ coprod.inl ≫ f) hT.w
    simpa [Category.assoc, reassoc_of% hjl, hrm] using hw
  refine { w := w, isColimit' := ⟨?_⟩ }
  refine PushoutCocone.isColimitAux' _ ?_
  intro t
  let delta : T ⟶ t.pt := hT.desc (coprod.desc t.inl (l ≫ t.inr)) (m ≫ t.inr) (by
    apply coprod.hom_ext
    · simpa [Category.assoc, reassoc_of% hjl] using t.condition
    · simpa [Category.assoc, reassoc_of% hjr] using congrArg (fun f ↦ f ≫ t.inr) hQ.w)
  refine ⟨delta, ?_, ?_, ?_⟩
  · simp [delta, Category.assoc]
  · change rho ≫ delta = t.inr
    apply hQ.hom_ext
    · rw [← Category.assoc, hrl, Category.assoc]
      simp [delta]
    · rw [← Category.assoc, hrm]
      simp [delta]
  · intro f hf1 hf2
    change rho ≫ f = t.inr at hf2
    apply hT.hom_ext
    · simp only [delta, hT.inl_desc]
      apply coprod.hom_ext
      · simpa [Category.assoc] using hf1
      · simp only [coprod.inr_desc]
        rw [← Category.assoc, ← hrl, Category.assoc, hf2]
    · simp only [delta, hT.inr_desc]
      rw [← hrm, Category.assoc, hf2]

/-- The second square, with every original leg retained, has the full pushout UP. -/
theorem second_isPushout {A X Z P A' X' Z' P' Q V : SSet.{u}}
    (k : A ⟶ X) (ell : A ⟶ Z) (r : X ⟶ P) (s : Z ⟶ P)
    (k' : A' ⟶ X') (ell' : A' ⟶ Z') (r' : X' ⟶ P') (s' : Z' ⟶ P')
    (sq0 : IsPushout k ell r s) (sq1 : IsPushout k' ell' r' s')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (d : P ⟶ P')
    (_he : ell ≫ c = a ≫ ell') (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s')
    (l : X ⟶ Q) (m : A' ⟶ Q) (hQ : IsPushout k a l m)
    (lambda : P ⟶ V) (mu : Z' ⟶ V) (hV : IsPushout s c lambda mu)
    (q : Q ⟶ X') (v : Q ⟶ V) (nu : V ⟶ P')
    (hql : l ≫ q = b) (hqm : m ≫ q = k')
    (hvl : l ≫ v = r ≫ lambda) (hvm : m ≫ v = ell' ≫ mu)
    (hnl : lambda ≫ nu = d) (hnm : mu ≫ nu = s') : IsPushout q v r' nu := by
  have w : q ≫ r' = v ≫ nu := by
    apply hQ.hom_ext
    · simpa [reassoc_of% hql, reassoc_of% hvl, Category.assoc, hnl] using hr.symm
    · simpa [reassoc_of% hqm, reassoc_of% hvm, Category.assoc, hnm] using sq1.w
  refine { w := w, isColimit' := ⟨?_⟩ }
  refine PushoutCocone.isColimitAux' _ ?_
  intro t
  have wa : k' ≫ t.inl = ell' ≫ (mu ≫ t.inr) := by
    have ht := congrArg (fun f ↦ m ≫ f) t.condition
    simpa [Category.assoc, reassoc_of% hqm, reassoc_of% hvm] using ht
  let delta : P' ⟶ t.pt := sq1.desc t.inl (mu ≫ t.inr) wa
  refine ⟨delta, ?_, ?_, ?_⟩
  · simp [delta]
  · change nu ≫ delta = t.inr
    apply hV.hom_ext
    · rw [← Category.assoc, hnl]
      apply sq0.hom_ext
      · rw [← Category.assoc, hr, Category.assoc]
        simp only [delta, sq1.inl_desc]
        have ht := congrArg (fun f ↦ l ≫ f) t.condition
        simpa [Category.assoc, reassoc_of% hql, reassoc_of% hvl] using ht
      · rw [← Category.assoc, hs, Category.assoc]
        simp only [delta, sq1.inr_desc]
        simpa [Category.assoc] using congrArg (fun f ↦ f ≫ t.inr) hV.w.symm
    · rw [← Category.assoc, hnm]
      simp [delta]
  · intro f hf1 hf2
    change nu ≫ f = t.inr at hf2
    apply sq1.hom_ext
    · simpa [delta] using hf1
    · simp only [delta, sq1.inr_desc]
      rw [← hnm, Category.assoc, hf2]

/-- Cobase change for the actual supplied square, not only a chosen apex. -/
theorem cofibration_of_square {A X Z P : SSet.{u}}
    {k : A ⟶ X} {ell : A ⟶ Z} {r : X ⟶ P} {s : Z ⟶ P}
    (sq : IsPushout k ell r s) [Cofibration ell] : Cofibration r := by
  rw [cofibration_iff]
  exact MorphismProperty.of_isPushout sq (mem_cofibrations ell)

theorem weakEquivalence_of_trivial_square {A X Z P : SSet.{u}}
    {k : A ⟶ X} {ell : A ⟶ Z} {r : X ⟶ P} {s : Z ⟶ P}
    (sq : IsPushout k ell r s) [Cofibration ell] [WeakEquivalence ell] :
    WeakEquivalence r := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout sq (mem_trivialCofibrations ell)).2

/-- Two literal pushouts of trivial cofibrations give the supplied apex map W. -/
theorem reedy_geometric {A X Z P A' X' Z' P' Q V : SSet.{u}}
    (k : A ⟶ X) (ell : A ⟶ Z) (r : X ⟶ P) (s : Z ⟶ P)
    (k' : A' ⟶ X') (ell' : A' ⟶ Z') (r' : X' ⟶ P') (s' : Z' ⟶ P')
    (sq0 : IsPushout k ell r s) (sq1 : IsPushout k' ell' r' s')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (d : P ⟶ P')
    (he : ell ≫ c = a ≫ ell') (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s')
    (l : X ⟶ Q) (m : A' ⟶ Q) (hQ : IsPushout k a l m)
    (lambda : P ⟶ V) (mu : Z' ⟶ V) (hV : IsPushout s c lambda mu)
    (q : Q ⟶ X') (v : Q ⟶ V) (nu : V ⟶ P')
    (hql : l ≫ q = b) (hqm : m ≫ q = k')
    (hvl : l ≫ v = r ≫ lambda) (hvm : m ≫ v = ell' ≫ mu)
    (hnl : lambda ≫ nu = d) (hnm : mu ≫ nu = s')
    [Cofibration a] [Cofibration c] [Cofibration q]
    (ha : GW a) (hb : GW b) (hc : GW c) : GW d := by
  letI : WeakEquivalence a := (weakEquivalence_iff_GW a).2 ha
  letI : WeakEquivalence b := (weakEquivalence_iff_GW b).2 hb
  letI : WeakEquivalence c := (weakEquivalence_iff_GW c).2 hc
  letI : Cofibration l := cofibration_of_square hQ
  letI : WeakEquivalence l := weakEquivalence_of_trivial_square hQ
  letI : WeakEquivalence q := weakEquivalence_of_precomp_of_fac hql
  letI : WeakEquivalence lambda := weakEquivalence_of_trivial_square hV
  have hn := second_isPushout k ell r s k' ell' r' s' sq0 sq1 a b c d he hr hs
    l m hQ lambda mu hV q v nu hql hqm hvl hvm hnl hnm
  letI : WeakEquivalence nu := weakEquivalence_of_trivial_square hn.flip
  have hd : WeakEquivalence (lambda ≫ nu) := inferInstance
  rw [hnl] at hd
  exact (weakEquivalence_iff_GW d).1 hd

/-- The relative comparison is the literal chosen pushout.desc. -/
def relativeMap {A X A' X' : SSet.{u}} (k : A ⟶ X) (k' : A' ⟶ X')
    (a : A ⟶ A') (b : X ⟶ X') (hk : k ≫ b = a ≫ k') :
    pushout k a ⟶ X' := pushout.desc b k' hk

/-- The small lemma on the canonical Q,V, preserving the supplied original d. -/
theorem reedy_of_relative {A X Z P A' X' Z' P' : SSet.{u}}
    (k : A ⟶ X) (ell : A ⟶ Z) (r : X ⟶ P) (s : Z ⟶ P)
    (k' : A' ⟶ X') (ell' : A' ⟶ Z') (r' : X' ⟶ P') (s' : Z' ⟶ P')
    (sq0 : IsPushout k ell r s) (sq1 : IsPushout k' ell' r' s')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (d : P ⟶ P')
    (hk : k ≫ b = a ≫ k') (he : ell ≫ c = a ≫ ell')
    (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s')
    [Cofibration a] [Cofibration c] [Cofibration (relativeMap k k' a b hk)]
    (ha : GW a) (hb : GW b) (hc : GW c) : GW d := by
  let v : pushout k a ⟶ pushout s c :=
    pushout.desc (r ≫ pushout.inl s c) (ell' ≫ pushout.inr s c) (by
      rw [← Category.assoc, sq0.w, Category.assoc, pushout.condition, ← Category.assoc, he]
      simp only [Category.assoc])
  let nu : pushout s c ⟶ P' := pushout.desc d s' hs
  exact reedy_geometric k ell r s k' ell' r' s' sq0 sq1 a b c d he hr hs
    (pushout.inl k a) (pushout.inr k a) (IsPushout.of_hasPushout k a)
    (pushout.inl s c) (pushout.inr s c) (IsPushout.of_hasPushout s c)
    (relativeMap k k' a b hk) v nu
    (by simp [relativeMap]) (by simp [relativeMap])
    (by simp [v]) (by simp [v]) (by simp [nu]) (by simp [nu]) ha hb hc

end
end DaggerSSetGluing
