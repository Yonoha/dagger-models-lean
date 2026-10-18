import SSetGluingSpan

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u
namespace DaggerSSetGluing
noncomputable section
set_option autoImplicit false

section MiddleMaps
variable {A X Z A' X' Z' : SSet.{u}}
  {k : A ⟶ X} {ell : A ⟶ Z} {k' : A' ⟶ X'} {ell' : A' ⟶ Z'}
  {a : A ⟶ A'} {b : X ⟶ X'} {c : Z ⟶ Z'}
  (M : Middle k ell k' ell' a b c)

/-- Both span inclusions are componentwise W by their SAME fold equations. -/
theorem Middle.component_geometric (ha : GW a) (hb : GW b) (hc : GW c) :
    GW M.iA ∧ GW M.iX ∧ GW M.iZ ∧ GW M.sA ∧ GW M.sX ∧ GW M.sZ := by
  letI : WeakEquivalence a := (weakEquivalence_iff_GW a).2 ha
  letI : WeakEquivalence b := (weakEquivalence_iff_GW b).2 hb
  letI : WeakEquivalence c := (weakEquivalence_iff_GW c).2 hc
  letI : WeakEquivalence M.pA := M.weak_pA
  letI : WeakEquivalence M.pX := M.weak_pX
  letI : WeakEquivalence M.pZ := M.weak_pZ
  exact ⟨(weakEquivalence_iff_GW M.iA).1 (weakEquivalence_of_postcomp_of_fac M.ia),
    (weakEquivalence_iff_GW M.iX).1 (weakEquivalence_of_postcomp_of_fac M.ib),
    (weakEquivalence_iff_GW M.iZ).1 (weakEquivalence_of_postcomp_of_fac M.ic),
    (weakEquivalence_iff_GW M.sA).1 (weakEquivalence_of_postcomp_of_fac M.sa),
    (weakEquivalence_iff_GW M.sX).1 (weakEquivalence_of_postcomp_of_fac M.sb),
    (weakEquivalence_iff_GW M.sZ).1 (weakEquivalence_of_postcomp_of_fac M.sc)⟩

variable {P P' : SSet.{u}} {r : X ⟶ P} {s : Z ⟶ P}
  {r' : X' ⟶ P'} {s' : Z' ⟶ P'}

def apexI (sq0 : IsPushout k ell r s) : P ⟶ pushout M.Mk M.Mu :=
  sq0.desc (M.iX ≫ pushout.inl M.Mk M.Mu) (M.iZ ≫ pushout.inr M.Mk M.Mu) (by
    rw [← Category.assoc, M.ik, Category.assoc, pushout.condition,
      ← Category.assoc, ← M.ie, Category.assoc])

def apexS (sq1 : IsPushout k' ell' r' s') : P' ⟶ pushout M.Mk M.Mu :=
  sq1.desc (M.sX ≫ pushout.inl M.Mk M.Mu) (M.sZ ≫ pushout.inr M.Mk M.Mu) (by
    rw [← Category.assoc, M.sk, Category.assoc, pushout.condition,
      ← Category.assoc, ← M.se, Category.assoc])

def apexP (sq1 : IsPushout k' ell' r' s') : pushout M.Mk M.Mu ⟶ P' :=
  pushout.desc (M.pX ≫ r') (M.pZ ≫ s') (by
    rw [← Category.assoc, M.pk, Category.assoc, sq1.w,
      ← Category.assoc, ← M.pe, Category.assoc])

@[simp, reassoc] theorem apexI_left (sq0 : IsPushout k ell r s) :
    r ≫ apexI M sq0 = M.iX ≫ pushout.inl M.Mk M.Mu := by simp [apexI]

@[simp, reassoc] theorem apexI_right (sq0 : IsPushout k ell r s) :
    s ≫ apexI M sq0 = M.iZ ≫ pushout.inr M.Mk M.Mu := by simp [apexI]

@[simp, reassoc] theorem apexS_left (sq1 : IsPushout k' ell' r' s') :
    r' ≫ apexS M sq1 = M.sX ≫ pushout.inl M.Mk M.Mu := by simp [apexS]

@[simp, reassoc] theorem apexS_right (sq1 : IsPushout k' ell' r' s') :
    s' ≫ apexS M sq1 = M.sZ ≫ pushout.inr M.Mk M.Mu := by simp [apexS]

@[simp, reassoc] theorem apexP_left (sq1 : IsPushout k' ell' r' s') :
    pushout.inl M.Mk M.Mu ≫ apexP M sq1 = M.pX ≫ r' := by simp [apexP]

@[simp, reassoc] theorem apexP_right (sq1 : IsPushout k' ell' r' s') :
    pushout.inr M.Mk M.Mu ≫ apexP M sq1 = M.pZ ≫ s' := by simp [apexP]

/-- The section is a compatible whole-span section, not independent objectwise sections. -/
theorem apexS_apexP (sq1 : IsPushout k' ell' r' s') :
    apexS M sq1 ≫ apexP M sq1 = 𝟙 P' := by
  apply sq1.hom_ext
  · rw [apexS_left_assoc, apexP_left, ← Category.assoc, M.sb]
    simp
  · rw [apexS_right_assoc, apexP_right, ← Category.assoc, M.sc]
    simp

/-- This composite is precisely the original supplied d, at the original apex P. -/
theorem apexI_apexP (sq0 : IsPushout k ell r s) (sq1 : IsPushout k' ell' r' s')
    (d : P ⟶ P') (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s') :
    apexI M sq0 ≫ apexP M sq1 = d := by
  apply sq0.hom_ext
  · rw [apexI_left_assoc, apexP_left, ← Category.assoc, M.ib, hr]
  · rw [apexI_right_assoc, apexP_right, ← Category.assoc, M.ic, hs]

theorem apexI_geometric (sq0 : IsPushout k ell r s)
    (ha : GW a) (hb : GW b) (hc : GW c) : GW (apexI M sq0) := by
  letI : Cofibration M.iA := M.cof_iA
  letI : Cofibration M.iZ := M.cof_iZ
  letI : Cofibration (relativeMap k M.Mk M.iA M.iX M.ik) := M.cof_qi
  have h := Middle.component_geometric M ha hb hc
  exact reedy_of_relative k ell r s M.Mk M.Mu
    (pushout.inl M.Mk M.Mu) (pushout.inr M.Mk M.Mu) sq0
    (IsPushout.of_hasPushout M.Mk M.Mu) M.iA M.iX M.iZ (apexI M sq0)
    M.ik M.ie (by simp) (by simp) h.1 h.2.1 h.2.2.1

theorem apexS_geometric (sq1 : IsPushout k' ell' r' s')
    (ha : GW a) (hb : GW b) (hc : GW c) : GW (apexS M sq1) := by
  letI : Cofibration M.sA := M.cof_sA
  letI : Cofibration M.sZ := M.cof_sZ
  letI : Cofibration (relativeMap k' M.Mk M.sA M.sX M.sk) := M.cof_qs
  have h := Middle.component_geometric M ha hb hc
  exact reedy_of_relative k' ell' r' s' M.Mk M.Mu
    (pushout.inl M.Mk M.Mu) (pushout.inr M.Mk M.Mu) sq1
    (IsPushout.of_hasPushout M.Mk M.Mu) M.sA M.sX M.sZ (apexS M sq1)
    M.sk M.se (by simp) (by simp) h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
end MiddleMaps

/-- FULL E5: arbitrary supplied pushouts, only k/k' mono, and the SAME original d. -/
theorem geometric_of_pushout_cube {A X Z P A' X' Z' P' : SSet.{u}}
    (k : A ⟶ X) (ell : A ⟶ Z) (r : X ⟶ P) (s : Z ⟶ P)
    (k' : A' ⟶ X') (ell' : A' ⟶ Z') (r' : X' ⟶ P') (s' : Z' ⟶ P')
    (sq0 : IsPushout k ell r s) (sq1 : IsPushout k' ell' r' s')
    [Mono k] [Mono k']
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (d : P ⟶ P')
    (hk : k ≫ b = a ≫ k') (he : ell ≫ c = a ≫ ell')
    (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s')
    (ha : GW a) (hb : GW b) (hc : GW c) : GW d := by
  let M := middle k ell k' ell' a b c hk he
  letI : WeakEquivalence (apexI M sq0) :=
    (weakEquivalence_iff_GW _).2 (apexI_geometric M sq0 ha hb hc)
  letI : WeakEquivalence (apexS M sq1) :=
    (weakEquivalence_iff_GW _).2 (apexS_geometric M sq1 ha hb hc)
  letI : WeakEquivalence (apexP M sq1) :=
    weakEquivalence_of_precomp_of_fac (apexS_apexP M sq1)
  have hd : WeakEquivalence (apexI M sq0 ≫ apexP M sq1) := inferInstance
  rw [apexI_apexP M sq0 sq1 d hr hs] at hd
  exact (weakEquivalence_iff_GW d).1 hd

end
end DaggerSSetGluing
