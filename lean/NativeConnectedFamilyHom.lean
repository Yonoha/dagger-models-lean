import NativeCoproductConnectedFactor

/-! Maps from a nonempty preconnected parameter retain the exact original family summand. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerOriginalProductGadget DaggerNativeCoproductConnectedFactor
universe u
namespace DaggerNativeConnectedFamilyHom
noncomputable section

instance family_inclusion_mono {I : Type u} (X : I → SSet.{u}) (i : I) :
    Mono (familyInclusion X i) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro n
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro a b h
  exact eq_of_heq (Sigma.mk.inj h).2

theorem family_factor_fixed_summand {I : Type u} (X : I → SSet.{u}) (i : I)
    {K : SSet.{u}} [Subsingleton K.π₀] (f : K ⟶ familySSet X)
    (v : K _⦋0⦌) (a : (X i) _⦋0⦌) (hv : f.app (op ⦋0⦌) v = ⟨i, a⟩) :
    ∃ g : K ⟶ X i, g ≫ familyInclusion X i = f := by
  have hi : familyInclusion X i ≫ (familySigmaIso X).inv = Sigma.ι X i := by
    rw [← familySigmaIso_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hz : (f ≫ (familySigmaIso X).inv).app (op ⦋0⦌) v =
      (Sigma.ι X i).app (op ⦋0⦌) a := by
    change (familySigmaIso X).inv.app (op ⦋0⦌) (f.app (op ⦋0⦌) v) = _
    rw [hv]
    exact congrFun (NatTrans.congr_app hi (op ⦋0⦌)) a
  obtain ⟨g, hg⟩ := connected_factor_fixed_summand X i (f ≫ (familySigmaIso X).inv) v a hz
  refine ⟨g, ?_⟩
  calc
    g ≫ familyInclusion X i = (g ≫ Sigma.ι X i) ≫ (familySigmaIso X).hom := by
      rw [Category.assoc, familySigmaIso_ι]
    _ = (f ≫ (familySigmaIso X).inv) ≫ (familySigmaIso X).hom := by rw [hg]
    _ = f := by simp

def familyHomMap {I : Type u} (X : I → SSet.{u}) (K : SSet.{u}) :
    (Σ i, K ⟶ X i) → (K ⟶ familySSet X) := fun f ↦ f.2 ≫ familyInclusion X f.1

theorem familyHomMap_bijective {I : Type u} (X : I → SSet.{u})
    {K : SSet.{u}} [Subsingleton K.π₀] (v : K _⦋0⦌) :
    Function.Bijective (familyHomMap X K) := by
  constructor
  · rintro ⟨i, f⟩ ⟨j, g⟩ h
    have hc : (⟨i, f.app (op ⦋0⦌) v⟩ : Σ i, (X i) _⦋0⦌) =
        ⟨j, g.app (op ⦋0⦌) v⟩ := congrFun (NatTrans.congr_app h (op ⦋0⦌)) v
    have hij := (Sigma.mk.inj hc).1
    cases hij
    have hfg : f = g := (cancel_mono (familyInclusion X i)).mp h
    cases hfg
    rfl
  · intro f
    obtain ⟨g, hg⟩ := family_factor_fixed_summand X (f.app (op ⦋0⦌) v).1 f v
      (f.app (op ⦋0⦌) v).2 rfl
    exact ⟨⟨_, g⟩, hg⟩

def familyHomEquiv {I : Type u} (X : I → SSet.{u})
    {K : SSet.{u}} [Subsingleton K.π₀] (v : K _⦋0⦌) :
    (Σ i, K ⟶ X i) ≃ (K ⟶ familySSet X) :=
  Equiv.ofBijective (familyHomMap X K) (familyHomMap_bijective X v)

theorem familyHomEquiv_parameter {I : Type u} (X : I → SSet.{u})
    {K L : SSet.{u}} [Subsingleton K.π₀] [Subsingleton L.π₀]
    (v : K _⦋0⦌) (w : L _⦋0⦌) (f : L ⟶ K) (g : Σ i, K ⟶ X i) :
    familyHomEquiv X w ⟨g.1, f ≫ g.2⟩ = f ≫ familyHomEquiv X v g := by
  change (f ≫ g.2) ≫ familyInclusion X g.1 = f ≫ g.2 ≫ familyInclusion X g.1
  exact Category.assoc _ _ _

end
end DaggerNativeConnectedFamilyHom
