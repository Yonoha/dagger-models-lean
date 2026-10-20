import OrdinaryAnodyneTensor
import IinjBridge
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-! The original geometric weak equivalences are preserved by arbitrary SSet products. -/

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

set_option autoImplicit false

universe u

namespace DaggerSSetProductGeometric

abbrev GW {X Y : SSet.{u}} (g : X ⟶ Y) : Prop :=
  SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map g))

lemma geometric_iff_weakEquivalence {X Y : SSet.{u}} (g : X ⟶ Y) :
    GW g ↔ WeakEquivalence g :=
  (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric g).symm

/-- This chooses the existing full Brown factorization; no new factorization is substituted. -/
noncomputable def brown {X Y : SSet.{u}} (g : X ⟶ Y) : CofibrantBrownFactorization g :=
  Classical.choice inferInstance

lemma brown_fac {X Y : SSet.{u}} (g : X ⟶ Y) : (brown g).i ≫ (brown g).p = g :=
  (brown g).fac

lemma brown_section {X Y : SSet.{u}} (g : X ⟶ Y) :
    (brown g).s ≫ (brown g).p = 𝟙 Y := (brown g).s_p

lemma brown_i_anodyne {X Y : SSet.{u}} (g : X ⟶ Y) (hg : GW g)
    (h : CofibrantBrownFactorization g) : SSet.anodyneExtensions h.i := by
  letI : WeakEquivalence g := (geometric_iff_weakEquivalence g).1 hg
  exact (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration h.i).2
    (mem_trivialCofibrations h.i)

lemma brown_s_anodyne {X Y : SSet.{u}} (g : X ⟶ Y)
    (h : CofibrantBrownFactorization g) : SSet.anodyneExtensions h.s :=
  (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration h.s).2
    (mem_trivialCofibrations h.s)

lemma whiskerLeft_fac {X Y : SSet.{u}} (g : X ⟶ Y)
    (h : CofibrantBrownFactorization g) (H : SSet.{u}) :
    (H ◁ h.i) ≫ (H ◁ h.p) = H ◁ g := by
  rw [← whiskerLeft_comp, h.fac]

lemma whiskerLeft_section {X Y : SSet.{u}} (g : X ⟶ Y)
    (h : CofibrantBrownFactorization g) (H : SSet.{u}) :
    (H ◁ h.s) ≫ (H ◁ h.p) = 𝟙 (H ⊗ Y) := by
  rw [← whiskerLeft_comp, h.s_p, whiskerLeft_id]

lemma whiskerRight_fac {X Y : SSet.{u}} (g : X ⟶ Y)
    (h : CofibrantBrownFactorization g) (H : SSet.{u}) :
    (h.i ▷ H) ≫ (h.p ▷ H) = g ▷ H := by
  rw [← comp_whiskerRight, h.fac]

lemma whiskerRight_section {X Y : SSet.{u}} (g : X ⟶ Y)
    (h : CofibrantBrownFactorization g) (H : SSet.{u}) :
    (h.s ▷ H) ≫ (h.p ▷ H) = 𝟙 (Y ⊗ H) := by
  rw [← comp_whiskerRight, h.s_p, id_whiskerRight]

lemma whiskerLeft_p_weakEquivalence {X Y : SSet.{u}} (g : X ⟶ Y)
    (h : CofibrantBrownFactorization g) (H : SSet.{u}) :
    WeakEquivalence (H ◁ h.p) := by
  have hs := DaggerOrdinaryAnodyneTensor.whiskerLeft h.s (brown_s_anodyne g h) H
  have ht := (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1 hs
  letI : WeakEquivalence (H ◁ h.s) := (mem_trivialCofibrations_iff _).1 ht |>.2
  exact weakEquivalence_of_precomp_of_fac (whiskerLeft_section g h H)

lemma whiskerRight_p_weakEquivalence {X Y : SSet.{u}} (g : X ⟶ Y)
    (h : CofibrantBrownFactorization g) (H : SSet.{u}) :
    WeakEquivalence (h.p ▷ H) := by
  have hs := DaggerOrdinaryAnodyneTensor.whiskerRight h.s (brown_s_anodyne g h) H
  have ht := (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1 hs
  letI : WeakEquivalence (h.s ▷ H) := (mem_trivialCofibrations_iff _).1 ht |>.2
  exact weakEquivalence_of_precomp_of_fac (whiskerRight_section g h H)

lemma whiskerLeft_geometric {X Y : SSet.{u}} (g : X ⟶ Y) (hg : GW g) (H : SSet.{u}) :
    GW (H ◁ g) := by
  let h := brown g
  have hi := DaggerOrdinaryAnodyneTensor.whiskerLeft h.i (brown_i_anodyne g hg h) H
  have ht := (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1 hi
  letI : WeakEquivalence (H ◁ h.i) := (mem_trivialCofibrations_iff _).1 ht |>.2
  letI : WeakEquivalence (H ◁ h.p) := whiskerLeft_p_weakEquivalence g h H
  apply (geometric_iff_weakEquivalence _).2
  rw [← whiskerLeft_fac g h H]
  infer_instance

lemma whiskerRight_geometric {X Y : SSet.{u}} (g : X ⟶ Y) (hg : GW g) (H : SSet.{u}) :
    GW (g ▷ H) := by
  let h := brown g
  have hi := DaggerOrdinaryAnodyneTensor.whiskerRight h.i (brown_i_anodyne g hg h) H
  have ht := (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1 hi
  letI : WeakEquivalence (h.i ▷ H) := (mem_trivialCofibrations_iff _).1 ht |>.2
  letI : WeakEquivalence (h.p ▷ H) := whiskerRight_p_weakEquivalence g h H
  apply (geometric_iff_weakEquivalence _).2
  rw [← whiskerRight_fac g h H]
  infer_instance

lemma tensorMap_geometric {X Y A B : SSet.{u}} (g : X ⟶ Y) (h : A ⟶ B)
    (hg : GW g) (hh : GW h) : GW (g ⊗ₘ h) := by
  letI : WeakEquivalence (g ▷ A) :=
    (geometric_iff_weakEquivalence _).1 (whiskerRight_geometric g hg A)
  letI : WeakEquivalence (Y ◁ h) :=
    (geometric_iff_weakEquivalence _).1 (whiskerLeft_geometric h hh Y)
  apply (geometric_iff_weakEquivalence _).2
  rw [tensorHom_def]
  infer_instance

lemma identity_geometric (X : SSet.{u}) : GW (𝟙 X) :=
  (geometric_iff_weakEquivalence _).2 inferInstance

/-- The exact parenthesization of the ordinary word tuple factors is retained. -/
lemma wordStep_geometric {X Y A B : SSet.{u}} (g : X ⟶ Y) (h : A ⟶ B)
    (L : SSet.{u}) (hg : GW g) (hh : GW h) : GW ((g ⊗ₘ 𝟙 L) ⊗ₘ h) :=
  tensorMap_geometric _ h (tensorMap_geometric g (𝟙 L) hg (identity_geometric L)) hh

def finiteTensorSource : List (Arrow SSet.{u}) → SSet.{u}
  | [] => 𝟙_ SSet.{u}
  | f :: fs => f.left ⊗ finiteTensorSource fs

def finiteTensorTarget : List (Arrow SSet.{u}) → SSet.{u}
  | [] => 𝟙_ SSet.{u}
  | f :: fs => f.right ⊗ finiteTensorTarget fs

def finiteTensorMap (fs : List (Arrow SSet.{u})) :
    finiteTensorSource fs ⟶ finiteTensorTarget fs :=
  match fs with
  | [] => 𝟙 (𝟙_ SSet.{u})
  | f :: fs => f.hom ⊗ₘ finiteTensorMap fs

lemma finiteTensorMap_geometric (fs : List (Arrow SSet.{u}))
    (hfs : ∀ f ∈ fs, GW f.hom) : GW (finiteTensorMap fs) := by
  induction fs with
  | nil => exact identity_geometric _
  | cons f fs ih =>
    exact tensorMap_geometric f.hom (finiteTensorMap fs)
      (hfs f (by simp)) (ih (fun k hk ↦ hfs k (by simp [hk])))

end DaggerSSetProductGeometric
