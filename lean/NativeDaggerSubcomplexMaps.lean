import NativeDaggerSubcomplexRestriction

/-! Original dagger maps restrict to stable subcomplexes with every original value retained. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeDaggerSubcomplexRestriction
universe u
namespace DaggerNativeDaggerSubcomplexMaps
noncomputable section

def map {X Y : DaggerSSet.{u}} (A : X.toSSet.Subcomplex) (B : Y.toSSet.Subcomplex)
    (hA : ∀ q (s : (A : SSet.{u}).obj q), X.dagger.app q s.val ∈ A.obj q)
    (hB : ∀ q (s : (B : SSet.{u}).obj q), Y.dagger.app q s.val ∈ B.obj q)
    (f : X ⟶ Y)
    (hf : ∀ q (s : (A : SSet.{u}).obj q), f.hom.app q s.val ∈ B.obj q) :
    restricted X A hA ⟶ restricted Y B hB where
  hom :=
    { app := fun q s ↦ ⟨f.hom.app q s.val, hf q s⟩
      naturality := by
        intro q r α
        funext s
        apply Subtype.ext
        exact congrFun (f.hom.naturality α) s.val }
  comm := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app f.comm q) s.val

theorem map_val {X Y : DaggerSSet.{u}} (A : X.toSSet.Subcomplex) (B : Y.toSSet.Subcomplex)
    (hA : ∀ q (s : (A : SSet.{u}).obj q), X.dagger.app q s.val ∈ A.obj q)
    (hB : ∀ q (s : (B : SSet.{u}).obj q), Y.dagger.app q s.val ∈ B.obj q)
    (f : X ⟶ Y) (hf : ∀ q (s : (A : SSet.{u}).obj q), f.hom.app q s.val ∈ B.obj q)
    (q : SimplexCategoryᵒᵖ) (s : (A : SSet.{u}).obj q) :
    ((map A B hA hB f hf).hom.app q s).val = f.hom.app q s.val := rfl

theorem inclusion_natural {X Y : DaggerSSet.{u}}
    (A : X.toSSet.Subcomplex) (B : Y.toSSet.Subcomplex)
    (hA : ∀ q (s : (A : SSet.{u}).obj q), X.dagger.app q s.val ∈ A.obj q)
    (hB : ∀ q (s : (B : SSet.{u}).obj q), Y.dagger.app q s.val ∈ B.obj q)
    (f : X ⟶ Y) (hf : ∀ q (s : (A : SSet.{u}).obj q), f.hom.app q s.val ∈ B.obj q) :
    map A B hA hB f hf ≫ inclusion Y B hB = inclusion X A hA ≫ f := by
  apply DaggerSSet.Hom.ext
  apply NatTrans.ext
  funext q s
  rfl

theorem map_id {X : DaggerSSet.{u}} (A : X.toSSet.Subcomplex)
    (hA : ∀ q (s : (A : SSet.{u}).obj q), X.dagger.app q s.val ∈ A.obj q)
    (hi : ∀ q (s : (A : SSet.{u}).obj q), (𝟙 X : X ⟶ X).hom.app q s.val ∈ A.obj q) :
    map A A hA hA (𝟙 X) hi = 𝟙 (restricted X A hA) := by
  apply DaggerSSet.Hom.ext
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  rfl

theorem map_comp {X Y Z : DaggerSSet.{u}}
    (A : X.toSSet.Subcomplex) (B : Y.toSSet.Subcomplex) (C : Z.toSSet.Subcomplex)
    (hA : ∀ q (s : (A : SSet.{u}).obj q), X.dagger.app q s.val ∈ A.obj q)
    (hB : ∀ q (s : (B : SSet.{u}).obj q), Y.dagger.app q s.val ∈ B.obj q)
    (hC : ∀ q (s : (C : SSet.{u}).obj q), Z.dagger.app q s.val ∈ C.obj q)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ q (s : (A : SSet.{u}).obj q), f.hom.app q s.val ∈ B.obj q)
    (hg : ∀ q (s : (B : SSet.{u}).obj q), g.hom.app q s.val ∈ C.obj q)
    (hfg : ∀ q (s : (A : SSet.{u}).obj q), (f ≫ g).hom.app q s.val ∈ C.obj q) :
    map A C hA hC (f ≫ g) hfg = map A B hA hB f hf ≫ map B C hB hC g hg := by
  apply DaggerSSet.Hom.ext
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  rfl

end
end DaggerNativeDaggerSubcomplexMaps
