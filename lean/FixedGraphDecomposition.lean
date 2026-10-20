import FixedGraphCore
import C2InvolutionBridge
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.SetTheory.Cardinal.Order

/-! The full fixed-object graph decomposition in Part I `bg.lem.gph-decomposition`.
The auxiliary order is on the original `O`. The inverse is exactly the manuscript Ψ.
-/

open CategoryTheory DaggerModels
open FixedDaggerSimplicialGraph

universe u

namespace DaggerFixedGraph

variable (O : Type u) [LinearOrder O]

abbrev Upper := {p : O × O // p.1 < p.2}

abbrev Parameters := (Upper O → SSet.{u}) × (O → Action SSet.{u} C2)

variable {O}

def forwardObj (G : FixedDaggerSimplicialGraph O) : Parameters O :=
  (fun p ↦ G.Hom p.1.1 p.1.2,
    fun x ↦ involutionAction (G.Hom x x) (G.dagger x x) (G.dagger_involutive x x))

def forwardMap {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    forwardObj G ⟶ forwardObj H :=
  (fun p ↦ f.map p.1.1 p.1.2,
    fun x ↦ involutionActionMap _ _ (G.dagger_involutive x x) (H.dagger_involutive x x)
      (f.map x x) (f.map_dagger x x).symm)

def forward : FixedDaggerSimplicialGraph O ⥤ Parameters O where
  obj := forwardObj
  map := forwardMap
  map_id _ := rfl
  map_comp _ _ := rfl

def inverseHom (P : Parameters O) (x y : O) : SSet.{u} :=
  if hxy : x < y then P.1 ⟨(x,y), hxy⟩
  else if hyx : y < x then P.1 ⟨(y,x), hyx⟩
  else (P.2 x).V

def inverseDagger (P : Parameters O) (x y : O) : inverseHom P x y ⟶ inverseHom P y x := by
  by_cases hxy : x < y
  · simpa only [inverseHom, dif_pos hxy, dif_neg (not_lt_of_gt hxy)] using
      (𝟙 (P.1 ⟨(x,y), hxy⟩))
  · by_cases hyx : y < x
    · simpa only [inverseHom, dif_neg hxy, dif_pos hyx] using
        (𝟙 (P.1 ⟨(y,x), hyx⟩))
    · have h : x = y := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
      subst y
      simpa only [inverseHom, dif_neg (lt_irrefl x)] using (P.2 x).ρ flip

theorem inverseDagger_involutive (P : Parameters O) (x y : O) :
    inverseDagger P x y ≫ inverseDagger P y x = 𝟙 (inverseHom P x y) := by
  by_cases hxy : x < y
  · have hx : inverseHom P x y = P.1 ⟨(x,y), hxy⟩ := by simp [inverseHom, hxy]
    have hy : inverseHom P y x = P.1 ⟨(x,y), hxy⟩ := by
      simp [inverseHom, hxy, not_lt_of_gt hxy]
    have hd : inverseDagger P x y ≍ 𝟙 (P.1 ⟨(x,y), hxy⟩) := by
      simp [inverseDagger, hxy]
    have hd' : inverseDagger P y x ≍ 𝟙 (P.1 ⟨(x,y), hxy⟩) := by
      simp [inverseDagger, hxy, not_lt_of_gt hxy]
    apply eq_of_heq
    exact (heq_comp hx hy hx hd hd').trans
      ((heq_of_eq (Category.id_comp _)).trans (congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) hx).symm)
  · by_cases hyx : y < x
    · have hx : inverseHom P x y = P.1 ⟨(y,x), hyx⟩ := by simp [inverseHom, hxy, hyx]
      have hy : inverseHom P y x = P.1 ⟨(y,x), hyx⟩ := by simp [inverseHom, hyx]
      have hd : inverseDagger P x y ≍ 𝟙 (P.1 ⟨(y,x), hyx⟩) := by
        simp [inverseDagger, hxy, hyx]
      have hd' : inverseDagger P y x ≍ 𝟙 (P.1 ⟨(y,x), hyx⟩) := by
        simp [inverseDagger, hyx]
      apply eq_of_heq
      exact (heq_comp hx hy hx hd hd').trans
        ((heq_of_eq (Category.id_comp _)).trans (congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) hx).symm)
    · have h : x = y := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
      subst y
      have hx : inverseHom P x x = (P.2 x).V := by simp [inverseHom]
      have hd : inverseDagger P x x ≍ (P.2 x).ρ flip := by simp [inverseDagger]
      apply eq_of_heq
      exact (heq_comp hx hx hx hd hd).trans
        ((heq_of_eq (action_flip_involutive (P.2 x))).trans
          (congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) hx).symm)

def inverseObj (P : Parameters O) : FixedDaggerSimplicialGraph O where
  Hom := inverseHom P
  dagger := inverseDagger P
  dagger_involutive := inverseDagger_involutive P

def inverseMapComponent {P Q : Parameters O} (f : P ⟶ Q) (x y : O) :
    inverseHom P x y ⟶ inverseHom Q x y := by
  by_cases hxy : x < y
  · simpa only [inverseHom, dif_pos hxy] using f.1 ⟨(x,y), hxy⟩
  · by_cases hyx : y < x
    · simpa only [inverseHom, dif_neg hxy, dif_pos hyx] using f.1 ⟨(y,x), hyx⟩
    · simpa only [inverseHom, dif_neg hxy, dif_neg hyx] using (f.2 x).hom

theorem inverseMapComponent_dagger {P Q : Parameters O} (f : P ⟶ Q) (x y : O) :
    inverseMapComponent f x y ≫ inverseDagger Q x y =
      inverseDagger P x y ≫ inverseMapComponent f y x := by
  by_cases hxy : x < y
  · have hp : inverseHom P x y = P.1 ⟨(x,y), hxy⟩ := by simp [inverseHom, hxy]
    have hp' : inverseHom P y x = P.1 ⟨(x,y), hxy⟩ := by simp [inverseHom, hxy, not_lt_of_gt hxy]
    have hq : inverseHom Q x y = Q.1 ⟨(x,y), hxy⟩ := by simp [inverseHom, hxy]
    have hq' : inverseHom Q y x = Q.1 ⟨(x,y), hxy⟩ := by simp [inverseHom, hxy, not_lt_of_gt hxy]
    have hf : inverseMapComponent f x y ≍ f.1 ⟨(x,y), hxy⟩ := by simp [inverseMapComponent, hxy]
    have hf' : inverseMapComponent f y x ≍ f.1 ⟨(x,y), hxy⟩ := by
      simp [inverseMapComponent, hxy, not_lt_of_gt hxy]
    have hd : inverseDagger P x y ≍ 𝟙 (P.1 ⟨(x,y), hxy⟩) := by simp [inverseDagger, hxy]
    have hd' : inverseDagger Q x y ≍ 𝟙 (Q.1 ⟨(x,y), hxy⟩) := by simp [inverseDagger, hxy]
    apply eq_of_heq
    exact (heq_comp hp hq hq' hf hd').trans
      ((heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)).trans
        (heq_comp hp hp' hq' hd hf').symm)
  · by_cases hyx : y < x
    · have hp : inverseHom P x y = P.1 ⟨(y,x), hyx⟩ := by simp [inverseHom, hxy, hyx]
      have hp' : inverseHom P y x = P.1 ⟨(y,x), hyx⟩ := by simp [inverseHom, hyx]
      have hq : inverseHom Q x y = Q.1 ⟨(y,x), hyx⟩ := by simp [inverseHom, hxy, hyx]
      have hq' : inverseHom Q y x = Q.1 ⟨(y,x), hyx⟩ := by simp [inverseHom, hyx]
      have hf : inverseMapComponent f x y ≍ f.1 ⟨(y,x), hyx⟩ := by
        simp [inverseMapComponent, hxy, hyx]
      have hf' : inverseMapComponent f y x ≍ f.1 ⟨(y,x), hyx⟩ := by simp [inverseMapComponent, hyx]
      have hd : inverseDagger P x y ≍ 𝟙 (P.1 ⟨(y,x), hyx⟩) := by simp [inverseDagger, hxy, hyx]
      have hd' : inverseDagger Q x y ≍ 𝟙 (Q.1 ⟨(y,x), hyx⟩) := by simp [inverseDagger, hxy, hyx]
      apply eq_of_heq
      exact (heq_comp hp hq hq' hf hd').trans
        ((heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)).trans
          (heq_comp hp hp' hq' hd hf').symm)
    · have h : x = y := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
      subst y
      have hp : inverseHom P x x = (P.2 x).V := by simp [inverseHom]
      have hq : inverseHom Q x x = (Q.2 x).V := by simp [inverseHom]
      have hf : inverseMapComponent f x x ≍ (f.2 x).hom := by simp [inverseMapComponent]
      have hd : inverseDagger P x x ≍ (P.2 x).ρ flip := by simp [inverseDagger]
      have hd' : inverseDagger Q x x ≍ (Q.2 x).ρ flip := by simp [inverseDagger]
      apply eq_of_heq
      exact (heq_comp hp hq hq hf hd').trans
        ((heq_of_eq ((f.2 x).comm flip).symm).trans (heq_comp hp hp hq hd hf).symm)

def inverseMap {P Q : Parameters O} (f : P ⟶ Q) : inverseObj P ⟶ inverseObj Q where
  map := inverseMapComponent f
  map_dagger := inverseMapComponent_dagger f

def inverse : Parameters O ⥤ FixedDaggerSimplicialGraph O where
  obj := inverseObj
  map := inverseMap
  map_id P := by
    apply Map.ext
    funext x y
    change inverseMapComponent (𝟙 P) x y = 𝟙 (inverseHom P x y)
    by_cases hxy : x < y
    · have hx : inverseHom P x y = P.1 ⟨(x,y),hxy⟩ := by simp [inverseHom, hxy]
      have hf : inverseMapComponent (𝟙 P) x y ≍ 𝟙 (P.1 ⟨(x,y),hxy⟩) := by
        simp [inverseMapComponent, hxy]
      exact eq_of_heq (hf.trans (congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) hx).symm)
    · by_cases hyx : y < x
      · have hx : inverseHom P x y = P.1 ⟨(y,x),hyx⟩ := by simp [inverseHom, hxy,hyx]
        have hf : inverseMapComponent (𝟙 P) x y ≍ 𝟙 (P.1 ⟨(y,x),hyx⟩) := by
          simp [inverseMapComponent, hxy,hyx]
        exact eq_of_heq (hf.trans (congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) hx).symm)
      · have hx : inverseHom P x y = (P.2 x).V := by simp [inverseHom, hxy,hyx]
        have hf : inverseMapComponent (𝟙 P) x y ≍ 𝟙 ((P.2 x).V) := by
          simp [inverseMapComponent, hxy,hyx]
        exact eq_of_heq (hf.trans (congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) hx).symm)
  map_comp {P Q R} f g := by
    apply Map.ext
    funext x y
    change inverseMapComponent (f ≫ g) x y = inverseMapComponent f x y ≫ inverseMapComponent g x y
    by_cases hxy : x < y
    · have hp : inverseHom P x y = P.1 ⟨(x,y),hxy⟩ := by simp [inverseHom, hxy]
      have hq : inverseHom Q x y = Q.1 ⟨(x,y),hxy⟩ := by simp [inverseHom, hxy]
      have hr : inverseHom R x y = R.1 ⟨(x,y),hxy⟩ := by simp [inverseHom, hxy]
      have hf : inverseMapComponent f x y ≍ f.1 ⟨(x,y),hxy⟩ := by simp [inverseMapComponent, hxy]
      have hg : inverseMapComponent g x y ≍ g.1 ⟨(x,y),hxy⟩ := by simp [inverseMapComponent, hxy]
      have hfg : inverseMapComponent (f ≫ g) x y ≍ f.1 ⟨(x,y),hxy⟩ ≫ g.1 ⟨(x,y),hxy⟩ := by
        simp [inverseMapComponent, hxy]
      exact eq_of_heq (hfg.trans (heq_comp hp hq hr hf hg).symm)
    · by_cases hyx : y < x
      · have hp : inverseHom P x y = P.1 ⟨(y,x),hyx⟩ := by simp [inverseHom, hxy,hyx]
        have hq : inverseHom Q x y = Q.1 ⟨(y,x),hyx⟩ := by simp [inverseHom, hxy,hyx]
        have hr : inverseHom R x y = R.1 ⟨(y,x),hyx⟩ := by simp [inverseHom, hxy,hyx]
        have hf : inverseMapComponent f x y ≍ f.1 ⟨(y,x),hyx⟩ := by
          simp [inverseMapComponent, hxy,hyx]
        have hg : inverseMapComponent g x y ≍ g.1 ⟨(y,x),hyx⟩ := by
          simp [inverseMapComponent, hxy,hyx]
        have hfg : inverseMapComponent (f ≫ g) x y ≍ f.1 ⟨(y,x),hyx⟩ ≫ g.1 ⟨(y,x),hyx⟩ := by
          simp [inverseMapComponent, hxy,hyx]
        exact eq_of_heq (hfg.trans (heq_comp hp hq hr hf hg).symm)
      · have hp : inverseHom P x y = (P.2 x).V := by simp [inverseHom, hxy,hyx]
        have hq : inverseHom Q x y = (Q.2 x).V := by simp [inverseHom, hxy,hyx]
        have hr : inverseHom R x y = (R.2 x).V := by simp [inverseHom, hxy,hyx]
        have hf : inverseMapComponent f x y ≍ (f.2 x).hom := by simp [inverseMapComponent, hxy,hyx]
        have hg : inverseMapComponent g x y ≍ (g.2 x).hom := by simp [inverseMapComponent, hxy,hyx]
        have hfg : inverseMapComponent (f ≫ g) x y ≍ (f.2 x).hom ≫ (g.2 x).hom := by
          simp [inverseMapComponent, hxy,hyx]
        exact eq_of_heq (hfg.trans (heq_comp hp hq hr hf hg).symm)

def daggerIso (G : FixedDaggerSimplicialGraph O) (x y : O) : G.Hom x y ≅ G.Hom y x where
  hom := G.dagger x y
  inv := G.dagger y x
  hom_inv_id := G.dagger_involutive x y
  inv_hom_id := G.dagger_involutive y x

def unitComponent (G : FixedDaggerSimplicialGraph O) (x y : O) :
    G.Hom x y ≅ (inverseObj (forwardObj G)).Hom x y := by
  by_cases hxy : x < y
  · exact eqToIso (by simp [inverseObj, inverseHom, forwardObj, hxy])
  · by_cases hyx : y < x
    · exact daggerIso G x y ≪≫ eqToIso (by simp [inverseObj, inverseHom, forwardObj, hxy, hyx])
    · have h : x = y := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
      subst y
      exact eqToIso (by simp [inverseObj, inverseHom, forwardObj, involutionAction])

theorem unitComponent_upper (G : FixedDaggerSimplicialGraph O) {x y : O} (hxy : x < y) :
    (unitComponent G x y).hom ≍ 𝟙 (G.Hom x y) := by
  simp [unitComponent, hxy, eqToHom_heq_id_dom]

theorem unitComponent_lower (G : FixedDaggerSimplicialGraph O) {x y : O} (hyx : y < x) :
    (unitComponent G x y).hom ≍ G.dagger x y := by
  simp [unitComponent, hyx, not_lt_of_gt hyx, daggerIso]

theorem unitComponent_diagonal (G : FixedDaggerSimplicialGraph O) (x : O) :
    (unitComponent G x x).hom ≍ 𝟙 (G.Hom x x) := by
  simp [unitComponent, eqToHom_heq_id_dom]

theorem unitComponent_dagger (G : FixedDaggerSimplicialGraph O) (x y : O) :
    (unitComponent G x y).hom ≫ (inverseObj (forwardObj G)).dagger x y =
      G.dagger x y ≫ (unitComponent G y x).hom := by
  by_cases hxy : x < y
  · have hx : inverseHom (forwardObj G) x y = G.Hom x y := by simp [inverseHom, forwardObj, hxy]
    have hy : inverseHom (forwardObj G) y x = G.Hom x y := by
      simp [inverseHom, forwardObj, hxy, not_lt_of_gt hxy]
    have hd : inverseDagger (forwardObj G) x y ≍ 𝟙 (G.Hom x y) := by
      simp [inverseDagger, forwardObj, hxy]
    apply eq_of_heq
    exact (heq_comp rfl hx hy (unitComponent_upper G hxy) hd).trans
      ((heq_of_eq ((Category.id_comp _).trans (G.dagger_involutive x y).symm)).trans
        (heq_comp rfl rfl hy (HEq.refl _) (unitComponent_lower G hxy)).symm)
  · by_cases hyx : y < x
    · have hx : inverseHom (forwardObj G) x y = G.Hom y x := by
        simp [inverseHom, forwardObj, hxy, hyx]
      have hy : inverseHom (forwardObj G) y x = G.Hom y x := by simp [inverseHom, forwardObj, hyx]
      have hd : inverseDagger (forwardObj G) x y ≍ 𝟙 (G.Hom y x) := by
        simp [inverseDagger, forwardObj, hxy, hyx]
      apply eq_of_heq
      exact (heq_comp rfl hx hy (unitComponent_lower G hyx) hd).trans
        (heq_comp rfl rfl hy (HEq.refl _) (unitComponent_upper G hyx)).symm
    · have h : x = y := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
      subst y
      have hx : inverseHom (forwardObj G) x x = G.Hom x x := by
        simp [inverseHom, forwardObj, involutionAction]
      have hd : inverseDagger (forwardObj G) x x ≍ G.dagger x x := by
        simp [inverseDagger, forwardObj, involutionAction_flip]
      apply eq_of_heq
      exact (heq_comp rfl hx hx (unitComponent_diagonal G x) hd).trans
        ((heq_of_eq ((Category.id_comp _).trans (Category.comp_id _).symm)).trans
          (heq_comp rfl rfl hx (HEq.refl _) (unitComponent_diagonal G x)).symm)

def unitGraphIso (G : FixedDaggerSimplicialGraph O) : G ≅ inverseObj (forwardObj G) :=
  FixedDaggerSimplicialGraph.mkIso (unitComponent G) (unitComponent_dagger G)

def unitIso : 𝟭 (FixedDaggerSimplicialGraph O) ≅ forward ⋙ inverse :=
  NatIso.ofComponents (fun G ↦ unitGraphIso (O := O) G) (fun {G H} f ↦ by
    apply Map.ext
    funext x y
    change f.map x y ≫ (unitComponent H x y).hom =
      (unitComponent G x y).hom ≫ inverseMapComponent (forwardMap f) x y
    by_cases hxy : x < y
    · have hg : inverseHom (forwardObj G) x y = G.Hom x y := by
        simp [inverseHom, forwardObj, hxy, involutionAction]
      have hh : inverseHom (forwardObj H) x y = H.Hom x y := by
        simp [inverseHom, forwardObj, hxy, involutionAction]
      have hm : inverseMapComponent (forwardMap f) x y ≍ f.map x y := by
        simp [inverseMapComponent, forwardMap, hxy, involutionActionMap]
      apply eq_of_heq
      exact (heq_comp rfl rfl hh (HEq.refl _) (unitComponent_upper H hxy)).trans
        ((heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)).trans (heq_comp rfl hg
          hh (unitComponent_upper G hxy) hm).symm)
    · by_cases hyx : y < x
      · have hg : inverseHom (forwardObj G) x y = G.Hom y x := by
          simp [inverseHom, forwardObj, hxy, hyx, involutionAction]
        have hh : inverseHom (forwardObj H) x y = H.Hom y x := by
          simp [inverseHom, forwardObj, hxy, hyx, involutionAction]
        have hm : inverseMapComponent (forwardMap f) x y ≍ f.map y x := by
          simp [inverseMapComponent, forwardMap, hxy, hyx, involutionActionMap]
        apply eq_of_heq
        exact (heq_comp rfl rfl hh (HEq.refl _) (unitComponent_lower H hyx)).trans
          ((heq_of_eq (f.map_dagger x y)).trans (heq_comp rfl hg hh (unitComponent_lower G hyx)
            hm).symm)
      · have h : x = y := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
        subst y
        have hg : inverseHom (forwardObj G) x x = G.Hom x x := by
          simp [inverseHom, forwardObj, involutionAction]
        have hh : inverseHom (forwardObj H) x x = H.Hom x x := by
          simp [inverseHom, forwardObj, involutionAction]
        have hm : inverseMapComponent (forwardMap f) x x ≍ f.map x x := by
          simp [inverseMapComponent, forwardMap, involutionActionMap]
        apply eq_of_heq
        exact (heq_comp rfl rfl hh (HEq.refl _) (unitComponent_diagonal H x)).trans
          ((heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)).trans (heq_comp rfl
            hg hh (unitComponent_diagonal G x) hm).symm))

def counitUpperIso (P : Parameters O) (p : Upper O) :
    (forwardObj (inverseObj P)).1 p ≅ P.1 p :=
  eqToIso (by rcases p with ⟨⟨x,y⟩, hxy⟩; simp [forwardObj, inverseObj, inverseHom, hxy])

def counitDiagonalIso (P : Parameters O) (x : O) :
    (forwardObj (inverseObj P)).2 x ≅ P.2 x := by
  let hx : inverseHom P x x = (P.2 x).V := by simp [inverseHom]
  refine Action.mkIso (eqToIso hx) (fun g ↦ ?_)
  rcases c2_cases g with rfl | rfl
  · change 𝟙 (inverseHom P x x) ≫ eqToHom hx = eqToHom hx ≫ (P.2 x).ρ 1
    rw [(P.2 x).ρ.map_one]
    simp
  · change inverseDagger P x x ≫ eqToHom hx = eqToHom hx ≫ (P.2 x).ρ flip
    have hd : inverseDagger P x x ≍ (P.2 x).ρ flip := by simp [inverseDagger]
    apply eq_of_heq
    exact (heq_comp hx hx rfl hd (eqToHom_heq_id_cod _ _ _)).trans
      ((heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)).trans
        (heq_comp hx rfl rfl (eqToHom_heq_id_cod _ _ _) (HEq.refl _)).symm)

theorem counitUpperIso_hom (P : Parameters O) (p : Upper O) :
    (counitUpperIso P p).hom ≍ 𝟙 (P.1 p) := by
  simp [counitUpperIso, eqToHom_heq_id_cod]

theorem counitDiagonalIso_hom (P : Parameters O) (x : O) :
    (counitDiagonalIso P x).hom.hom ≍ 𝟙 (P.2 x).V := by
  simp [counitDiagonalIso, eqToHom_heq_id_cod]

def counitParameterIso (P : Parameters O) : forwardObj (inverseObj P) ≅ P :=
  Iso.prod (Pi.isoMk (counitUpperIso P)) (Pi.isoMk (counitDiagonalIso P))

def counitIso : inverse.{u} (O := O) ⋙ forward.{u} (O := O) ≅ 𝟭 (Parameters O) :=
  NatIso.ofComponents (fun P ↦ counitParameterIso (O := O) P) (fun {P Q} f ↦ by
    apply Prod.ext
    · funext p
      rcases p with ⟨⟨x,y⟩,hxy⟩
      change inverseMapComponent f x y ≫ (counitUpperIso Q ⟨(x,y),hxy⟩).hom =
        (counitUpperIso P ⟨(x,y),hxy⟩).hom ≫ f.1 ⟨(x,y),hxy⟩
      have hp : inverseHom P x y = P.1 ⟨(x,y),hxy⟩ := by simp [inverseHom,hxy]
      have hq : inverseHom Q x y = Q.1 ⟨(x,y),hxy⟩ := by simp [inverseHom,hxy]
      have hf : inverseMapComponent f x y ≍ f.1 ⟨(x,y),hxy⟩ := by simp [inverseMapComponent,hxy]
      apply eq_of_heq
      exact (heq_comp hp hq rfl hf (counitUpperIso_hom Q _)).trans
        ((heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)).trans
          (heq_comp hp rfl rfl (counitUpperIso_hom P _) (HEq.refl _)).symm)
    · funext x
      apply Action.hom_ext
      change inverseMapComponent f x x ≫ (counitDiagonalIso Q x).hom.hom =
        (counitDiagonalIso P x).hom.hom ≫ (f.2 x).hom
      have hp : inverseHom P x x = (P.2 x).V := by simp [inverseHom]
      have hq : inverseHom Q x x = (Q.2 x).V := by simp [inverseHom]
      have hf : inverseMapComponent f x x ≍ (f.2 x).hom := by simp [inverseMapComponent]
      apply eq_of_heq
      exact (heq_comp hp hq rfl hf (counitDiagonalIso_hom Q _)).trans
        ((heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)).trans
          (heq_comp hp rfl rfl (counitDiagonalIso_hom P _) (HEq.refl _)).symm))

def actionDecomposition : FixedDaggerSimplicialGraph O ≌ Parameters O where
  functor := forward.{u} (O := O)
  inverse := inverse.{u} (O := O)
  unitIso := unitIso.{u} (O := O)
  counitIso := counitIso.{u} (O := O)
  functor_unitIso_comp G := by
    apply Prod.ext
    · funext p
      rcases p with ⟨⟨x,y⟩,hxy⟩
      simp [forward, forwardMap, unitIso, unitGraphIso, FixedDaggerSimplicialGraph.mkIso,
        unitComponent, counitIso, counitParameterIso, counitUpperIso, forwardObj,
        inverseObj, inverseHom, hxy]
    · funext x
      apply Action.hom_ext
      simp [forward, forwardMap, unitIso, unitGraphIso, FixedDaggerSimplicialGraph.mkIso,
        unitComponent, counitIso, counitParameterIso, counitDiagonalIso, forwardObj,
        inverseObj, inverseHom, inverseDagger, involutionActionMap]

abbrev FunctorParameters := (Upper O → SSet.{u}) × (O → (SingleObj C2 ⥤ SSet.{u}))

def parametersEquivalence : Parameters O ≌ FunctorParameters (O := O) :=
  CategoryTheory.Equivalence.prod (CategoryTheory.Equivalence.refl (C := Upper O → SSet.{u}))
    (CategoryTheory.Equivalence.pi (fun _ : O ↦ Action.functorCategoryEquivalence SSet.{u} C2))

def decomposition : FixedDaggerSimplicialGraph O ≌ FunctorParameters (O := O) :=
  (actionDecomposition.{u} (O := O)).trans (parametersEquivalence.{u} (O := O))

end DaggerFixedGraph

namespace DaggerFixedGraph

/-- Choose a well-order on the same original object type; no finiteness assumption. -/
noncomputable def chosenLinearOrder (O : Type u) : LinearOrder O :=
  Classical.choose (exists_wellOrder O)

abbrev ChosenFunctorParameters (O : Type u) :=
  @FunctorParameters.{u} O (chosenLinearOrder O)

/-- The complete decomposition for arbitrary `O`, using only a chosen order on `O`. -/
noncomputable def fixedObjectDecomposition (O : Type u) :
    FixedDaggerSimplicialGraph O ≌ ChosenFunctorParameters O :=
  @decomposition.{u} O (chosenLinearOrder O)

end DaggerFixedGraph
