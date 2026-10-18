import ChosenFlagHomColimit

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

variable {X Y Z : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- The same necklace and full flags, with only its original map postcomposed. -/
def flagHomMap (f : X ⟶ Y) : flagHom X a b ⟶ flagHom Y (f.app _ a) (f.app _ b) where
  app q := Quot.map (fun p ↦ ⟨(NecklacesOver.postcomp f).obj p.1, p.2⟩) (by
    rintro ⟨P, F⟩ ⟨Q, G⟩ ⟨h, he⟩
    exact ⟨(NecklacesOver.postcomp f).map h, he⟩)
  naturality _ _ _ := by
    funext t
    induction t using Quot.ind with | _ t
    rfl

theorem flagHomMap_leg (f : X ⟶ Y) (P : NecklacesOver X a b) :
    flagLeg X a b P ≫ flagHomMap f =
      flagLeg Y (f.app _ a) (f.app _ b) ((NecklacesOver.postcomp f).obj P) := rfl

theorem flagHomMap_app_mk (f : X ⟶ Y) (q : SimplexCategoryᵒᵖ) (p : RawFlag X a b q) :
    (flagHomMap f).app q (Quot.mk _ p) =
      Quot.mk _ ⟨(NecklacesOver.postcomp f).obj p.1, p.2⟩ := rfl

theorem postcomp_id_obj (P : NecklacesOver X a b) :
    (NecklacesOver.postcomp (𝟙 X)).obj P = P := by
  cases P
  simp [NecklacesOver.postcomp]

theorem postcomp_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (P : NecklacesOver X a b) :
    (NecklacesOver.postcomp (f ≫ g)).obj P =
      (NecklacesOver.postcomp g).obj ((NecklacesOver.postcomp f).obj P) := by
  cases P
  simp [NecklacesOver.postcomp, Category.assoc]

theorem flagHomMap_id : flagHomMap (a := a) (b := b) (𝟙 X) = 𝟙 (flagHom X a b) := by
  ext q t
  induction t using Quot.ind with | _ t
  apply congrArg (Quot.mk _)
  apply Sigma.ext (postcomp_id_obj t.1)
  cases t with | mk P F
  cases P
  simp

theorem flagHomMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    flagHomMap (a := a) (b := b) (f ≫ g) = flagHomMap f ≫ flagHomMap g := by
  ext q t
  induction t using Quot.ind with | _ t
  apply congrArg (Quot.mk _)
  apply Sigma.ext (postcomp_comp_obj f g t.1)
  cases t with | mk P F
  cases P
  simp [NecklacesOver.postcomp]

end

end DaggerChosenRigidificationNecklace
