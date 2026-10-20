import OriginalFlagDescentBeadCondition
import OriginalFlagFlankedCodeEpi

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}
variable {P Q R : NecklacesOver X a b}
variable (F : Flag.{u} P.code n) (G : Flag.{u} Q.code n) (H : Flag.{u} R.code n)
variable (f : P ⟶ Q) (g : P ⟶ R)
variable (hf : NecklaceCode.Flag.map f.hom F = G)
variable (hg : NecklaceCode.Flag.map g.hom F = H)
variable (hF : Flanked F) (hG : Flanked G) (hH : Flanked H)
variable (hQ : ∀ d : Q.code.Bead, beadElement Q d ∈ X.nonDegenerate d.length)

/-- Endpoints follow from l(g(v))=f(v), never from an endpoint property of the section. -/
def flankedDescentCodeHom : NecklaceCode.Hom.{u} R.code Q.code where
  map := orderLift (T := R.code) (U := Q.code)
    (flankedDescentOrder F H f g hg hF hH)
    (flankedDescentOrder_beadCondition F G H f g hf hg hF hG hH hQ)
  first := by
    apply Q.code.verticesEquiv.injective
    have h := orderLift_vertices (T := R.code) (U := Q.code)
      (flankedDescentOrder F H f g hg hF hH)
      (flankedDescentOrder_beadCondition F G H f g hf hg hF hG hH hQ)
      (ULift.up 0 : Vertices.{u} R.code)
    rw [flankedDescentOrder_first F G H f g hf hg hF hG hH hQ] at h
    simpa only [mapVertices, first, Equiv.apply_symm_apply] using h
  last := by
    apply Q.code.verticesEquiv.injective
    have h := orderLift_vertices (T := R.code) (U := Q.code)
      (flankedDescentOrder F H f g hg hF hH)
      (flankedDescentOrder_beadCondition F G H f g hf hg hF hG hH hQ)
      (ULift.up (Fin.last R.code.len) : Vertices.{u} R.code)
    rw [flankedDescentOrder_last F G H f g hf hg hF hG hH hQ] at h
    simpa only [mapVertices, last, Equiv.apply_symm_apply] using h

theorem flankedDescentCodeHom_vertices (v : Vertices.{u} R.code) :
    mapVertices (flankedDescentCodeHom F G H f g hf hg hF hG hH hQ).map v =
      ULift.up (flankedDescentOrder F H f g hg hF hH v.down) :=
  orderLift_vertices (T := R.code) (U := Q.code)
    (flankedDescentOrder F H f g hg hF hH)
    (flankedDescentOrder_beadCondition F G H f g hf hg hF hG hH hQ) v

/-- Equality of whole code maps is proved only into the literal necklace Q. -/
theorem flankedDescentCodeHom_factor :
    g.hom.map ≫ (flankedDescentCodeHom F G H f g hf hg hF hG hH hQ).map =
      f.hom.map := by
  apply hom_ext_vertices
  funext v
  rw [mapVertices_comp, Function.comp_apply, flankedDescentCodeHom_vertices]
  apply ULift.ext
  change flankedDescentOrder F H f g hg hF hH (orderMap g.hom.map v.down) =
    orderMap f.hom.map v.down
  exact flankedDescentOrder_factor F G H f g hf hg hF hG hH hQ v.down

/-- The original over-X triangle cancels the full all-degree epi, not merely a vertex map. -/
def flankedDescentOver : R ⟶ Q where
  hom := flankedDescentCodeHom F G H f g hf hg hF hG hH hQ
  w := by
    letI : Epi g.hom.map := flanked_code_epi F H g.hom hg hF hH
    apply (cancel_epi g.hom.map).mp
    rw [← Category.assoc, flankedDescentCodeHom_factor, f.w, g.w]

theorem flankedDescentOver_triangle :
    (flankedDescentOver F G H f g hf hg hF hG hH hQ).hom.map ≫ Q.map = R.map :=
  (flankedDescentOver F G H f g hf hg hF hG hH hQ).w

theorem flankedDescentOver_factor :
    g ≫ flankedDescentOver F G H f g hf hg hF hG hH hQ = f := by
  apply NecklacesOver.Hom.ext
  apply NecklaceCode.Hom.ext
  exact flankedDescentCodeHom_factor F G H f g hf hg hF hG hH hQ

/-- The entire original flag descends, including every intermediate layer. -/
theorem flankedDescentOver_flag :
    NecklaceCode.Flag.map
      (flankedDescentOver F G H f g hf hg hF hG hH hQ).hom H = G := by
  let l := flankedDescentOver F G H f g hf hg hF hG hH hQ
  have hc : NecklaceCode.Hom.comp g.hom l.hom = f.hom :=
    NecklaceCode.Hom.ext (flankedDescentCodeHom_factor F G H f g hf hg hF hG hH hQ)
  calc
    NecklaceCode.Flag.map l.hom H =
        NecklaceCode.Flag.map l.hom (NecklaceCode.Flag.map g.hom F) :=
      congrArg (NecklaceCode.Flag.map l.hom) hg.symm
    _ = NecklaceCode.Flag.map (NecklaceCode.Hom.comp g.hom l.hom) F :=
      (NecklaceCode.Flag.map_comp g.hom l.hom F).symm
    _ = G := by rw [hc, hf]

theorem flankedDescentOver_flag_image (i : Fin (n + 1)) :
    mapVertices (flankedDescentOver F G H f g hf hg hF hG hH hQ).hom.map ''
      H.chain i = G.chain i :=
  congrArg (fun K : Flag.{u} Q.code n ↦ K.chain i)
    (flankedDescentOver_flag F G H f g hf hg hF hG hH hQ)

theorem flankedDescentOver_operator {s t : SimplexCategoryᵒᵖ} (α : s ⟶ t) :
    R.code.toSSet.map α ≫
        (flankedDescentOver F G H f g hf hg hF hG hH hQ).hom.map.app t =
      (flankedDescentOver F G H f g hf hg hF hG hH hQ).hom.map.app s ≫
        Q.code.toSSet.map α :=
  (flankedDescentOver F G H f g hf hg hF hG hH hQ).hom.map.naturality α

end

end DaggerOriginalFlagFlankification
