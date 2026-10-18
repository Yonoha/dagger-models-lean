import OriginalProductBeadExtension
import ChosenNecklacesOver

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalProductGadget

noncomputable section

open DaggerChosenRigidificationNecklace

/-- Both the original necklace and its one-bead completion start at vertex zero. -/
theorem singleIso_first_eq_inclusion_first (T : NecklaceCode) :
    (NecklaceCode.singleIso T.len).hom.app (op ⦋0⦌)
      (NecklaceCode.single T.len).first = T.inclusion.app (op ⦋0⦌) T.first := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [NecklaceCode.singleIso_vertex, ← T.verticesEquiv_down]
  simp only [NecklaceCode.first, Equiv.apply_symm_apply]

/-- Both the original necklace and its one-bead completion end at the last vertex. -/
theorem singleIso_last_eq_inclusion_last (T : NecklaceCode) :
    (NecklaceCode.singleIso T.len).hom.app (op ⦋0⦌)
      (NecklaceCode.single T.len).last = T.inclusion.app (op ⦋0⦌) T.last := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [NecklaceCode.singleIso_vertex, ← T.verticesEquiv_down]
  simp only [NecklaceCode.last, Equiv.apply_symm_apply]
  rfl

theorem ambientSimplexMap_first {T U : NecklaceCode} (h : NecklaceCode.Hom.{u} T U) :
    (ambientSimplexMap h.map).app (op ⦋0⦌)
      (T.inclusion.app (op ⦋0⦌) T.first) = U.inclusion.app (op ⦋0⦌) U.first := by
  have hh := congrFun (NatTrans.congr_app (ambientSimplexMap_fac h.map) (op ⦋0⦌))
    T.first
  change (ambientSimplexMap h.map).app _ (T.inclusion.app _ T.first) =
    U.inclusion.app _ (h.map.app _ T.first) at hh
  rwa [h.first] at hh

theorem ambientSimplexMap_last {T U : NecklaceCode} (h : NecklaceCode.Hom.{u} T U) :
    (ambientSimplexMap h.map).app (op ⦋0⦌)
      (T.inclusion.app (op ⦋0⦌) T.last) = U.inclusion.app (op ⦋0⦌) U.last := by
  have hh := congrFun (NatTrans.congr_app (ambientSimplexMap_fac h.map) (op ⦋0⦌))
    T.last
  change (ambientSimplexMap h.map).app _ (T.inclusion.app _ T.last) =
    U.inclusion.app _ (h.map.app _ T.last) at hh
  rwa [h.last] at hh

def beadSpace (m : ℕ) (dim : Fin m → ℕ) : SSet.{u} :=
  productSpace m (fun i ↦ NecklaceCode.single (dim i))

/-- Complete an over-product necklace to its ambient one-bead simplex. -/
def completeObject (m : ℕ) (dim : Fin m → ℕ)
    {a b : (beadSpace.{u} m dim).obj (op ⦋0⦌)}
    (P : NecklacesOver (beadSpace m dim) a b) :
    NecklacesOver (beadSpace m dim) a b where
  code := NecklaceCode.single P.code.len
  map := (NecklaceCode.singleIso P.code.len).hom ≫
    beadProductExtension P.code m dim P.map
  first := by
    change (beadProductExtension P.code m dim P.map).app _
      ((NecklaceCode.singleIso P.code.len).hom.app _
        (NecklaceCode.single P.code.len).first) = a
    rw [singleIso_first_eq_inclusion_first]
    have h := congrFun
      (NatTrans.congr_app (beadProductExtension_fac P.code m dim P.map) (op ⦋0⦌))
      P.code.first
    change (beadProductExtension P.code m dim P.map).app _
      (P.code.inclusion.app _ P.code.first) = P.map.app _ P.code.first at h
    exact h.trans P.first
  last := by
    change (beadProductExtension P.code m dim P.map).app _
      ((NecklaceCode.singleIso P.code.len).hom.app _
        (NecklaceCode.single P.code.len).last) = b
    rw [singleIso_last_eq_inclusion_last]
    have h := congrFun
      (NatTrans.congr_app (beadProductExtension_fac P.code m dim P.map) (op ⦋0⦌))
      P.code.last
    change (beadProductExtension P.code m dim P.map).app _
      (P.code.inclusion.app _ P.code.last) = P.map.app _ P.code.last at h
    exact h.trans P.last

/-- The inclusion of a necklace into its one-bead completion, over the same product. -/
def toComplete (m : ℕ) (dim : Fin m → ℕ)
    {a b : (beadSpace.{u} m dim).obj (op ⦋0⦌)}
    (P : NecklacesOver (beadSpace m dim) a b) :
    P ⟶ completeObject m dim P where
  hom :=
    { map := P.code.inclusion ≫ (NecklaceCode.singleIso P.code.len).inv
      first := by
        change (NecklaceCode.singleIso P.code.len).inv.app _
          (P.code.inclusion.app _ P.code.first) =
            (NecklaceCode.single P.code.len).first
        have h := congrFun
          (NatTrans.congr_app
            (NecklaceCode.singleIso P.code.len).hom_inv_id (op ⦋0⦌))
          (NecklaceCode.single P.code.len).first
        change (NecklaceCode.singleIso P.code.len).inv.app _
          ((NecklaceCode.singleIso P.code.len).hom.app _
            (NecklaceCode.single P.code.len).first) =
              (NecklaceCode.single P.code.len).first at h
        rw [singleIso_first_eq_inclusion_first] at h
        exact h
      last := by
        change (NecklaceCode.singleIso P.code.len).inv.app _
          (P.code.inclusion.app _ P.code.last) =
            (NecklaceCode.single P.code.len).last
        have h := congrFun
          (NatTrans.congr_app
            (NecklaceCode.singleIso P.code.len).hom_inv_id (op ⦋0⦌))
          (NecklaceCode.single P.code.len).last
        change (NecklaceCode.singleIso P.code.len).inv.app _
          ((NecklaceCode.singleIso P.code.len).hom.app _
            (NecklaceCode.single P.code.len).last) =
              (NecklaceCode.single P.code.len).last at h
        rw [singleIso_last_eq_inclusion_last] at h
        exact h }
  w := by
    change (P.code.inclusion ≫ (NecklaceCode.singleIso P.code.len).inv) ≫
      ((NecklaceCode.singleIso P.code.len).hom ≫
        beadProductExtension P.code m dim P.map) = P.map
    rw [Category.assoc, Iso.inv_hom_id_assoc, beadProductExtension_fac]

/-- The ambient map of an over-product necklace morphism acts on completions. -/
def completeMap (m : ℕ) (dim : Fin m → ℕ)
    {a b : (beadSpace.{u} m dim).obj (op ⦋0⦌)}
    {P Q : NecklacesOver (beadSpace m dim) a b} (h : P ⟶ Q) :
    completeObject m dim P ⟶ completeObject m dim Q where
  hom :=
    { map := (NecklaceCode.singleIso P.code.len).hom ≫
        ambientSimplexMap h.hom.map ≫
        (NecklaceCode.singleIso Q.code.len).inv
      first := by
        change (NecklaceCode.singleIso Q.code.len).inv.app _
          ((ambientSimplexMap h.hom.map).app _
            ((NecklaceCode.singleIso P.code.len).hom.app _
              (NecklaceCode.single P.code.len).first)) =
                (NecklaceCode.single Q.code.len).first
        rw [singleIso_first_eq_inclusion_first, ambientSimplexMap_first h.hom]
        have hq := (toComplete m dim Q).hom.first
        change (NecklaceCode.singleIso Q.code.len).inv.app _
          (Q.code.inclusion.app _ Q.code.first) =
            (NecklaceCode.single Q.code.len).first at hq
        exact hq
      last := by
        change (NecklaceCode.singleIso Q.code.len).inv.app _
          ((ambientSimplexMap h.hom.map).app _
            ((NecklaceCode.singleIso P.code.len).hom.app _
              (NecklaceCode.single P.code.len).last)) =
                (NecklaceCode.single Q.code.len).last
        rw [singleIso_last_eq_inclusion_last, ambientSimplexMap_last h.hom]
        have hq := (toComplete m dim Q).hom.last
        change (NecklaceCode.singleIso Q.code.len).inv.app _
          (Q.code.inclusion.app _ Q.code.last) =
            (NecklaceCode.single Q.code.len).last at hq
        exact hq }
  w := by
    have hnat := beadProductExtension_naturality h.hom.map m dim Q.map
    rw [h.w] at hnat
    change ((NecklaceCode.singleIso P.code.len).hom ≫
      ambientSimplexMap h.hom.map ≫
      (NecklaceCode.singleIso Q.code.len).inv) ≫
      ((NecklaceCode.singleIso Q.code.len).hom ≫
        beadProductExtension Q.code m dim Q.map) =
          (NecklaceCode.singleIso P.code.len).hom ≫
            beadProductExtension P.code m dim P.map
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [hnat]

/-- The completion endofunctor on the actual necklace-over-product category. -/
def completionFunctor (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌)) :
    NecklacesOver (beadSpace m dim) a b ⥤
      NecklacesOver (beadSpace m dim) a b where
  obj := completeObject m dim
  map := completeMap m dim
  map_id P := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change (NecklaceCode.singleIso P.code.len).hom ≫
      ambientSimplexMap (𝟙 (P.code.toSSet : SSet.{u})) ≫
        (NecklaceCode.singleIso P.code.len).inv =
          𝟙 ((NecklaceCode.single P.code.len).toSSet : SSet.{u})
    rw [ambientSimplexMap_id]
    simp
  map_comp f g := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change (NecklaceCode.singleIso _).hom ≫
      ambientSimplexMap (f.hom.map ≫ g.hom.map) ≫
        (NecklaceCode.singleIso _).inv =
          ((NecklaceCode.singleIso _).hom ≫ ambientSimplexMap f.hom.map ≫
            (NecklaceCode.singleIso _).inv) ≫
          ((NecklaceCode.singleIso _).hom ≫ ambientSimplexMap g.hom.map ≫
            (NecklaceCode.singleIso _).inv)
    rw [ambientSimplexMap_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The original necklace includes naturally into its ambient one-bead completion. -/
def toCompletionNat (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌)) :
    𝟭 (NecklacesOver (beadSpace m dim) a b) ⟶ completionFunctor m dim a b where
  app := toComplete m dim
  naturality := by
    intro P Q h
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change h.hom.map ≫
      (Q.code.inclusion ≫ (NecklaceCode.singleIso Q.code.len).inv) =
        (P.code.inclusion ≫ (NecklaceCode.singleIso P.code.len).inv) ≫
          ((NecklaceCode.singleIso P.code.len).hom ≫
            ambientSimplexMap h.hom.map ≫
            (NecklaceCode.singleIso Q.code.len).inv)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    conv_lhs => rw [← Category.assoc]
    rw [← ambientSimplexMap_fac]
    simp only [Category.assoc]

end

end DaggerOriginalProductGadget
