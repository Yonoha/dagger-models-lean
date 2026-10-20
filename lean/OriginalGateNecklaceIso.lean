import OriginalGateNecklaceComparison

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (S : Set (X.obj (op ⦋0⦌)))
variable (hm : ∀ P : NecklacesOver X a b,
  (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)

include hm in
/-- Degreewise bijectivity proves the actual simplicial comparison is an isomorphism. -/
theorem monicGateComparison_isIso : IsIso (monicGateComparison a b S) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with
  | _ d =>
    exact (isIso_iff_bijective _).2
      ⟨monicGateComparison_injective hm, monicGateComparison_surjective hm⟩

/-- The canonical necklace-colimit isomorphism with the literal original Hom subcomplex. -/
def monicGateIso : monicGateHom a b S ≅ (flagGateSubcomplex a b S).toFunctor := by
  have := monicGateComparison_isIso S hm
  exact asIso (monicGateComparison a b S)

/-- The specified gate cocone uses the actual original flag classes as its legs. -/
def monicGateSubcomplexCocone : Cocone (monicGateFlagDiagram a b S) :=
  (monicGateCocone a b S).extend (monicGateComparison a b S)

/-- Full arbitrary-target universal property of the original gate subcomplex. -/
def monicGateSubcomplexIsColimit : IsColimit (monicGateSubcomplexCocone (a := a) (b := b) S) := by
  have := monicGateComparison_isIso S hm
  exact (monicGateIsColimit a b S).extendIso (monicGateComparison a b S)

variable {S} {R : Set (X.obj (op ⦋0⦌))}

/-- Dropping some required gates retains the exact original representative and every original arrow. -/
def monicGateForget (h : S ⊆ R) : MonicGateNecklaces a b R ⥤ MonicGateNecklaces a b S where
  obj P := ⟨P.obj, P.property.1, h.trans P.property.2⟩
  map f := ObjectProperty.homMk f.hom

/-- The induced map of the literal colimit quotients as gate requirements decrease. -/
def monicGateTransition (h : S ⊆ R) : monicGateHom a b R ⟶ monicGateHom a b S where
  app q := Quot.map (fun p ↦ ⟨(monicGateForget h).obj p.1, p.2⟩) (by
    rintro ⟨P, F⟩ ⟨Q, G⟩ ⟨f, hf⟩
    exact ⟨(monicGateForget h).map f, hf⟩)
  naturality p q α := by
    funext x
    induction x using Quot.ind with | _ x
    rfl

/-- The canonical comparisons commute with the actual inclusions of gate subcomplexes. -/
theorem monicGateComparison_naturality (h : S ⊆ R) :
    monicGateTransition h ≫ monicGateComparison a b S =
      monicGateComparison a b R ≫
        Subfunctor.homOfLe (flagGateSubcomplex_antitone a b h) := by
  ext q x
  induction x using Quot.ind with | _ x
  rfl

/-- The isomorphisms, not just degreewise bijections, respect all changes of gate requirements. -/
theorem monicGateIso_naturality (h : S ⊆ R) :
    monicGateTransition h ≫ (monicGateIso S hm).hom =
      (monicGateIso R hm).hom ≫
        Subfunctor.homOfLe (flagGateSubcomplex_antitone a b h) :=
  monicGateComparison_naturality h

/-- No ordered-target monomorphism assumption remains for the actual binary necklace product. -/
def productCutGateIso (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    {a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    (S : Set ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌))) :
    monicGateHom a b S ≅ (flagGateSubcomplex a b S).toFunctor :=
  monicGateIso S (productCut_necklace_mono_of_nondegenerate n factor T)

/-- The paper's binary-product gate value has the complete restricted-colimit universal property. -/
def productCutGateIsColimit (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    {a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    (S : Set ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌))) :
    IsColimit (monicGateSubcomplexCocone (a := a) (b := b) S) :=
  monicGateSubcomplexIsColimit S (productCut_necklace_mono_of_nondegenerate n factor T)

end

end DaggerOriginalProductGadget
