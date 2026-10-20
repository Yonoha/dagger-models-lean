import NativeBisimplicialReedyRestrictions
import NativeWeaklyContractibleMaps

/-! Genuine Reedy fibrancy implies Kan horizontal mapping objects and all mono restrictions. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialReedyRestrictions
open DaggerNativeWeaklyContractibleMaps
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeReedyFibrantHorizontalMapping
noncomputable section

def homUnique (Y : SSet.{u}) (hY : ∀ d, Unique (Y.obj d)) (Z : SSet.{u}) :
    Unique (Z ⟶ Y) where
  default :=
    { app := fun d _ ↦ (hY d).default
      naturality := by
        intro d e α
        funext z
        have : Unique (Y.obj e) := hY e
        exact Subsingleton.elim _ _ }
  uniq f := by
    apply NatTrans.ext
    funext d z
    have : Unique (Y.obj d) := hY d
    exact Subsingleton.elim _ _

def terminalOfDegreewiseUnique (Y : SSet.{u}) (hY : ∀ d, Unique (Y.obj d)) :
    IsTerminal Y := by
  have (Z : SSet.{u}) : Unique (Z ⟶ Y) := homUnique Y hY Z
  exact IsTerminal.ofUnique Y

def terminalBi : BiSSet.{u} := (Functor.const _).obj (Δ[0] : SSet.{u})

def toTerminal (X : BiSSet.{u}) : X ⟶ terminalBi where
  app d := collapse (X.obj d)
  naturality _ _ _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

def ReedyFibrant (X : BiSSet.{u}) : Prop := ReedyFibration (toTerminal X)

def mappingTerminal_isTerminal (K : SSet.{u}) : IsTerminal (horizontalMapping K terminalBi) :=
  terminalOfDegreewiseUnique _ (fun d ↦ homUnique _ (by
    intro e
    change Unique ((Δ[0] : SSet.{u}).obj d)
    infer_instance) K)

theorem terminal_restriction_isIso {K L : SSet.{u}} (i : K ⟶ L) :
    IsIso (horizontalPre i terminalBi.{u}) := by
  let hK := mappingTerminal_isTerminal K
  let hL := mappingTerminal_isTerminal L
  let e : horizontalMapping L terminalBi ≅ horizontalMapping K terminalBi :=
    { hom := horizontalPre i terminalBi
      inv := hL.from _
      hom_inv_id := hL.hom_ext _ _
      inv_hom_id := hK.hom_ext _ _ }
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

theorem restriction_fibration (X : BiSSet.{u}) (hX : ReedyFibrant X)
    {K L : SSet.{u}} (i : K ⟶ L) [Mono i] : Fibration (horizontalPre i X) := by
  have : Fibration (relativeRestriction i (toTerminal X)) :=
    DaggerNativeBisimplicialReedyRestrictions.restriction_fibration (toTerminal X) hX i
  have : IsIso (horizontalPre i terminalBi.{u}) := terminal_restriction_isIso i
  have : Fibration (relativeRestriction i (toTerminal X) ≫
      pullback.fst (horizontalMap K (toTerminal X)) (horizontalPre i terminalBi)) :=
    inferInstance
  simpa only [relativeRestriction_fst] using this

def empty : SSet.{u} := (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

def emptyTo (K : SSet.{u}) : empty.{u} ⟶ K := by
  change ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ K
  exact default

theorem emptyTo_mono (K : SSet.{u}) : Mono (emptyTo K) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro d
  apply (CategoryTheory.mono_iff_injective _).mpr
  rintro ⟨x, hx⟩
  simp at hx

def mappingEmpty_isTerminal (X : BiSSet.{u}) : IsTerminal (horizontalMapping empty.{u} X) :=
  terminalOfDegreewiseUnique _ (by
    intro d
    change Unique ((((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X.flip.obj d))
    infer_instance)

theorem mapping_isFibrant (X : BiSSet.{u}) (hX : ReedyFibrant X) (K : SSet.{u}) :
    IsFibrant (horizontalMapping K X) := by
  have : Mono (emptyTo K) := emptyTo_mono K
  have : Fibration (horizontalPre (emptyTo K) X) := restriction_fibration X hX _
  exact (isFibrant_iff_of_isTerminal (horizontalPre (emptyTo K) X)
    (mappingEmpty_isTerminal X)).mpr inferInstance

end
end DaggerNativeReedyFibrantHorizontalMapping
