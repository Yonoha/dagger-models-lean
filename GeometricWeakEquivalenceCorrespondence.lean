import EdgeHomotopyCorrespondence
import IinjBridge

open CategoryTheory HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.GeometricWeakEquivalenceSpec

noncomputable section

private lemma bijective_iff_of_commuting_equivalences
    {α β γ δ : Type u} (e : α ≃ β) (e' : γ ≃ δ)
    (f : α → γ) (g : β → δ) (h : ∀ x, e' (f x) = g (e x)) :
    Function.Bijective g ↔ Function.Bijective f := by
  rw [← e.bijective_comp g, ← e'.comp_bijective f]
  have w : g ∘ e = e' ∘ f := funext (fun x ↦ (h x).symm)
  rw [w]

variable {X Y : SSet.{u}}

lemma mapPi_bijective_iff (f : X ⟶ Y) (n : ℕ) (x : Vertex X) (y : Vertex Y)
    (h : f.app _ x = y) :
    Function.Bijective (mapPi f n x y h) ↔
      Function.Bijective (SSet.KanComplex.mapπ f n x y h) :=
  bijective_iff_of_commuting_equivalences (pointedEquiv n X x) (pointedEquiv n Y y)
    _ _ (pointedEquiv_map f n x y h)

lemma edgeMap_bijective_iff [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y)
    (x y : Vertex X) :
    Function.Bijective (edgeMap f x y) ↔
      Function.Bijective ((SSet.KanComplex.mapFundamentalGroupoid f).map :
        (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm x ⟶
          SSet.KanComplex.FundamentalGroupoid.objEquiv.symm y) → _) :=
  bijective_iff_of_commuting_equivalences (edgeClassEquiv X x y)
    (edgeClassEquiv Y (f.app _ x) (f.app _ y)) _ _ (edgeClassEquiv_map f x y)

lemma fundamentalGroupoid_essSurj_iff [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    (SSet.KanComplex.mapFundamentalGroupoid f).EssSurj ↔
      ∀ y : Vertex Y, ∃ x : Vertex X, Nonempty (EdgeClass Y (f.app _ x) y) := by
  constructor
  · intro h y
    obtain ⟨⟨x⟩, ⟨e⟩⟩ := h.mem_essImage (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm y)
    exact ⟨x, ⟨edgeClassEquiv Y (f.app _ x) y (Groupoid.isoEquivHom _ _ e)⟩⟩
  · intro h
    refine ⟨fun y ↦ ?_⟩
    rcases y with ⟨y⟩
    obtain ⟨x, ⟨p⟩⟩ := h y
    exact ⟨SSet.KanComplex.FundamentalGroupoid.objEquiv.symm x,
      ⟨(Groupoid.isoEquivHom _ _).symm ((edgeClassEquiv Y (f.app _ x) y).symm p)⟩⟩

/-- Uses the existing full groupoid functor; essential surjectivity is not vertex surjectivity. -/
lemma fundamentalGroupoid_isEquivalence_iff [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    (SSet.KanComplex.mapFundamentalGroupoid f).IsEquivalence ↔
      (∀ x y : Vertex X, Function.Bijective (edgeMap f x y)) ∧
      (∀ y : Vertex Y, ∃ x : Vertex X, Nonempty (EdgeClass Y (f.app _ x) y)) := by
  constructor
  · intro h
    letI := h
    refine ⟨fun x y ↦ (edgeMap_bijective_iff f x y).2 ?_,
      (fundamentalGroupoid_essSurj_iff f).1 inferInstance⟩
    exact (Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _
  · rintro ⟨h, hs⟩
    have ff : Nonempty (SSet.KanComplex.mapFundamentalGroupoid f).FullyFaithful :=
      (Functor.FullyFaithful.nonempty_iff_map_bijective _).2 (fun ⟨x⟩ ⟨y⟩ ↦
        (edgeMap_bijective_iff f x y).1 (h x y))
    let ff' := Classical.choice ff
    letI := ff'.full
    letI := ff'.faithful
    letI := (fundamentalGroupoid_essSurj_iff f).2 hs
    exact {}

theorem kanW_iff_original (f : X ⟶ Y) : kanW f ↔ SSet.KanComplex.W f := by
  constructor
  · rintro ⟨hX, hY, hhom, hess, hpi⟩
    letI := hX
    letI := hY
    exact ⟨hX, hY, (fundamentalGroupoid_isEquivalence_iff f).2 ⟨hhom, hess⟩,
      fun n x y h ↦ (mapPi_bijective_iff f n x y h).1 (hpi n x y h)⟩
  · rintro ⟨hX, hY, hgroupoid, hpi⟩
    letI := hX
    letI := hY
    obtain ⟨hhom, hess⟩ := (fundamentalGroupoid_isEquivalence_iff f).1 hgroupoid
    exact ⟨hX, hY, hhom, hess,
      fun n x y h ↦ (mapPi_bijective_iff f n x y h).2 (hpi n x y h)⟩

theorem geometricW_iff_original (f : X ⟶ Y) :
    geometricW f ↔ SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f)) :=
  kanW_iff_original _

theorem geometricW_eq_original : geometricW.{u} =
    SSet.KanComplex.W.inverseImage (SSet.toTop.{u} ⋙ TopCat.toSSet) := by
  funext X Y f
  exact propext (geometricW_iff_original f)

theorem geometricW_iff_existingSSet (f : X ⟶ Y) :
    geometricW f ↔ WeakEquivalence f :=
  (geometricW_iff_original f).trans
    (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric f).symm

theorem geometricW_eq_existingSSet : geometricW.{u} = weakEquivalences SSet.{u} := by
  funext X Y f
  exact propext ((geometricW_iff_existingSSet f).trans (weakEquivalence_iff f))

end

end DaggerModels.GeometricWeakEquivalenceSpec
