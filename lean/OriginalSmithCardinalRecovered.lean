import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.SetTheory.Cardinal.Order

/-! The original general Smith cardinal witness, rechecked from explicit source terms. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open CategoryTheory MorphismProperty
section
universe w v u

namespace DaggerSmithSolutionSet

/-- The same regular cardinal and small-object-argument data as the original witness. -/
structure CardinalWitness {C : Type u} [Category.{v} C] (P : MorphismProperty C) where
  κ : Cardinal.{w}
  regular : κ.IsRegular
  orderBot : OrderBot κ.ord.ToType
  suitable :
    letI : Fact κ.IsRegular := ⟨regular⟩
    letI : OrderBot κ.ord.ToType := orderBot
    P.IsCardinalForSmallObjectArgument κ

end DaggerSmithSolutionSet
end

theorem DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} :
  ∀ (κ : Cardinal.{u_1}), Cardinal.IsRegular.{u_1} κ → Fact (Cardinal.IsRegular.{u_1} κ) :=
  fun (κ : Cardinal.{u_1}) (hκ : Cardinal.IsRegular.{u_1} κ) =>
    @Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ

theorem DaggerSmithSolutionSet.uniformPresentability._simp_1_1.{u} :
  ∀ (X : Type u) (κ : Cardinal.{u}),
    @Eq.{1} Prop (HasCardinalLT.{u, u} X κ)
      (@LT.lt.{u + 1} Cardinal.{u}
        (@Preorder.toLT.{u + 1} Cardinal.{u}
          (@PartialOrder.toPreorder.{u + 1} Cardinal.{u} Cardinal.partialOrder.{u}))
        (Cardinal.mk.{u} X) κ) :=
  fun (X : Type u) (κ : Cardinal.{u}) =>
    @propext (HasCardinalLT.{u, u} X κ)
      (@LT.lt.{u + 1} Cardinal.{u}
        (@Preorder.toLT.{u + 1} Cardinal.{u}
          (@PartialOrder.toPreorder.{u + 1} Cardinal.{u} Cardinal.partialOrder.{u}))
        (Cardinal.mk.{u} X) κ)
      (hasCardinalLT_iff_cardinal_mk_lt.{u} X κ)

theorem DaggerSmithSolutionSet.uniformPresentability.{w, v, u, u_1} :
  ∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
    [@CategoryTheory.IsLocallyPresentable.{w, v, u} C inst] {S : Type u_1} [Small.{w, u_1} S]
    (A : S → C),
    @Exists.{w + 2} Cardinal.{w} fun (κ : Cardinal.{w}) =>
      @Exists.{0} (Cardinal.IsRegular.{w} κ) fun (hκ : Cardinal.IsRegular.{w} κ) =>
        ∀ (s : S),
          @CategoryTheory.IsCardinalPresentable.{w, v, u} C inst (A s) κ
            (@Fact.mk (Cardinal.IsRegular.{w} κ) hκ) :=
  fun {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{w, v, u} C inst] {S : Type u_1}
      [inst_2 : Small.{w, u_1} S] (A : S → C) =>
    (fun (κ : S → Cardinal.{w})
          (x :
            ∀ (s : S),
              @Exists.{0} (Fact (Cardinal.IsRegular.{w} (κ s)))
                fun (x : Fact (Cardinal.IsRegular.{w} (κ s))) =>
                @CategoryTheory.Functor.IsCardinalAccessible.{w, v, v, u, v + 1} C inst (Type v)
                  CategoryTheory.types.{v}
                  (@CategoryTheory.Functor.obj.{v, max u v, u, max u (v + 1)}
                    (Opposite.{u + 1} C) (@CategoryTheory.Category.opposite.{v, u} C inst)
                    (@CategoryTheory.Functor.{v, v, u, v + 1} C inst (Type v)
                      CategoryTheory.types.{v})
                    (@CategoryTheory.Functor.category.{v, v, u, v + 1} C inst (Type v)
                      CategoryTheory.types.{v})
                    (@CategoryTheory.coyoneda.{v, u} C inst) (@Opposite.op.{u + 1} C (A s)))
                  (κ s) x) =>
        (fun (hκ : ∀ (s : S), Fact (Cardinal.IsRegular.{w} (κ s)))
              (hp :
                ∀ (s : S),
                  @CategoryTheory.Functor.IsCardinalAccessible.{w, v, v, u, v + 1} C inst
                    (Type v) CategoryTheory.types.{v}
                    (@CategoryTheory.Functor.obj.{v, max u v, u, max u (v + 1)}
                      (Opposite.{u + 1} C) (@CategoryTheory.Category.opposite.{v, u} C inst)
                      (@CategoryTheory.Functor.{v, v, u, v + 1} C inst (Type v)
                        CategoryTheory.types.{v})
                      (@CategoryTheory.Functor.category.{v, v, u, v + 1} C inst (Type v)
                        CategoryTheory.types.{v})
                      (@CategoryTheory.coyoneda.{v, u} C inst) (@Opposite.op.{u + 1} C (A s)))
                    (κ s) (hκ s)) =>
            @Exists.casesOn.{w + 2} Cardinal.{w}
              (fun (κ_1 : Cardinal.{w}) =>
                And (Cardinal.IsRegular.{w} κ_1)
                  (∀ (i : S),
                    HasCardinalLT.{w, w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ i))) κ_1))
              (fun
                  (_x :
                    @Exists.{w + 2} Cardinal.{w} fun (κ_1 : Cardinal.{w}) =>
                      And (Cardinal.IsRegular.{w} κ_1)
                        (∀ (i : S),
                          HasCardinalLT.{w, w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ i)))
                            κ_1)) =>
                @Exists.{w + 2} Cardinal.{w} fun (κ : Cardinal.{w}) =>
                  @Exists.{0} (Cardinal.IsRegular.{w} κ) fun (hκ : Cardinal.IsRegular.{w} κ) =>
                    ∀ (s : S),
                      @CategoryTheory.IsCardinalPresentable.{w, v, u} C inst (A s) κ
                        (@Fact.mk (Cardinal.IsRegular.{w} κ) hκ))
              (@HasCardinalLT.exists_regular_cardinal_forall.{w, u_1, w} S
                (fun (s : S) => Ordinal.ToType.{w} (Cardinal.ord.{w} (κ s))) inst_2
                fun (i : S) =>
                @UnivLE.small.{w, w} UnivLE.self.{w}
                  (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ i))))
              fun (ρ : Cardinal.{w})
                (h :
                  And (Cardinal.IsRegular.{w} ρ)
                    (∀ (i : S),
                      HasCardinalLT.{w, w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ i))) ρ)) =>
              @And.casesOn.{0} (Cardinal.IsRegular.{w} ρ)
                (∀ (i : S),
                  HasCardinalLT.{w, w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ i))) ρ)
                (fun
                    (_x :
                      And (Cardinal.IsRegular.{w} ρ)
                        (∀ (i : S),
                          HasCardinalLT.{w, w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ i)))
                            ρ)) =>
                  @Exists.{w + 2} Cardinal.{w} fun (κ : Cardinal.{w}) =>
                    @Exists.{0} (Cardinal.IsRegular.{w} κ)
                      fun (hκ : Cardinal.IsRegular.{w} κ) =>
                      ∀ (s : S),
                        @CategoryTheory.IsCardinalPresentable.{w, v, u} C inst (A s) κ
                          (@Fact.mk (Cardinal.IsRegular.{w} κ) hκ))
                h
                fun (hρ : Cardinal.IsRegular.{w} ρ)
                  (hlt :
                    ∀ (i : S),
                      HasCardinalLT.{w, w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ i))) ρ) =>
                @Exists.intro.{w + 2} Cardinal.{w}
                  (fun (κ : Cardinal.{w}) =>
                    @Exists.{0} (Cardinal.IsRegular.{w} κ)
                      fun (hκ : Cardinal.IsRegular.{w} κ) =>
                      ∀ (s : S),
                        @CategoryTheory.IsCardinalPresentable.{w, v, u} C inst (A s) κ
                          (@Fact.mk (Cardinal.IsRegular.{w} κ) hκ))
                  ρ
                  (@Exists.intro.{0} (Cardinal.IsRegular.{w} ρ)
                    (fun (hκ : Cardinal.IsRegular.{w} ρ) =>
                      ∀ (s : S),
                        @CategoryTheory.IsCardinalPresentable.{w, v, u} C inst (A s) ρ
                          (@Fact.mk (Cardinal.IsRegular.{w} ρ) hκ))
                    hρ fun (s : S) =>
                    @CategoryTheory.isCardinalPresentable_of_le.{w, v, u} C inst (A s) (κ s)
                      (hκ s) (hp s) ρ (@Fact.mk (Cardinal.IsRegular.{w} ρ) hρ)
                      (@le_of_lt.{w + 1} Cardinal.{w}
                        (@PartialOrder.toPreorder.{w + 1} Cardinal.{w}
                          Cardinal.partialOrder.{w})
                        (κ s) ρ
                        (@Eq.mp.{0}
                          (HasCardinalLT.{w, w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ s))) ρ)
                          (@LT.lt.{w + 1} Cardinal.{w}
                            (@Preorder.toLT.{w + 1} Cardinal.{w}
                              (@PartialOrder.toPreorder.{w + 1} Cardinal.{w}
                                Cardinal.partialOrder.{w}))
                            (κ s) ρ)
                          (@Eq.trans.{1} Prop
                            (HasCardinalLT.{w, w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ s)))
                              ρ)
                            (@LT.lt.{w + 1} Cardinal.{w}
                              (@Preorder.toLT.{w + 1} Cardinal.{w}
                                (@PartialOrder.toPreorder.{w + 1} Cardinal.{w}
                                  Cardinal.partialOrder.{w}))
                              (Cardinal.mk.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ s)))) ρ)
                            (@LT.lt.{w + 1} Cardinal.{w}
                              (@Preorder.toLT.{w + 1} Cardinal.{w}
                                (@PartialOrder.toPreorder.{w + 1} Cardinal.{w}
                                  Cardinal.partialOrder.{w}))
                              (κ s) ρ)
                            (DaggerSmithSolutionSet.uniformPresentability._simp_1_1.{w}
                              (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ s))) ρ)
                            (@congrArg.{w + 2, 1} Cardinal.{w} Prop
                              (Cardinal.mk.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ s))))
                              (κ s)
                              (fun (x : Cardinal.{w}) =>
                                @LT.lt.{w + 1} Cardinal.{w}
                                  (@Preorder.toLT.{w + 1} Cardinal.{w}
                                    (@PartialOrder.toPreorder.{w + 1} Cardinal.{w}
                                      Cardinal.partialOrder.{w}))
                                  x ρ)
                              (@Eq.trans.{w + 2} Cardinal.{w}
                                (Cardinal.mk.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} (κ s))))
                                (Ordinal.card.{w} (Cardinal.ord.{w} (κ s))) (κ s)
                                (Cardinal.mk_toType.{w} (Cardinal.ord.{w} (κ s)))
                                (Cardinal.card_ord.{w} (κ s)))))
                          (hlt s)))))
          (fun (s : S) =>
            @Classical.choose.{0} (Fact (Cardinal.IsRegular.{w} (κ s)))
              (fun (x : Fact (Cardinal.IsRegular.{w} (κ s))) =>
                @CategoryTheory.Functor.IsCardinalAccessible.{w, v, v, u, v + 1} C inst (Type v)
                  CategoryTheory.types.{v}
                  (@CategoryTheory.Functor.obj.{v, max u v, u, max u (v + 1)}
                    (Opposite.{u + 1} C) (@CategoryTheory.Category.opposite.{v, u} C inst)
                    (@CategoryTheory.Functor.{v, v, u, v + 1} C inst (Type v)
                      CategoryTheory.types.{v})
                    (@CategoryTheory.Functor.category.{v, v, u, v + 1} C inst (Type v)
                      CategoryTheory.types.{v})
                    (@CategoryTheory.coyoneda.{v, u} C inst) (@Opposite.op.{u + 1} C (A s)))
                  (κ s) x)
              (x s))
          fun (s : S) =>
          @Classical.choose_spec.{0} (Fact (Cardinal.IsRegular.{w} (κ s)))
            (fun (x : Fact (Cardinal.IsRegular.{w} (κ s))) =>
              @CategoryTheory.Functor.IsCardinalAccessible.{w, v, v, u, v + 1} C inst (Type v)
                CategoryTheory.types.{v}
                (@CategoryTheory.Functor.obj.{v, max u v, u, max u (v + 1)} (Opposite.{u + 1} C)
                  (@CategoryTheory.Category.opposite.{v, u} C inst)
                  (@CategoryTheory.Functor.{v, v, u, v + 1} C inst (Type v)
                    CategoryTheory.types.{v})
                  (@CategoryTheory.Functor.category.{v, v, u, v + 1} C inst (Type v)
                    CategoryTheory.types.{v})
                  (@CategoryTheory.coyoneda.{v, u} C inst) (@Opposite.op.{u + 1} C (A s)))
                (κ s) x)
            (x s))
      (fun (s : S) =>
        @Classical.choose.{w + 2} Cardinal.{w}
          (fun (κ : Cardinal.{w}) =>
            @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
              fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
              @CategoryTheory.Functor.IsCardinalAccessible.{w, v, v, u, v + 1} C inst (Type v)
                CategoryTheory.types.{v}
                (@CategoryTheory.Functor.obj.{v, max u v, u, max u (v + 1)} (Opposite.{u + 1} C)
                  (@CategoryTheory.Category.opposite.{v, u} C inst)
                  (@CategoryTheory.Functor.{v, v, u, v + 1} C inst (Type v)
                    CategoryTheory.types.{v})
                  (@CategoryTheory.Functor.category.{v, v, u, v + 1} C inst (Type v)
                    CategoryTheory.types.{v})
                  (@CategoryTheory.coyoneda.{v, u} C inst) (@Opposite.op.{u + 1} C (A s)))
                κ x)
          ((fun (s : S) =>
              @CategoryTheory.Functor.IsAccessible.exists_cardinal.{w, v, v, u, v + 1} C inst
                (Type v) CategoryTheory.types.{v}
                (@CategoryTheory.Functor.obj.{v, max u v, u, max u (v + 1)} (Opposite.{u + 1} C)
                  (@CategoryTheory.Category.opposite.{v, u} C inst)
                  (@CategoryTheory.Functor.{v, v, u, v + 1} C inst (Type v)
                    CategoryTheory.types.{v})
                  (@CategoryTheory.Functor.category.{v, v, u, v + 1} C inst (Type v)
                    CategoryTheory.types.{v})
                  (@CategoryTheory.coyoneda.{v, u} C inst) (@Opposite.op.{u + 1} C (A s)))
                (@CategoryTheory.instIsPresentableOfIsAccessibleCategory.{w, v, u} C inst
                  (@CategoryTheory.instIsAccessibleCategoryOfIsLocallyPresentable.{w, v, u} C
                    inst inst_1)
                  (A s)))
            s))
      fun (s : S) =>
      @Classical.choose_spec.{w + 2} Cardinal.{w}
        (fun (κ : Cardinal.{w}) =>
          @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
            fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
            @CategoryTheory.Functor.IsCardinalAccessible.{w, v, v, u, v + 1} C inst (Type v)
              CategoryTheory.types.{v}
              (@CategoryTheory.Functor.obj.{v, max u v, u, max u (v + 1)} (Opposite.{u + 1} C)
                (@CategoryTheory.Category.opposite.{v, u} C inst)
                (@CategoryTheory.Functor.{v, v, u, v + 1} C inst (Type v)
                  CategoryTheory.types.{v})
                (@CategoryTheory.Functor.category.{v, v, u, v + 1} C inst (Type v)
                  CategoryTheory.types.{v})
                (@CategoryTheory.coyoneda.{v, u} C inst) (@Opposite.op.{u + 1} C (A s)))
              κ x)
        ((fun (s : S) =>
            @CategoryTheory.Functor.IsAccessible.exists_cardinal.{w, v, v, u, v + 1} C inst
              (Type v) CategoryTheory.types.{v}
              (@CategoryTheory.Functor.obj.{v, max u v, u, max u (v + 1)} (Opposite.{u + 1} C)
                (@CategoryTheory.Category.opposite.{v, u} C inst)
                (@CategoryTheory.Functor.{v, v, u, v + 1} C inst (Type v)
                  CategoryTheory.types.{v})
                (@CategoryTheory.Functor.category.{v, v, u, v + 1} C inst (Type v)
                  CategoryTheory.types.{v})
                (@CategoryTheory.coyoneda.{v, u} C inst) (@Opposite.op.{u + 1} C (A s)))
              (@CategoryTheory.instIsPresentableOfIsAccessibleCategory.{w, v, u} C inst
                (@CategoryTheory.instIsAccessibleCategoryOfIsLocallyPresentable.{w, v, u} C inst
                  inst_1)
                (A s)))
          s)

theorem DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} :
  ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C]
    [@CategoryTheory.IsLocallyPresentable.{u_1, u_3, u_2} C inst]
    (P :
      @CategoryTheory.MorphismProperty.{u_3, u_2} C
        (@CategoryTheory.Category.toCategoryStruct.{u_3, u_2} C inst))
    [@CategoryTheory.MorphismProperty.IsSmall.{u_1, u_3, u_2} C inst P],
    @Exists.{u_1 + 2} Cardinal.{u_1} fun (κ : Cardinal.{u_1}) =>
      @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
        ∀
          (s :
            @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
              (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
          @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
            (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
              (@Subtype.val.{max (u_2 + 1) (u_3 + 1)} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                  @Membership.mem.{max u_2 u_3, max u_2 u_3}
                    (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                    (@Set.instMembership.{max u_2 u_3}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                s))
            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ) :=
  fun {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_3, u_2} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{u_3, u_2} C
          (@CategoryTheory.Category.toCategoryStruct.{u_3, u_2} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_3, u_2} C inst P] =>
    @DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C inst inst_1
      (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
        (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
      (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst P inst_2)
      fun
        (s :
          @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
      @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
        (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
        (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
        (@Subtype.val.{max (u_2 + 1) (u_3 + 1)} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
          (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
            @Membership.mem.{max u_2 u_3, max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
              (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
              (@Set.instMembership.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
              (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
          s)

theorem DaggerSmithSolutionSet.cardinalWitness._proof_4.{u_1, u_2, u_3} :
  ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C]
    [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_3, u_2} C inst]
    (P :
      @CategoryTheory.MorphismProperty.{u_3, u_2} C
        (@CategoryTheory.Category.toCategoryStruct.{u_3, u_2} C inst))
    [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_3, u_2} C inst P],
    Fact
      (Cardinal.IsRegular.{u_1}
        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
          (fun (κ : Cardinal.{u_1}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                  (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                        @Membership.mem.{max u_2 u_3, max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@Set.instMembership.{max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                      s))
                  κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} C inst inst_1 P
            inst_2))) :=
  fun {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_3, u_2} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{u_3, u_2} C
          (@CategoryTheory.Category.toCategoryStruct.{u_3, u_2} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_3, u_2} C inst P] =>
    @Fact.mk
      (Cardinal.IsRegular.{u_1}
        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
          (fun (κ : Cardinal.{u_1}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                  (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                        @Membership.mem.{max u_2 u_3, max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@Set.instMembership.{max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                      s))
                  κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
          (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C inst
            inst_1
            (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
              (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
            (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst P
              inst_2)
            fun
              (s :
                @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
            @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
              (@Subtype.val.{max (u_2 + 1) (u_3 + 1)} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                  @Membership.mem.{max u_2 u_3, max u_2 u_3}
                    (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                    (@Set.instMembership.{max u_2 u_3}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                s))))
      (@Exists.choose.{0}
        (Cardinal.IsRegular.{u_1}
          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
            (fun (κ : Cardinal.{u_1}) =>
              @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                ∀
                  (s :
                    @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                  @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                    (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                          @Membership.mem.{max u_2 u_3, max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@Set.instMembership.{max u_2 u_3}
                              (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                        s))
                    κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
            (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C inst
              inst_1
              (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
              (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst P
                inst_2)
              fun
                (s :
                  @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
              @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
                (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                  (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                  (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                    @Membership.mem.{max u_2 u_3, max u_2 u_3}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                      (@Set.instMembership.{max u_2 u_3}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                      (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                  s))))
        (fun
            (hκ :
              Cardinal.IsRegular.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                          (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                            (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                            (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                              (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                                @Membership.mem.{max u_2 u_3, max u_2 u_3}
                                  (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                                  (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                                  (@Set.instMembership.{max u_2 u_3}
                                    (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)
                                  x)
                              s))
                          κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
                  (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C
                    inst inst_1
                    (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
                    (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst
                      P inst_2)
                    fun
                      (s :
                        @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
                    @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                          @Membership.mem.{max u_2 u_3, max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@Set.instMembership.{max u_2 u_3}
                              (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                        s)))) =>
          ∀
            (s :
              @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
            @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
              (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
                (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                  (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                  (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                    @Membership.mem.{max u_2 u_3, max u_2 u_3}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                      (@Set.instMembership.{max u_2 u_3}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                      (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                  s))
              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                (fun (κ : Cardinal.{u_1}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                        (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                          (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                          (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                              @Membership.mem.{max u_2 u_3, max u_2 u_3}
                                (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                                (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                                (@Set.instMembership.{max u_2 u_3}
                                  (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                            s))
                        κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
                (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C
                  inst inst_1
                  (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
                  (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst P
                    inst_2)
                  fun
                    (s :
                      @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
                  @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                        @Membership.mem.{max u_2 u_3, max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@Set.instMembership.{max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                      s)))
              (@Fact.mk
                (Cardinal.IsRegular.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                            (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                              (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                                (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                                  @Membership.mem.{max u_2 u_3, max u_2 u_3}
                                    (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                                    (Set.{max u_2 u_3}
                                      (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                                    (@Set.instMembership.{max u_2 u_3}
                                      (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)
                                    x)
                                s))
                            κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
                    (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3}
                      C inst inst_1
                      (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
                      (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C
                        inst P inst_2)
                      fun
                        (s :
                          @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
                      @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                        inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                        (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                        (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                            @Membership.mem.{max u_2 u_3, max u_2 u_3}
                              (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                              (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                              (@Set.instMembership.{max u_2 u_3}
                                (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                              (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                          s))))
                hκ))
        (@Exists.choose_spec.{u_1 + 2} Cardinal.{u_1}
          (fun (κ : Cardinal.{u_1}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                  (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                        @Membership.mem.{max u_2 u_3, max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@Set.instMembership.{max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                      s))
                  κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
          (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C inst
            inst_1
            (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
              (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
            (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst P
              inst_2)
            fun
              (s :
                @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
            @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
              (@Subtype.val.{max (u_2 + 1) (u_3 + 1)} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                  @Membership.mem.{max u_2 u_3, max u_2 u_3}
                    (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                    (@Set.instMembership.{max u_2 u_3}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                s))))

theorem DaggerSmithSolutionSet.cardinalWitness._proof_5.{u_1, u_2, u_3} :
  ∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_2, u_1} C]
    [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_3, u_2, u_1} C inst]
    (P :
      @CategoryTheory.MorphismProperty.{u_2, u_1} C
        (@CategoryTheory.Category.toCategoryStruct.{u_2, u_1} C inst))
    [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_3, u_2, u_1} C inst P]
    (s :
      @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)),
    @CategoryTheory.IsCardinalPresentable.{u_3, u_2, u_1} C inst
      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C inst
        (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
        (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
        (@Subtype.val.{max (u_1 + 1) (u_2 + 1)} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
          (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
            @Membership.mem.{max u_1 u_2, max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
              (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
              (@Set.instMembership.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
          s))
      (@Exists.choose.{u_3 + 2} Cardinal.{u_3}
        (fun (κ : Cardinal.{u_3}) =>
          @Exists.{0} (Cardinal.IsRegular.{u_3} κ) fun (hκ : Cardinal.IsRegular.{u_3} κ) =>
            ∀
              (s :
                @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)),
              @CategoryTheory.IsCardinalPresentable.{u_3, u_2, u_1} C inst
                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                  (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                  (@Subtype.val.{max (u_1 + 1) (u_2 + 1)}
                    (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                      @Membership.mem.{max u_1 u_2, max u_1 u_2}
                        (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                        (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                        (@Set.instMembership.{max u_1 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
                    s))
                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_3} κ hκ))
        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_3, u_1, u_2} C inst inst_1 P
          inst_2))
      (@DaggerSmithSolutionSet.cardinalWitness._proof_4.{u_3, u_1, u_2} C inst inst_1 P inst_2) :=
  fun {C : Type u_1} [inst : CategoryTheory.Category.{u_2, u_1} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_3, u_2, u_1} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{u_2, u_1} C
          (@CategoryTheory.Category.toCategoryStruct.{u_2, u_1} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_3, u_2, u_1} C inst P] =>
    @Exists.choose_spec.{0}
      (Cardinal.IsRegular.{u_3}
        (@Exists.choose.{u_3 + 2} Cardinal.{u_3}
          (fun (κ : Cardinal.{u_3}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_3} κ) fun (hκ : Cardinal.IsRegular.{u_3} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_3, u_2, u_1} C inst
                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                    (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                    (@Subtype.val.{max (u_1 + 1) (u_2 + 1)}
                      (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                        @Membership.mem.{max u_1 u_2, max u_1 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                          (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                          (@Set.instMembership.{max u_1 u_2}
                            (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
                      s))
                  κ (@Fact.mk (Cardinal.IsRegular.{u_3} κ) hκ))
          (@DaggerSmithSolutionSet.uniformPresentability.{u_3, u_2, u_1, max u_1 u_2} C inst
            inst_1
            (@Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P))
            (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_3, u_2, u_1} C inst P
              inst_2)
            fun
              (s :
                @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)) =>
            @CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C inst
              (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
              (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
              (@Subtype.val.{max (u_1 + 1) (u_2 + 1)} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                  @Membership.mem.{max u_1 u_2, max u_1 u_2}
                    (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                    (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                    (@Set.instMembership.{max u_1 u_2}
                      (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
                s))))
      (fun
          (hκ :
            Cardinal.IsRegular.{u_3}
              (@Exists.choose.{u_3 + 2} Cardinal.{u_3}
                (fun (κ : Cardinal.{u_3}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_3} κ)
                    fun (hκ : Cardinal.IsRegular.{u_3} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_3, u_2, u_1} C inst
                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                          (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                          (@Subtype.val.{max (u_1 + 1) (u_2 + 1)}
                            (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                              @Membership.mem.{max u_1 u_2, max u_1 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                                (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                                (@Set.instMembership.{max u_1 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
                            s))
                        κ (@Fact.mk (Cardinal.IsRegular.{u_3} κ) hκ))
                (@DaggerSmithSolutionSet.uniformPresentability.{u_3, u_2, u_1, max u_1 u_2} C
                  inst inst_1
                  (@Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P))
                  (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_3, u_2, u_1} C inst P
                    inst_2)
                  fun
                    (s :
                      @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)) =>
                  @CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C inst
                    (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                    (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                    (@Subtype.val.{max (u_1 + 1) (u_2 + 1)}
                      (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                        @Membership.mem.{max u_1 u_2, max u_1 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                          (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                          (@Set.instMembership.{max u_1 u_2}
                            (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
                      s)))) =>
        ∀
          (s :
            @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)),
          @CategoryTheory.IsCardinalPresentable.{u_3, u_2, u_1} C inst
            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C inst
              (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
              (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
              (@Subtype.val.{max (u_1 + 1) (u_2 + 1)} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                  @Membership.mem.{max u_1 u_2, max u_1 u_2}
                    (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                    (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                    (@Set.instMembership.{max u_1 u_2}
                      (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
                s))
            (@Exists.choose.{u_3 + 2} Cardinal.{u_3}
              (fun (κ : Cardinal.{u_3}) =>
                @Exists.{0} (Cardinal.IsRegular.{u_3} κ)
                  fun (hκ : Cardinal.IsRegular.{u_3} κ) =>
                  ∀
                    (s :
                      @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)),
                    @CategoryTheory.IsCardinalPresentable.{u_3, u_2, u_1} C inst
                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C
                        inst (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                        (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                        (@Subtype.val.{max (u_1 + 1) (u_2 + 1)}
                          (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                          (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                            @Membership.mem.{max u_1 u_2, max u_1 u_2}
                              (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                              (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                              (@Set.instMembership.{max u_1 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
                          s))
                      κ (@Fact.mk (Cardinal.IsRegular.{u_3} κ) hκ))
              (@DaggerSmithSolutionSet.uniformPresentability.{u_3, u_2, u_1, max u_1 u_2} C inst
                inst_1
                (@Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P))
                (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_3, u_2, u_1} C inst P
                  inst_2)
                fun
                  (s :
                    @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)) =>
                @CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                  (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                  (@Subtype.val.{max (u_1 + 1) (u_2 + 1)}
                    (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                      @Membership.mem.{max u_1 u_2, max u_1 u_2}
                        (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                        (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                        (@Set.instMembership.{max u_1 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
                    s)))
            (@Fact.mk
              (Cardinal.IsRegular.{u_3}
                (@Exists.choose.{u_3 + 2} Cardinal.{u_3}
                  (fun (κ : Cardinal.{u_3}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_3} κ)
                      fun (hκ : Cardinal.IsRegular.{u_3} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_3, u_2, u_1} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                            (@Subtype.val.{max (u_1 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                                @Membership.mem.{max u_1 u_2, max u_1 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                                  (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                                  (@Set.instMembership.{max u_1 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)
                                  x)
                              s))
                          κ (@Fact.mk (Cardinal.IsRegular.{u_3} κ) hκ))
                  (@DaggerSmithSolutionSet.uniformPresentability.{u_3, u_2, u_1, max u_1 u_2} C
                    inst inst_1
                    (@Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P))
                    (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_3, u_2, u_1} C inst
                      P inst_2)
                    fun
                      (s :
                        @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)) =>
                    @CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                      (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                      (@Subtype.val.{max (u_1 + 1) (u_2 + 1)}
                        (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                          @Membership.mem.{max u_1 u_2, max u_1 u_2}
                            (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                            (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                            (@Set.instMembership.{max u_1 u_2}
                              (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
                        s))))
              hκ))
      (@Exists.choose_spec.{u_3 + 2} Cardinal.{u_3}
        (fun (κ : Cardinal.{u_3}) =>
          @Exists.{0} (Cardinal.IsRegular.{u_3} κ) fun (hκ : Cardinal.IsRegular.{u_3} κ) =>
            ∀
              (s :
                @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)),
              @CategoryTheory.IsCardinalPresentable.{u_3, u_2, u_1} C inst
                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                  (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
                  (@Subtype.val.{max (u_1 + 1) (u_2 + 1)}
                    (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                      @Membership.mem.{max u_1 u_2, max u_1 u_2}
                        (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                        (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                        (@Set.instMembership.{max u_1 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
                    s))
                κ (@Fact.mk (Cardinal.IsRegular.{u_3} κ) hκ))
        (@DaggerSmithSolutionSet.uniformPresentability.{u_3, u_2, u_1, max u_1 u_2} C inst
          inst_1
          (@Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P))
          (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_3, u_2, u_1} C inst P inst_2)
          fun
            (s :
              @Set.Elem.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P)) =>
          @CategoryTheory.Comma.left.{u_2, u_2, u_2, u_1, u_1, u_1} C inst C inst C inst
            (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
            (@CategoryTheory.Functor.id.{u_2, u_1} C inst)
            (@Subtype.val.{max (u_1 + 1) (u_2 + 1)} (@CategoryTheory.Arrow.{u_2, u_1} C inst)
              (fun (x : @CategoryTheory.Arrow.{u_2, u_1} C inst) =>
                @Membership.mem.{max u_1 u_2, max u_1 u_2}
                  (@CategoryTheory.Arrow.{u_2, u_1} C inst)
                  (Set.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                  (@Set.instMembership.{max u_1 u_2} (@CategoryTheory.Arrow.{u_2, u_1} C inst))
                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_1} C inst P) x)
              s)))

theorem DaggerSmithSolutionSet.cardinalWitness._proof_6.{u_1, u_2, u_3} :
  ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C]
    [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_3, u_2} C inst]
    (P :
      @CategoryTheory.MorphismProperty.{u_3, u_2} C
        (@CategoryTheory.Category.toCategoryStruct.{u_3, u_2} C inst))
    [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_3, u_2} C inst P],
    Cardinal.IsRegular.{u_1}
        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
          (fun (κ : Cardinal.{u_1}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                  (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                        @Membership.mem.{max u_2 u_3, max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@Set.instMembership.{max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                      s))
                  κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} C inst inst_1 P
            inst_2)) →
      Fact
        (Cardinal.IsRegular.{u_1}
          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
            (fun (κ : Cardinal.{u_1}) =>
              @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                ∀
                  (s :
                    @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                  @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                    (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                          @Membership.mem.{max u_2 u_3, max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@Set.instMembership.{max u_2 u_3}
                              (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                        s))
                    κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} C inst inst_1 P
              inst_2))) :=
  fun {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_3, u_2} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{u_3, u_2} C
          (@CategoryTheory.Category.toCategoryStruct.{u_3, u_2} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_3, u_2} C inst P]
      (hκ :
        Cardinal.IsRegular.{u_1}
          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
            (fun (κ : Cardinal.{u_1}) =>
              @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                ∀
                  (s :
                    @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                  @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                    (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                          @Membership.mem.{max u_2 u_3, max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@Set.instMembership.{max u_2 u_3}
                              (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                        s))
                    κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} C inst inst_1 P
              inst_2))) =>
    @Fact.mk
      (Cardinal.IsRegular.{u_1}
        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
          (fun (κ : Cardinal.{u_1}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                  (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                        @Membership.mem.{max u_2 u_3, max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@Set.instMembership.{max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                      s))
                  κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} C inst inst_1 P
            inst_2)))
      hκ

theorem DaggerSmithSolutionSet.cardinalWitness._proof_7.{u_1, u_2, u_3} :
  ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C]
    [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_3, u_2} C inst]
    (P :
      @CategoryTheory.MorphismProperty.{u_3, u_2} C
        (@CategoryTheory.Category.toCategoryStruct.{u_3, u_2} C inst))
    [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_3, u_2} C inst P],
    Cardinal.IsRegular.{u_1}
        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
          (fun (κ : Cardinal.{u_1}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                  (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                        @Membership.mem.{max u_2 u_3, max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@Set.instMembership.{max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                      s))
                  κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} C inst inst_1 P
            inst_2)) →
      @Ne.{u_1 + 2} Cardinal.{u_1}
        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
          (fun (κ : Cardinal.{u_1}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                  (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                        @Membership.mem.{max u_2 u_3, max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@Set.instMembership.{max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                      s))
                  κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} C inst inst_1 P
            inst_2))
        (@OfNat.ofNat.{u_1 + 1} Cardinal.{u_1} (nat_lit 0)
          (@Zero.toOfNat0.{u_1 + 1} Cardinal.{u_1} Cardinal.instZero.{u_1})) :=
  fun {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_3, u_2} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{u_3, u_2} C
          (@CategoryTheory.Category.toCategoryStruct.{u_3, u_2} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_3, u_2} C inst P]
      (hκ :
        Cardinal.IsRegular.{u_1}
          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
            (fun (κ : Cardinal.{u_1}) =>
              @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                ∀
                  (s :
                    @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                  @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                    (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                          @Membership.mem.{max u_2 u_3, max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@Set.instMembership.{max u_2 u_3}
                              (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                        s))
                    κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} C inst inst_1 P
              inst_2))) =>
    @Cardinal.IsRegular.ne_zero.{u_1}
      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
        (fun (κ : Cardinal.{u_1}) =>
          @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
            ∀
              (s :
                @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
              @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                  (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                  (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                    (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                      @Membership.mem.{max u_2 u_3, max u_2 u_3}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                        (@Set.instMembership.{max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                    s))
                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} C inst inst_1 P
          inst_2))
      hκ

theorem DaggerSmithSolutionSet.locallySmall.{w, v, u} :
  ∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
    [@CategoryTheory.IsLocallyPresentable.{w, v, u} C inst],
    @CategoryTheory.LocallySmall.{w, v, u} C inst :=
  fun {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{w, v, u} C inst] =>
    @Exists.casesOn.{w + 2} Cardinal.{w}
      (fun (κ : Cardinal.{w}) =>
        @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
          fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
          @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ x)
      (fun
          (_x :
            @Exists.{w + 2} Cardinal.{w} fun (κ : Cardinal.{w}) =>
              @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
                fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
                @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ x) =>
        @CategoryTheory.LocallySmall.{w, v, u} C inst)
      (@CategoryTheory.IsLocallyPresentable.exists_cardinal.{w, v, u} C inst inst_1)
      fun (κ : Cardinal.{w})
        (h :
          @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
            fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
            @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ x) =>
      @Exists.casesOn.{0} (Fact (Cardinal.IsRegular.{w} κ))
        (fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
          @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ x)
        (fun
            (_x :
              @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
                fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
                @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ x) =>
          @CategoryTheory.LocallySmall.{w, v, u} C inst)
        h
        fun (w : Fact (Cardinal.IsRegular.{w} κ))
          (h : @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ w) =>
        @inferInstance.{0} (@CategoryTheory.LocallySmall.{w, v, u} C inst)
          (@CategoryTheory.HasCardinalFilteredGenerator.toLocallySmall.{w, v, u} C inst κ w
            (@CategoryTheory.IsCardinalAccessibleCategory.toHasCardinalFilteredGenerator.{w, v,
                  u}
              C inst κ w
              (@CategoryTheory.instIsCardinalAccessibleCategoryOfIsCardinalLocallyPresentable.{w,
                    v, u}
                C inst κ w h)))

theorem DaggerSmithSolutionSet.colimits.{w, v, u} :
  ∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
    [@CategoryTheory.IsLocallyPresentable.{w, v, u} C inst],
    @CategoryTheory.Limits.HasColimitsOfSize.{w, w, v, u} C inst :=
  fun {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{w, v, u} C inst] =>
    @Exists.casesOn.{w + 2} Cardinal.{w}
      (fun (κ : Cardinal.{w}) =>
        @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
          fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
          @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ x)
      (fun
          (_x :
            @Exists.{w + 2} Cardinal.{w} fun (κ : Cardinal.{w}) =>
              @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
                fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
                @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ x) =>
        @CategoryTheory.Limits.HasColimitsOfSize.{w, w, v, u} C inst)
      (@CategoryTheory.IsLocallyPresentable.exists_cardinal.{w, v, u} C inst inst_1)
      fun (κ : Cardinal.{w})
        (h :
          @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
            fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
            @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ x) =>
      @Exists.casesOn.{0} (Fact (Cardinal.IsRegular.{w} κ))
        (fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
          @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ x)
        (fun
            (_x :
              @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
                fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
                @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ x) =>
          @CategoryTheory.Limits.HasColimitsOfSize.{w, w, v, u} C inst)
        h
        fun (w : Fact (Cardinal.IsRegular.{w} κ))
          (h : @CategoryTheory.IsCardinalLocallyPresentable.{w, v, u} C inst κ w) =>
        @inferInstance.{0} (@CategoryTheory.Limits.HasColimitsOfSize.{w, w, v, u} C inst)
          (@CategoryTheory.IsCardinalLocallyPresentable.toHasColimitsOfSize.{w, v, u} C inst κ w
            h)

theorem DaggerSmithSolutionSet.cardinalWitness._proof_8.{u_1, u_2, u_3} :
  ∀ {C : Type u_3} [inst : CategoryTheory.Category.{u_2, u_3} C]
    [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_2, u_3} C inst]
    (P :
      @CategoryTheory.MorphismProperty.{u_2, u_3} C
        (@CategoryTheory.Category.toCategoryStruct.{u_2, u_3} C inst))
    [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_2, u_3} C inst P]
    (hκ :
      Cardinal.IsRegular.{u_1}
        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
          (fun (κ : Cardinal.{u_1}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                          (@Set.instMembership.{max u_3 u_2}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                      s))
                  κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
            inst_2))),
    (∀
        (s :
          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C inst
            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                  (@Set.instMembership.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
              s))
          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
            (fun (κ : Cardinal.{u_1}) =>
              @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                ∀
                  (s :
                    @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                            (@Set.instMembership.{max u_3 u_2}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                        s))
                    κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
              inst_2))
          (@DaggerSmithSolutionSet.cardinalWitness._proof_4.{u_1, u_3, u_2} C inst inst_1 P
            inst_2)) →
      @CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.{u_1, u_2, u_3} C inst P
        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
          (fun (κ : Cardinal.{u_1}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                          (@Set.instMembership.{max u_3 u_2}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                      s))
                  κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
            inst_2))
        (@DaggerSmithSolutionSet.cardinalWitness._proof_6.{u_1, u_3, u_2} C inst inst_1 P inst_2
          hκ)
        (@inferInstance.{u_1 + 1}
          (@OrderBot.{u_1}
            (Ordinal.ToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (@Preorder.toLE.{u_1}
              (Ordinal.ToType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (@PartialOrder.toPreorder.{u_1}
                (Ordinal.ToType.{u_1}
                  (Cardinal.ord.{u_1}
                    (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                      (fun (κ : Cardinal.{u_1}) =>
                        @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                          fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                          ∀
                            (s :
                              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                            @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                              (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst
                                C inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (Set.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@Set.instMembership.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)
                                      x)
                                  s))
                              κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                      (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                        inst_1 P inst_2))))
                (@SemilatticeInf.toPartialOrder.{u_1}
                  (Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                  (@Lattice.toSemilatticeInf.{u_1}
                    (Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                    (@DistribLattice.toLattice.{u_1}
                      (Ordinal.ToType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))
                      (@instDistribLatticeOfLinearOrder.{u_1}
                        (Ordinal.ToType.{u_1}
                          (Cardinal.ord.{u_1}
                            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                              (fun (κ : Cardinal.{u_1}) =>
                                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                  ∀
                                    (s :
                                      @Set.Elem.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)),
                                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3}
                                        C inst C inst C inst
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (Set.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@Set.instMembership.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)
                                              x)
                                          s))
                                      κ
                                      (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                        hκ))
                              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2}
                                C inst inst_1 P inst_2))))
                        (linearOrder_toType.{u_1}
                          (Cardinal.ord.{u_1}
                            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                              (fun (κ : Cardinal.{u_1}) =>
                                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                  ∀
                                    (s :
                                      @Set.Elem.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)),
                                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3}
                                        C inst C inst C inst
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (Set.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@Set.instMembership.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)
                                              x)
                                          s))
                                      κ
                                      (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                        hκ))
                              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2}
                                C inst inst_1 P inst_2)))))))))))
          (@Cardinal.toTypeOrderBot.{u_1}
            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
              (fun (κ : Cardinal.{u_1}) =>
                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                  ∀
                    (s :
                      @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C
                        inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                              (@Set.instMembership.{max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                          s))
                      κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
                inst_2))
            (@DaggerSmithSolutionSet.cardinalWitness._proof_7.{u_1, u_3, u_2} C inst inst_1 P
              inst_2 hκ))) :=
  fun {C : Type u_3} [inst : CategoryTheory.Category.{u_2, u_3} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_2, u_3} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{u_2, u_3} C
          (@CategoryTheory.Category.toCategoryStruct.{u_2, u_3} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_2, u_3} C inst P]
      (hκ :
        Cardinal.IsRegular.{u_1}
          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
            (fun (κ : Cardinal.{u_1}) =>
              @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                ∀
                  (s :
                    @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                            (@Set.instMembership.{max u_3 u_2}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                        s))
                    κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
              inst_2)))
      (hp :
        ∀
          (s :
            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C inst
              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                    (@Set.instMembership.{max u_3 u_2}
                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                s))
            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
              (fun (κ : Cardinal.{u_1}) =>
                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                  ∀
                    (s :
                      @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C
                        inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                              (@Set.instMembership.{max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                          s))
                      κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
                inst_2))
            (@DaggerSmithSolutionSet.cardinalWitness._proof_4.{u_1, u_3, u_2} C inst inst_1 P
              inst_2)) =>
    @CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.mk.{u_1, u_2, u_3} C inst
      P
      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
        (fun (κ : Cardinal.{u_1}) =>
          @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
            ∀
              (s :
                @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                        (@Set.instMembership.{max u_3 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                    s))
                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
          inst_2))
      (@Fact.mk
        (Cardinal.IsRegular.{u_1}
          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
            (fun (κ : Cardinal.{u_1}) =>
              @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                ∀
                  (s :
                    @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                            (@Set.instMembership.{max u_3 u_2}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                        s))
                    κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
              inst_2)))
        hκ)
      (@inferInstance.{u_1 + 1}
        (@OrderBot.{u_1}
          (Ordinal.ToType.{u_1}
            (Cardinal.ord.{u_1}
              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                (fun (κ : Cardinal.{u_1}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@Set.instMembership.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                            s))
                        κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1
                  P inst_2))))
          (@Preorder.toLE.{u_1}
            (Ordinal.ToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (@PartialOrder.toPreorder.{u_1}
              (Ordinal.ToType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (@SemilatticeInf.toPartialOrder.{u_1}
                (Ordinal.ToType.{u_1}
                  (Cardinal.ord.{u_1}
                    (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                      (fun (κ : Cardinal.{u_1}) =>
                        @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                          fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                          ∀
                            (s :
                              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                            @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                              (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst
                                C inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (Set.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@Set.instMembership.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)
                                      x)
                                  s))
                              κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                      (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                        inst_1 P inst_2))))
                (@Lattice.toSemilatticeInf.{u_1}
                  (Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                  (@DistribLattice.toLattice.{u_1}
                    (Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                    (@instDistribLatticeOfLinearOrder.{u_1}
                      (Ordinal.ToType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))
                      (linearOrder_toType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2)))))))))))
        (@Cardinal.toTypeOrderBot.{u_1}
          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
            (fun (κ : Cardinal.{u_1}) =>
              @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                ∀
                  (s :
                    @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                            (@Set.instMembership.{max u_3 u_2}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                        s))
                    κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
              inst_2))
          (@Cardinal.IsRegular.ne_zero.{u_1}
            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
              (fun (κ : Cardinal.{u_1}) =>
                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                  ∀
                    (s :
                      @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C
                        inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                              (@Set.instMembership.{max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                          s))
                      κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
                inst_2))
            hκ)))
      (@inferInstance.{0} (@CategoryTheory.MorphismProperty.IsSmall.{u_1, u_2, u_3} C inst P)
        inst_2)
      (@inferInstance.{0} (@CategoryTheory.LocallySmall.{u_1, u_2, u_3} C inst)
        (@DaggerSmithSolutionSet.locallySmall.{u_1, u_2, u_3} C inst inst_1))
      (@inferInstance.{0} (@CategoryTheory.Limits.HasPushouts.{u_2, u_3} C inst)
        (@CategoryTheory.Limits.hasPushouts_of_hasWidePushouts.{u_1, u_2, u_3} C inst
          fun (J : Type u_1) =>
          @CategoryTheory.Limits.hasColimitsOfShapeOfHasColimitsOfSize.{u_1, u_1, u_2, u_3} C
            inst (CategoryTheory.Limits.WidePushoutShape.{u_1} J)
            (@CategoryTheory.Limits.WidePushoutShape.category.{u_1} J)
            (@DaggerSmithSolutionSet.colimits.{u_1, u_2, u_3} C inst inst_1)))
      (@inferInstance.{0} (@CategoryTheory.Limits.HasCoproducts.{u_1, u_2, u_3} C inst)
        fun (J : Type u_1) =>
        @CategoryTheory.Limits.hasCoproductsOfShape_of_hasCoproducts.{u_1, u_2, u_3} C inst
          (fun (J : Type u_1) =>
            @CategoryTheory.Limits.hasColimitsOfShapeOfHasColimitsOfSize.{u_1, u_1, u_2, u_3} C
              inst (CategoryTheory.Discrete.{u_1} J) (CategoryTheory.discreteCategory.{u_1} J)
              (@DaggerSmithSolutionSet.colimits.{u_1, u_2, u_3} C inst inst_1))
          J)
      (@inferInstance.{0}
        (@CategoryTheory.Limits.HasIterationOfShape.{u_1, u_2, u_3}
          (Ordinal.ToType.{u_1}
            (Cardinal.ord.{u_1}
              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                (fun (κ : Cardinal.{u_1}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@Set.instMembership.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                            s))
                        κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1
                  P inst_2))))
          (linearOrder_toType.{u_1}
            (Cardinal.ord.{u_1}
              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                (fun (κ : Cardinal.{u_1}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@Set.instMembership.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                            s))
                        κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1
                  P inst_2))))
          C inst)
        (@CategoryTheory.Limits.instHasIterationOfShapeOfHasColimitsOfSize.{u_1, u_2, u_3}
          (Ordinal.ToType.{u_1}
            (Cardinal.ord.{u_1}
              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                (fun (κ : Cardinal.{u_1}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@Set.instMembership.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                            s))
                        κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1
                  P inst_2))))
          (linearOrder_toType.{u_1}
            (Cardinal.ord.{u_1}
              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                (fun (κ : Cardinal.{u_1}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@Set.instMembership.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                            s))
                        κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1
                  P inst_2))))
          C inst (@DaggerSmithSolutionSet.colimits.{u_1, u_2, u_3} C inst inst_1)))
      fun {A B X Y : C}
        (i :
          @Quiver.Hom.{u_2 + 1, u_3} C
            (@CategoryTheory.CategoryStruct.toQuiver.{u_2, u_3} C
              (@CategoryTheory.Category.toCategoryStruct.{u_2, u_3} C inst))
            A B)
        (hi : @P A B i)
        (f :
          @Quiver.Hom.{u_2 + 1, u_3} C
            (@CategoryTheory.CategoryStruct.toQuiver.{u_2, u_3} C
              (@CategoryTheory.Category.toCategoryStruct.{u_2, u_3} C inst))
            X Y)
        (hf :
          @HomotopicalAlgebra.RelativeCellComplex.{u_1, u_1, max u_3 u_2, u_2, u_3} C inst
            (Ordinal.ToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (linearOrder_toType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (@inferInstance.{u_1 + 1}
              (@OrderBot.{u_1}
                (Ordinal.ToType.{u_1}
                  (Cardinal.ord.{u_1}
                    (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                      (fun (κ : Cardinal.{u_1}) =>
                        @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                          fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                          ∀
                            (s :
                              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                            @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                              (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst
                                C inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (Set.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@Set.instMembership.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)
                                      x)
                                  s))
                              κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                      (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                        inst_1 P inst_2))))
                (@Preorder.toLE.{u_1}
                  (Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                  (@PartialOrder.toPreorder.{u_1}
                    (Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                    (@SemilatticeInf.toPartialOrder.{u_1}
                      (Ordinal.ToType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))
                      (@Lattice.toSemilatticeInf.{u_1}
                        (Ordinal.ToType.{u_1}
                          (Cardinal.ord.{u_1}
                            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                              (fun (κ : Cardinal.{u_1}) =>
                                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                  ∀
                                    (s :
                                      @Set.Elem.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)),
                                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3}
                                        C inst C inst C inst
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (Set.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@Set.instMembership.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)
                                              x)
                                          s))
                                      κ
                                      (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                        hκ))
                              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2}
                                C inst inst_1 P inst_2))))
                        (@DistribLattice.toLattice.{u_1}
                          (Ordinal.ToType.{u_1}
                            (Cardinal.ord.{u_1}
                              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                (fun (κ : Cardinal.{u_1}) =>
                                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                    ∀
                                      (s :
                                        @Set.Elem.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)),
                                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                        inst
                                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                              u_3}
                                          C inst C inst C inst
                                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (fun
                                                (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                (Set.{max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                (@Set.instMembership.{max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                      u_3}
                                                  C inst P)
                                                x)
                                            s))
                                        κ
                                        (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                          hκ))
                                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                      u_2}
                                  C inst inst_1 P inst_2))))
                          (@instDistribLatticeOfLinearOrder.{u_1}
                            (Ordinal.ToType.{u_1}
                              (Cardinal.ord.{u_1}
                                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                  (fun (κ : Cardinal.{u_1}) =>
                                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                      ∀
                                        (s :
                                          @Set.Elem.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)),
                                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                          inst
                                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                                u_3}
                                            C inst C inst C inst
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (fun
                                                  (x :
                                                    @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                  (Set.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@Set.instMembership.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                        u_3}
                                                    C inst P)
                                                  x)
                                              s))
                                          κ
                                          (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                            κ hκ))
                                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                        u_2}
                                    C inst inst_1 P inst_2))))
                            (linearOrder_toType.{u_1}
                              (Cardinal.ord.{u_1}
                                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                  (fun (κ : Cardinal.{u_1}) =>
                                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                      ∀
                                        (s :
                                          @Set.Elem.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)),
                                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                          inst
                                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                                u_3}
                                            C inst C inst C inst
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (fun
                                                  (x :
                                                    @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                  (Set.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@Set.instMembership.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                        u_3}
                                                    C inst P)
                                                  x)
                                              s))
                                          κ
                                          (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                            κ hκ))
                                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                        u_2}
                                    C inst inst_1 P inst_2)))))))))))
              (@Cardinal.toTypeOrderBot.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))
                (@Cardinal.IsRegular.ne_zero.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))
                  hκ)))
            (Ordinal.instSuccOrderToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (wellFoundedLT_toType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (fun
                (_x :
                  Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2)))) =>
              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P))
            (fun
                (_x :
                  Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                (i :
                  @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)) =>
              @CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C inst
                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                      (@Set.instMembership.{max u_3 u_2}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                  i))
            (fun
                (_x :
                  Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                (i :
                  @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)) =>
              @CategoryTheory.Comma.right.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C inst
                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                      (@Set.instMembership.{max u_3 u_2}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                  i))
            (fun
                (_x :
                  Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2)))) =>
              @CategoryTheory.MorphismProperty.homFamily.{u_2, u_3} C inst P)
            X Y f) =>
      @inferInstance.{0}
        (@CategoryTheory.Limits.PreservesColimit.{u_1, u_1, u_2, u_2, u_3, u_2 + 1} C inst
          (Type u_2) CategoryTheory.types.{u_2}
          (Ordinal.ToType.{u_1}
            (Cardinal.ord.{u_1}
              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                (fun (κ : Cardinal.{u_1}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@Set.instMembership.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                            s))
                        κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1
                  P inst_2))))
          (@Preorder.smallCategory.{u_1}
            (Ordinal.ToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (@PartialOrder.toPreorder.{u_1}
              (Ordinal.ToType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (@SemilatticeInf.toPartialOrder.{u_1}
                (Ordinal.ToType.{u_1}
                  (Cardinal.ord.{u_1}
                    (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                      (fun (κ : Cardinal.{u_1}) =>
                        @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                          fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                          ∀
                            (s :
                              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                            @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                              (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst
                                C inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (Set.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@Set.instMembership.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)
                                      x)
                                  s))
                              κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                      (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                        inst_1 P inst_2))))
                (@Lattice.toSemilatticeInf.{u_1}
                  (Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                  (@DistribLattice.toLattice.{u_1}
                    (Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                    (@instDistribLatticeOfLinearOrder.{u_1}
                      (Ordinal.ToType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))
                      (linearOrder_toType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))))))))
          (@CategoryTheory.TransfiniteCompositionOfShape.F.{u_1, u_2, u_3} C inst
            (Ordinal.ToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (linearOrder_toType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (@inferInstance.{u_1 + 1}
              (@OrderBot.{u_1}
                (Ordinal.ToType.{u_1}
                  (Cardinal.ord.{u_1}
                    (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                      (fun (κ : Cardinal.{u_1}) =>
                        @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                          fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                          ∀
                            (s :
                              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                            @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                              (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst
                                C inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (Set.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@Set.instMembership.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)
                                      x)
                                  s))
                              κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                      (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                        inst_1 P inst_2))))
                (@Preorder.toLE.{u_1}
                  (Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                  (@PartialOrder.toPreorder.{u_1}
                    (Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                    (@SemilatticeInf.toPartialOrder.{u_1}
                      (Ordinal.ToType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))
                      (@Lattice.toSemilatticeInf.{u_1}
                        (Ordinal.ToType.{u_1}
                          (Cardinal.ord.{u_1}
                            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                              (fun (κ : Cardinal.{u_1}) =>
                                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                  ∀
                                    (s :
                                      @Set.Elem.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)),
                                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3}
                                        C inst C inst C inst
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (Set.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@Set.instMembership.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)
                                              x)
                                          s))
                                      κ
                                      (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                        hκ))
                              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2}
                                C inst inst_1 P inst_2))))
                        (@DistribLattice.toLattice.{u_1}
                          (Ordinal.ToType.{u_1}
                            (Cardinal.ord.{u_1}
                              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                (fun (κ : Cardinal.{u_1}) =>
                                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                    ∀
                                      (s :
                                        @Set.Elem.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)),
                                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                        inst
                                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                              u_3}
                                          C inst C inst C inst
                                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (fun
                                                (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                (Set.{max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                (@Set.instMembership.{max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                      u_3}
                                                  C inst P)
                                                x)
                                            s))
                                        κ
                                        (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                          hκ))
                                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                      u_2}
                                  C inst inst_1 P inst_2))))
                          (@instDistribLatticeOfLinearOrder.{u_1}
                            (Ordinal.ToType.{u_1}
                              (Cardinal.ord.{u_1}
                                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                  (fun (κ : Cardinal.{u_1}) =>
                                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                      ∀
                                        (s :
                                          @Set.Elem.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)),
                                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                          inst
                                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                                u_3}
                                            C inst C inst C inst
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (fun
                                                  (x :
                                                    @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                  (Set.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@Set.instMembership.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                        u_3}
                                                    C inst P)
                                                  x)
                                              s))
                                          κ
                                          (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                            κ hκ))
                                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                        u_2}
                                    C inst inst_1 P inst_2))))
                            (linearOrder_toType.{u_1}
                              (Cardinal.ord.{u_1}
                                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                  (fun (κ : Cardinal.{u_1}) =>
                                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                      ∀
                                        (s :
                                          @Set.Elem.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)),
                                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                          inst
                                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                                u_3}
                                            C inst C inst C inst
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (fun
                                                  (x :
                                                    @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                  (Set.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@Set.instMembership.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                        u_3}
                                                    C inst P)
                                                  x)
                                              s))
                                          κ
                                          (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                            κ hκ))
                                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                        u_2}
                                    C inst inst_1 P inst_2)))))))))))
              (@Cardinal.toTypeOrderBot.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))
                (@Cardinal.IsRegular.ne_zero.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))
                  hκ)))
            X Y f
            (Ordinal.instSuccOrderToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (wellFoundedLT_toType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (@HomotopicalAlgebra.RelativeCellComplex.toTransfiniteCompositionOfShape.{u_1, u_1,
                  max u_3 u_2, u_2, u_3}
              C inst
              (Ordinal.ToType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (linearOrder_toType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (@inferInstance.{u_1 + 1}
                (@OrderBot.{u_1}
                  (Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                  (@Preorder.toLE.{u_1}
                    (Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                    (@PartialOrder.toPreorder.{u_1}
                      (Ordinal.ToType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))
                      (@SemilatticeInf.toPartialOrder.{u_1}
                        (Ordinal.ToType.{u_1}
                          (Cardinal.ord.{u_1}
                            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                              (fun (κ : Cardinal.{u_1}) =>
                                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                  ∀
                                    (s :
                                      @Set.Elem.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)),
                                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3}
                                        C inst C inst C inst
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (Set.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@Set.instMembership.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)
                                              x)
                                          s))
                                      κ
                                      (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                        hκ))
                              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2}
                                C inst inst_1 P inst_2))))
                        (@Lattice.toSemilatticeInf.{u_1}
                          (Ordinal.ToType.{u_1}
                            (Cardinal.ord.{u_1}
                              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                (fun (κ : Cardinal.{u_1}) =>
                                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                    ∀
                                      (s :
                                        @Set.Elem.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)),
                                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                        inst
                                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                              u_3}
                                          C inst C inst C inst
                                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (fun
                                                (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                (Set.{max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                (@Set.instMembership.{max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                      u_3}
                                                  C inst P)
                                                x)
                                            s))
                                        κ
                                        (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                          hκ))
                                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                      u_2}
                                  C inst inst_1 P inst_2))))
                          (@DistribLattice.toLattice.{u_1}
                            (Ordinal.ToType.{u_1}
                              (Cardinal.ord.{u_1}
                                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                  (fun (κ : Cardinal.{u_1}) =>
                                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                      ∀
                                        (s :
                                          @Set.Elem.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)),
                                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                          inst
                                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                                u_3}
                                            C inst C inst C inst
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (fun
                                                  (x :
                                                    @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                  (Set.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@Set.instMembership.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                        u_3}
                                                    C inst P)
                                                  x)
                                              s))
                                          κ
                                          (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                            κ hκ))
                                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                        u_2}
                                    C inst inst_1 P inst_2))))
                            (@instDistribLatticeOfLinearOrder.{u_1}
                              (Ordinal.ToType.{u_1}
                                (Cardinal.ord.{u_1}
                                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                    (fun (κ : Cardinal.{u_1}) =>
                                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                        ∀
                                          (s :
                                            @Set.Elem.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)),
                                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3}
                                            C inst
                                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3,
                                                  u_3, u_3}
                                              C inst C inst C inst
                                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                (fun
                                                    (x :
                                                      @CategoryTheory.Arrow.{u_2, u_3} C
                                                        inst) =>
                                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                    (Set.{max u_3 u_2}
                                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                    (@Set.instMembership.{max u_3 u_2}
                                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                    (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                          u_3}
                                                      C inst P)
                                                    x)
                                                s))
                                            κ
                                            (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                              κ hκ))
                                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                          u_2}
                                      C inst inst_1 P inst_2))))
                              (linearOrder_toType.{u_1}
                                (Cardinal.ord.{u_1}
                                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                    (fun (κ : Cardinal.{u_1}) =>
                                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                        ∀
                                          (s :
                                            @Set.Elem.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)),
                                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3}
                                            C inst
                                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3,
                                                  u_3, u_3}
                                              C inst C inst C inst
                                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                (fun
                                                    (x :
                                                      @CategoryTheory.Arrow.{u_2, u_3} C
                                                        inst) =>
                                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                    (Set.{max u_3 u_2}
                                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                    (@Set.instMembership.{max u_3 u_2}
                                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                    (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                          u_3}
                                                      C inst P)
                                                    x)
                                                s))
                                            κ
                                            (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                              κ hκ))
                                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                          u_2}
                                      C inst inst_1 P inst_2)))))))))))
                (@Cardinal.toTypeOrderBot.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))
                  (@Cardinal.IsRegular.ne_zero.{u_1}
                    (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                      (fun (κ : Cardinal.{u_1}) =>
                        @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                          fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                          ∀
                            (s :
                              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                            @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                              (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst
                                C inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (Set.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@Set.instMembership.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)
                                      x)
                                  s))
                              κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                      (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                        inst_1 P inst_2))
                    hκ)))
              (Ordinal.instSuccOrderToType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (wellFoundedLT_toType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (fun
                  (_x :
                    Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2)))) =>
                @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P))
              (fun
                  (_x :
                    Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                  (i :
                    @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)) =>
                @CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                        (@Set.instMembership.{max u_3 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                    i))
              (fun
                  (_x :
                    Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                  (i :
                    @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)) =>
                @CategoryTheory.Comma.right.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                        (@Set.instMembership.{max u_3 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                    i))
              (fun
                  (_x :
                    Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2)))) =>
                @CategoryTheory.MorphismProperty.homFamily.{u_2, u_3} C inst P)
              X Y f hf))
          (@CategoryTheory.Functor.obj.{u_2, max u_3 u_2, u_3, max u_3 (u_2 + 1)}
            (Opposite.{u_3 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_3} C inst)
            (@CategoryTheory.Functor.{u_2, u_2, u_3, u_2 + 1} C inst (Type u_2)
              CategoryTheory.types.{u_2})
            (@CategoryTheory.Functor.category.{u_2, u_2, u_3, u_2 + 1} C inst (Type u_2)
              CategoryTheory.types.{u_2})
            (@CategoryTheory.coyoneda.{u_2, u_3} C inst) (@Opposite.op.{u_3 + 1} C A)))
        (@CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit.{u_1, u_1, u_2, u_2,
              u_3, u_2 + 1}
          C inst (Type u_2) CategoryTheory.types.{u_2}
          (Ordinal.ToType.{u_1}
            (Cardinal.ord.{u_1}
              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                (fun (κ : Cardinal.{u_1}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@Set.instMembership.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                            s))
                        κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1
                  P inst_2))))
          (@Preorder.smallCategory.{u_1}
            (Ordinal.ToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (@PartialOrder.toPreorder.{u_1}
              (Ordinal.ToType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (@SemilatticeInf.toPartialOrder.{u_1}
                (Ordinal.ToType.{u_1}
                  (Cardinal.ord.{u_1}
                    (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                      (fun (κ : Cardinal.{u_1}) =>
                        @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                          fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                          ∀
                            (s :
                              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                            @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                              (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst
                                C inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (Set.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@Set.instMembership.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)
                                      x)
                                  s))
                              κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                      (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                        inst_1 P inst_2))))
                (@Lattice.toSemilatticeInf.{u_1}
                  (Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                  (@DistribLattice.toLattice.{u_1}
                    (Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                    (@instDistribLatticeOfLinearOrder.{u_1}
                      (Ordinal.ToType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))
                      (linearOrder_toType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))))))))
          (@CategoryTheory.Functor.obj.{u_2, max u_3 u_2, u_3, max u_3 (u_2 + 1)}
            (Opposite.{u_3 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_3} C inst)
            (@CategoryTheory.Functor.{u_2, u_2, u_3, u_2 + 1} C inst (Type u_2)
              CategoryTheory.types.{u_2})
            (@CategoryTheory.Functor.category.{u_2, u_2, u_3, u_2 + 1} C inst (Type u_2)
              CategoryTheory.types.{u_2})
            (@CategoryTheory.coyoneda.{u_2, u_3} C inst) (@Opposite.op.{u_3 + 1} C A))
          (@CategoryTheory.preservesColimitsOfShape_of_isCardinalPresentable.{u_1, u_2, u_3} C
            inst A
            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
              (fun (κ : Cardinal.{u_1}) =>
                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                  ∀
                    (s :
                      @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C
                        inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                              (@Set.instMembership.{max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                          s))
                      κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1 P
                inst_2))
            (@Fact.mk
              (Cardinal.IsRegular.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2)))
              hκ)
            (hp
              (@Subtype.mk.{max (u_3 + 1) (u_2 + 1)} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                    (@Set.instMembership.{max u_3 u_2}
                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                (@CategoryTheory.Arrow.mk.{u_2, u_3} C inst A B i) hi))
            (Ordinal.ToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (@Preorder.smallCategory.{u_1}
              (Ordinal.ToType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (@PartialOrder.toPreorder.{u_1}
                (Ordinal.ToType.{u_1}
                  (Cardinal.ord.{u_1}
                    (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                      (fun (κ : Cardinal.{u_1}) =>
                        @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                          fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                          ∀
                            (s :
                              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                            @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                              (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst
                                C inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (Set.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@Set.instMembership.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)
                                      x)
                                  s))
                              κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                      (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                        inst_1 P inst_2))))
                (@SemilatticeInf.toPartialOrder.{u_1}
                  (Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                  (@Lattice.toSemilatticeInf.{u_1}
                    (Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                    (@DistribLattice.toLattice.{u_1}
                      (Ordinal.ToType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))
                      (@instDistribLatticeOfLinearOrder.{u_1}
                        (Ordinal.ToType.{u_1}
                          (Cardinal.ord.{u_1}
                            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                              (fun (κ : Cardinal.{u_1}) =>
                                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                  ∀
                                    (s :
                                      @Set.Elem.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)),
                                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3}
                                        C inst C inst C inst
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (Set.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@Set.instMembership.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)
                                              x)
                                          s))
                                      κ
                                      (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                        hκ))
                              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2}
                                C inst inst_1 P inst_2))))
                        (linearOrder_toType.{u_1}
                          (Cardinal.ord.{u_1}
                            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                              (fun (κ : Cardinal.{u_1}) =>
                                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                  ∀
                                    (s :
                                      @Set.Elem.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)),
                                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3}
                                        C inst C inst C inst
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (Set.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@Set.instMembership.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)
                                              x)
                                          s))
                                      κ
                                      (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                        hκ))
                              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2}
                                C inst inst_1 P inst_2))))))))))
            (@CategoryTheory.instIsCardinalFilteredToTypeOrd.{u_1}
              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                (fun (κ : Cardinal.{u_1}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@Set.instMembership.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                            s))
                        κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst inst_1
                  P inst_2))
              (@Fact.mk
                (Cardinal.IsRegular.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2)))
                hκ)))
          (@CategoryTheory.TransfiniteCompositionOfShape.F.{u_1, u_2, u_3} C inst
            (Ordinal.ToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (linearOrder_toType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (@inferInstance.{u_1 + 1}
              (@OrderBot.{u_1}
                (Ordinal.ToType.{u_1}
                  (Cardinal.ord.{u_1}
                    (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                      (fun (κ : Cardinal.{u_1}) =>
                        @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                          fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                          ∀
                            (s :
                              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                            @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                              (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst
                                C inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (Set.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@Set.instMembership.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)
                                      x)
                                  s))
                              κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                      (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                        inst_1 P inst_2))))
                (@Preorder.toLE.{u_1}
                  (Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                  (@PartialOrder.toPreorder.{u_1}
                    (Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                    (@SemilatticeInf.toPartialOrder.{u_1}
                      (Ordinal.ToType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))
                      (@Lattice.toSemilatticeInf.{u_1}
                        (Ordinal.ToType.{u_1}
                          (Cardinal.ord.{u_1}
                            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                              (fun (κ : Cardinal.{u_1}) =>
                                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                  ∀
                                    (s :
                                      @Set.Elem.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)),
                                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3}
                                        C inst C inst C inst
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (Set.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@Set.instMembership.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)
                                              x)
                                          s))
                                      κ
                                      (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                        hκ))
                              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2}
                                C inst inst_1 P inst_2))))
                        (@DistribLattice.toLattice.{u_1}
                          (Ordinal.ToType.{u_1}
                            (Cardinal.ord.{u_1}
                              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                (fun (κ : Cardinal.{u_1}) =>
                                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                    ∀
                                      (s :
                                        @Set.Elem.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)),
                                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                        inst
                                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                              u_3}
                                          C inst C inst C inst
                                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (fun
                                                (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                (Set.{max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                (@Set.instMembership.{max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                      u_3}
                                                  C inst P)
                                                x)
                                            s))
                                        κ
                                        (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                          hκ))
                                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                      u_2}
                                  C inst inst_1 P inst_2))))
                          (@instDistribLatticeOfLinearOrder.{u_1}
                            (Ordinal.ToType.{u_1}
                              (Cardinal.ord.{u_1}
                                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                  (fun (κ : Cardinal.{u_1}) =>
                                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                      ∀
                                        (s :
                                          @Set.Elem.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)),
                                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                          inst
                                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                                u_3}
                                            C inst C inst C inst
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (fun
                                                  (x :
                                                    @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                  (Set.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@Set.instMembership.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                        u_3}
                                                    C inst P)
                                                  x)
                                              s))
                                          κ
                                          (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                            κ hκ))
                                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                        u_2}
                                    C inst inst_1 P inst_2))))
                            (linearOrder_toType.{u_1}
                              (Cardinal.ord.{u_1}
                                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                  (fun (κ : Cardinal.{u_1}) =>
                                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                      ∀
                                        (s :
                                          @Set.Elem.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)),
                                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                          inst
                                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                                u_3}
                                            C inst C inst C inst
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (fun
                                                  (x :
                                                    @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                  (Set.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@Set.instMembership.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                        u_3}
                                                    C inst P)
                                                  x)
                                              s))
                                          κ
                                          (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                            κ hκ))
                                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                        u_2}
                                    C inst inst_1 P inst_2)))))))))))
              (@Cardinal.toTypeOrderBot.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))
                (@Cardinal.IsRegular.ne_zero.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))
                  hκ)))
            X Y f
            (Ordinal.instSuccOrderToType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (wellFoundedLT_toType.{u_1}
              (Cardinal.ord.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@Set.instMembership.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                  x)
                              s))
                          κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                    inst_1 P inst_2))))
            (@HomotopicalAlgebra.RelativeCellComplex.toTransfiniteCompositionOfShape.{u_1, u_1,
                  max u_3 u_2, u_2, u_3}
              C inst
              (Ordinal.ToType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (linearOrder_toType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (@inferInstance.{u_1 + 1}
                (@OrderBot.{u_1}
                  (Ordinal.ToType.{u_1}
                    (Cardinal.ord.{u_1}
                      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                        (fun (κ : Cardinal.{u_1}) =>
                          @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                            fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                            ∀
                              (s :
                                @Set.Elem.{max u_3 u_2}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                              @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                  inst C inst C inst
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (Set.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@Set.instMembership.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)
                                        x)
                                    s))
                                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                          inst_1 P inst_2))))
                  (@Preorder.toLE.{u_1}
                    (Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                    (@PartialOrder.toPreorder.{u_1}
                      (Ordinal.ToType.{u_1}
                        (Cardinal.ord.{u_1}
                          (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                            (fun (κ : Cardinal.{u_1}) =>
                              @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                ∀
                                  (s :
                                    @Set.Elem.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)),
                                  @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                    (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                      inst C inst C inst
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                      (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                          @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (Set.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@Set.instMembership.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)
                                            x)
                                        s))
                                    κ
                                    (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                      hκ))
                            (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                              inst inst_1 P inst_2))))
                      (@SemilatticeInf.toPartialOrder.{u_1}
                        (Ordinal.ToType.{u_1}
                          (Cardinal.ord.{u_1}
                            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                              (fun (κ : Cardinal.{u_1}) =>
                                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                  ∀
                                    (s :
                                      @Set.Elem.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                          inst P)),
                                    @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                      (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3}
                                        C inst C inst C inst
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                        (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                            @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (Set.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@Set.instMembership.{max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)
                                              x)
                                          s))
                                      κ
                                      (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                        hκ))
                              (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2}
                                C inst inst_1 P inst_2))))
                        (@Lattice.toSemilatticeInf.{u_1}
                          (Ordinal.ToType.{u_1}
                            (Cardinal.ord.{u_1}
                              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                (fun (κ : Cardinal.{u_1}) =>
                                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                    ∀
                                      (s :
                                        @Set.Elem.{max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)),
                                      @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                        inst
                                        (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                              u_3}
                                          C inst C inst C inst
                                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                          (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                          (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (fun
                                                (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                              @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                (Set.{max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                (@Set.instMembership.{max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                      u_3}
                                                  C inst P)
                                                x)
                                            s))
                                        κ
                                        (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ
                                          hκ))
                                (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                      u_2}
                                  C inst inst_1 P inst_2))))
                          (@DistribLattice.toLattice.{u_1}
                            (Ordinal.ToType.{u_1}
                              (Cardinal.ord.{u_1}
                                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                  (fun (κ : Cardinal.{u_1}) =>
                                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                      ∀
                                        (s :
                                          @Set.Elem.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                            (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                              inst P)),
                                        @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C
                                          inst
                                          (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3,
                                                u_3}
                                            C inst C inst C inst
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                            (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (fun
                                                  (x :
                                                    @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                                @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                  (Set.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@Set.instMembership.{max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                  (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                        u_3}
                                                    C inst P)
                                                  x)
                                              s))
                                          κ
                                          (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                            κ hκ))
                                  (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                        u_2}
                                    C inst inst_1 P inst_2))))
                            (@instDistribLatticeOfLinearOrder.{u_1}
                              (Ordinal.ToType.{u_1}
                                (Cardinal.ord.{u_1}
                                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                    (fun (κ : Cardinal.{u_1}) =>
                                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                        ∀
                                          (s :
                                            @Set.Elem.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)),
                                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3}
                                            C inst
                                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3,
                                                  u_3, u_3}
                                              C inst C inst C inst
                                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                (fun
                                                    (x :
                                                      @CategoryTheory.Arrow.{u_2, u_3} C
                                                        inst) =>
                                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                    (Set.{max u_3 u_2}
                                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                    (@Set.instMembership.{max u_3 u_2}
                                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                    (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                          u_3}
                                                      C inst P)
                                                    x)
                                                s))
                                            κ
                                            (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                              κ hκ))
                                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                          u_2}
                                      C inst inst_1 P inst_2))))
                              (linearOrder_toType.{u_1}
                                (Cardinal.ord.{u_1}
                                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                                    (fun (κ : Cardinal.{u_1}) =>
                                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                                        ∀
                                          (s :
                                            @Set.Elem.{max u_3 u_2}
                                              (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3}
                                                C inst P)),
                                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3}
                                            C inst
                                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3,
                                                  u_3, u_3}
                                              C inst C inst C inst
                                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                (fun
                                                    (x :
                                                      @CategoryTheory.Arrow.{u_2, u_3} C
                                                        inst) =>
                                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                                    (Set.{max u_3 u_2}
                                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                    (@Set.instMembership.{max u_3 u_2}
                                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                                    (@CategoryTheory.MorphismProperty.toSet.{u_2,
                                                          u_3}
                                                      C inst P)
                                                    x)
                                                s))
                                            κ
                                            (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1}
                                              κ hκ))
                                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3,
                                          u_2}
                                      C inst inst_1 P inst_2)))))))))))
                (@Cardinal.toTypeOrderBot.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))
                  (@Cardinal.IsRegular.ne_zero.{u_1}
                    (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                      (fun (κ : Cardinal.{u_1}) =>
                        @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                          fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                          ∀
                            (s :
                              @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                            @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                              (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst
                                C inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                  (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                  (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                    @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (Set.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@Set.instMembership.{max u_3 u_2}
                                        (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                        P)
                                      x)
                                  s))
                              κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                      (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                        inst_1 P inst_2))
                    hκ)))
              (Ordinal.instSuccOrderToType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (wellFoundedLT_toType.{u_1}
                (Cardinal.ord.{u_1}
                  (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                    (fun (κ : Cardinal.{u_1}) =>
                      @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                        fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                        ∀
                          (s :
                            @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                              (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)),
                          @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                            (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C
                              inst C inst (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                              (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                  @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (Set.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@Set.instMembership.{max u_3 u_2}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)
                                    x)
                                s))
                            κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                    (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C inst
                      inst_1 P inst_2))))
              (fun
                  (_x :
                    Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2)))) =>
                @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P))
              (fun
                  (_x :
                    Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                  (i :
                    @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)) =>
                @CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                        (@Set.instMembership.{max u_3 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                    i))
              (fun
                  (_x :
                    Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2))))
                  (i :
                    @Set.Elem.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P)) =>
                @CategoryTheory.Comma.right.{u_2, u_2, u_2, u_3, u_3, u_3} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                  (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                  (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                      @Membership.mem.{max u_3 u_2, max u_3 u_2}
                        (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                        (Set.{max u_3 u_2} (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                        (@Set.instMembership.{max u_3 u_2}
                          (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst P) x)
                    i))
              (fun
                  (_x :
                    Ordinal.ToType.{u_1}
                      (Cardinal.ord.{u_1}
                        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                          (fun (κ : Cardinal.{u_1}) =>
                            @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                              fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                              ∀
                                (s :
                                  @Set.Elem.{max u_3 u_2}
                                    (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                    (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C inst
                                      P)),
                                @CategoryTheory.IsCardinalPresentable.{u_1, u_2, u_3} C inst
                                  (@CategoryTheory.Comma.left.{u_2, u_2, u_2, u_3, u_3, u_3} C
                                    inst C inst C inst
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@CategoryTheory.Functor.id.{u_2, u_3} C inst)
                                    (@Subtype.val.{max (u_3 + 1) (u_2 + 1)}
                                      (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                      (fun (x : @CategoryTheory.Arrow.{u_2, u_3} C inst) =>
                                        @Membership.mem.{max u_3 u_2, max u_3 u_2}
                                          (@CategoryTheory.Arrow.{u_2, u_3} C inst)
                                          (Set.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@Set.instMembership.{max u_3 u_2}
                                            (@CategoryTheory.Arrow.{u_2, u_3} C inst))
                                          (@CategoryTheory.MorphismProperty.toSet.{u_2, u_3} C
                                            inst P)
                                          x)
                                      s))
                                  κ
                                  (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
                          (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_3, u_2} C
                            inst inst_1 P inst_2)))) =>
                @CategoryTheory.MorphismProperty.homFamily.{u_2, u_3} C inst P)
              X Y f hf)))

theorem DaggerSmithSolutionSet.cardinalWitness._proof_3.{u_1, u_2, u_3} :
  ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C]
    [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_3, u_2} C inst]
    (P :
      @CategoryTheory.MorphismProperty.{u_3, u_2} C
        (@CategoryTheory.Category.toCategoryStruct.{u_3, u_2} C inst))
    [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_3, u_2} C inst P],
    Cardinal.IsRegular.{u_1}
      (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
        (fun (κ : Cardinal.{u_1}) =>
          @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
            ∀
              (s :
                @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
              @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                  (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                  (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                    (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                      @Membership.mem.{max u_2 u_3, max u_2 u_3}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                        (@Set.instMembership.{max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                    s))
                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{u_1} κ hκ))
        (@DaggerSmithSolutionSet.cardinalWitness._proof_2.{u_1, u_2, u_3} C inst inst_1 P
          inst_2)) :=
  fun {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_3, u_2} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{u_3, u_2} C
          (@CategoryTheory.Category.toCategoryStruct.{u_3, u_2} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_3, u_2} C inst P] =>
    @Exists.choose.{0}
      (Cardinal.IsRegular.{u_1}
        (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
          (fun (κ : Cardinal.{u_1}) =>
            @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
              ∀
                (s :
                  @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                  (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                    inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                        @Membership.mem.{max u_2 u_3, max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@Set.instMembership.{max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                      s))
                  κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
          (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C inst
            inst_1
            (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
              (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
            (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst P
              inst_2)
            fun
              (s :
                @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
            @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
              (@Subtype.val.{max (u_2 + 1) (u_3 + 1)} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                  @Membership.mem.{max u_2 u_3, max u_2 u_3}
                    (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                    (@Set.instMembership.{max u_2 u_3}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                s))))
      (fun
          (hκ :
            Cardinal.IsRegular.{u_1}
              (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                (fun (κ : Cardinal.{u_1}) =>
                  @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                    fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                    ∀
                      (s :
                        @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                      @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                        (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst
                          C inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                          (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                          (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                              @Membership.mem.{max u_2 u_3, max u_2 u_3}
                                (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                                (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                                (@Set.instMembership.{max u_2 u_3}
                                  (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                                (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                            s))
                        κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
                (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C
                  inst inst_1
                  (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
                  (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst P
                    inst_2)
                  fun
                    (s :
                      @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
                  @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                    (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                        @Membership.mem.{max u_2 u_3, max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@Set.instMembership.{max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                      s)))) =>
        ∀
          (s :
            @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
              (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
          @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
            (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
              (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
              (@Subtype.val.{max (u_2 + 1) (u_3 + 1)} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                  @Membership.mem.{max u_2 u_3, max u_2 u_3}
                    (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                    (@Set.instMembership.{max u_2 u_3}
                      (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                    (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                s))
            (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
              (fun (κ : Cardinal.{u_1}) =>
                @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                  fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                  ∀
                    (s :
                      @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                    @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                      (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                        inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                        (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                        (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                            @Membership.mem.{max u_2 u_3, max u_2 u_3}
                              (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                              (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                              (@Set.instMembership.{max u_2 u_3}
                                (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                              (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                          s))
                      κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
              (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C inst
                inst_1
                (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
                (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst P
                  inst_2)
                fun
                  (s :
                    @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
                @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                  (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                  (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                    (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                      @Membership.mem.{max u_2 u_3, max u_2 u_3}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                        (@Set.instMembership.{max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                    s)))
            (@Fact.mk
              (Cardinal.IsRegular.{u_1}
                (@Exists.choose.{u_1 + 2} Cardinal.{u_1}
                  (fun (κ : Cardinal.{u_1}) =>
                    @Exists.{0} (Cardinal.IsRegular.{u_1} κ)
                      fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
                      ∀
                        (s :
                          @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
                        @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                          (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C
                            inst C inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                            (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                            (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                              (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                              (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                                @Membership.mem.{max u_2 u_3, max u_2 u_3}
                                  (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                                  (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                                  (@Set.instMembership.{max u_2 u_3}
                                    (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                                  (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)
                                  x)
                              s))
                          κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
                  (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C
                    inst inst_1
                    (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                      (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
                    (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst
                      P inst_2)
                    fun
                      (s :
                        @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                          (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
                    @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C
                      inst (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                      (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                          @Membership.mem.{max u_2 u_3, max u_2 u_3}
                            (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                            (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@Set.instMembership.{max u_2 u_3}
                              (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                        s))))
              hκ))
      (@Exists.choose_spec.{u_1 + 2} Cardinal.{u_1}
        (fun (κ : Cardinal.{u_1}) =>
          @Exists.{0} (Cardinal.IsRegular.{u_1} κ) fun (hκ : Cardinal.IsRegular.{u_1} κ) =>
            ∀
              (s :
                @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)),
              @CategoryTheory.IsCardinalPresentable.{u_1, u_3, u_2} C inst
                (@CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                  (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
                  (@Subtype.val.{max (u_2 + 1) (u_3 + 1)}
                    (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                    (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                      @Membership.mem.{max u_2 u_3, max u_2 u_3}
                        (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                        (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                        (@Set.instMembership.{max u_2 u_3}
                          (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
                    s))
                κ (@Fact.mk (Cardinal.IsRegular.{u_1} κ) hκ))
        (@DaggerSmithSolutionSet.uniformPresentability.{u_1, u_3, u_2, max u_2 u_3} C inst
          inst_1
          (@Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
            (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P))
          (@CategoryTheory.MorphismProperty.IsSmall.small_toSet.{u_1, u_3, u_2} C inst P inst_2)
          fun
            (s :
              @Set.Elem.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P)) =>
          @CategoryTheory.Comma.left.{u_3, u_3, u_3, u_2, u_2, u_2} C inst C inst C inst
            (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
            (@CategoryTheory.Functor.id.{u_3, u_2} C inst)
            (@Subtype.val.{max (u_2 + 1) (u_3 + 1)} (@CategoryTheory.Arrow.{u_3, u_2} C inst)
              (fun (x : @CategoryTheory.Arrow.{u_3, u_2} C inst) =>
                @Membership.mem.{max u_2 u_3, max u_2 u_3}
                  (@CategoryTheory.Arrow.{u_3, u_2} C inst)
                  (Set.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                  (@Set.instMembership.{max u_2 u_3} (@CategoryTheory.Arrow.{u_3, u_2} C inst))
                  (@CategoryTheory.MorphismProperty.toSet.{u_3, u_2} C inst P) x)
              s)))

noncomputable def DaggerSmithSolutionSet.cardinalWitness.{w, v, u} :
  {C : Type u} →
    [inst : CategoryTheory.Category.{v, u} C] →
      [@CategoryTheory.IsLocallyPresentable.{w, v, u} C inst] →
        (P :
            @CategoryTheory.MorphismProperty.{v, u} C
              (@CategoryTheory.Category.toCategoryStruct.{v, u} C inst)) →
          [@CategoryTheory.MorphismProperty.IsSmall.{w, v, u} C inst P] →
            @DaggerSmithSolutionSet.CardinalWitness.{w, v, u} C inst P :=
  fun {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{w, v, u} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{v, u} C
          (@CategoryTheory.Category.toCategoryStruct.{v, u} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{w, v, u} C inst P] =>
    have h := @DaggerSmithSolutionSet.cardinalWitness._proof_2.{w, u, v} C inst inst_1 P inst_2;
    let κ :=
      @Exists.choose.{w + 2} Cardinal.{w}
        (fun (κ : Cardinal.{w}) =>
          @Exists.{0} (Cardinal.IsRegular.{w} κ) fun (hκ : Cardinal.IsRegular.{w} κ) =>
            ∀
              (s :
                @Set.Elem.{max u v} (@CategoryTheory.Arrow.{v, u} C inst)
                  (@CategoryTheory.MorphismProperty.toSet.{v, u} C inst P)),
              @CategoryTheory.IsCardinalPresentable.{w, v, u} C inst
                (@CategoryTheory.Comma.left.{v, v, v, u, u, u} C inst C inst C inst
                  (@CategoryTheory.Functor.id.{v, u} C inst)
                  (@CategoryTheory.Functor.id.{v, u} C inst)
                  (@Subtype.val.{max (u + 1) (v + 1)} (@CategoryTheory.Arrow.{v, u} C inst)
                    (fun (x : @CategoryTheory.Arrow.{v, u} C inst) =>
                      @Membership.mem.{max u v, max u v} (@CategoryTheory.Arrow.{v, u} C inst)
                        (Set.{max u v} (@CategoryTheory.Arrow.{v, u} C inst))
                        (@Set.instMembership.{max u v} (@CategoryTheory.Arrow.{v, u} C inst))
                        (@CategoryTheory.MorphismProperty.toSet.{v, u} C inst P) x)
                    s))
                κ (DaggerSmithSolutionSet.cardinalWitness._proof_1.{w} κ hκ))
        h;
    have hκ :=
      @DaggerSmithSolutionSet.cardinalWitness._proof_3.{w, u, v} C inst inst_1 P inst_2;
    have hp :=
      @DaggerSmithSolutionSet.cardinalWitness._proof_5.{u, v, w} C inst inst_1 P inst_2;
    @DaggerSmithSolutionSet.CardinalWitness.mk.{w, v, u} C inst P κ hκ
      (@inferInstance.{w + 1}
        (@OrderBot.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
          (@Preorder.toLE.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
            (@PartialOrder.toPreorder.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
              (@SemilatticeInf.toPartialOrder.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                (@Lattice.toSemilatticeInf.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                  (@DistribLattice.toLattice.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                    (@instDistribLatticeOfLinearOrder.{w}
                      (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                      (linearOrder_toType.{w} (Cardinal.ord.{w} κ)))))))))
        (@Cardinal.toTypeOrderBot.{w} κ (@Cardinal.IsRegular.ne_zero.{w} κ hκ)))
      (@DaggerSmithSolutionSet.cardinalWitness._proof_8.{w, v, u} C inst inst_1 P inst_2 hκ hp)

noncomputable def DaggerSmithSolutionSet.smallObjectArgument.{w, v, u} :
  ∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
    [@CategoryTheory.IsLocallyPresentable.{w, v, u} C inst]
    (P :
      @CategoryTheory.MorphismProperty.{v, u} C
        (@CategoryTheory.Category.toCategoryStruct.{v, u} C inst))
    [@CategoryTheory.MorphismProperty.IsSmall.{w, v, u} C inst P],
    @CategoryTheory.MorphismProperty.HasSmallObjectArgument.{w, v, u} C inst P :=
  fun {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{w, v, u} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{v, u} C
          (@CategoryTheory.Category.toCategoryStruct.{v, u} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{w, v, u} C inst P] =>
    let k := @DaggerSmithSolutionSet.cardinalWitness.{w, v, u} C inst inst_1 P inst_2;
    @CategoryTheory.MorphismProperty.HasSmallObjectArgument.mk.{w, v, u} C inst P
      (@Exists.intro.{w + 2} Cardinal.{w}
        (fun (κ : Cardinal.{w}) =>
          @Exists.{0} (Fact (Cardinal.IsRegular.{w} κ))
            fun (x : Fact (Cardinal.IsRegular.{w} κ)) =>
            @Exists.{w + 1}
              (@OrderBot.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                (@Preorder.toLE.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                  (@PartialOrder.toPreorder.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                    (@SemilatticeInf.toPartialOrder.{w}
                      (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                      (@Lattice.toSemilatticeInf.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                        (@DistribLattice.toLattice.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                          (@instDistribLatticeOfLinearOrder.{w}
                            (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                            (linearOrder_toType.{w} (Cardinal.ord.{w} κ)))))))))
              fun
                (x_1 :
                  @OrderBot.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                    (@Preorder.toLE.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                      (@PartialOrder.toPreorder.{w} (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                        (@SemilatticeInf.toPartialOrder.{w}
                          (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                          (@Lattice.toSemilatticeInf.{w}
                            (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                            (@DistribLattice.toLattice.{w}
                              (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                              (@instDistribLatticeOfLinearOrder.{w}
                                (Ordinal.ToType.{w} (Cardinal.ord.{w} κ))
                                (linearOrder_toType.{w} (Cardinal.ord.{w} κ))))))))) =>
              @CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.{w, v, u} C inst
                P κ x x_1)
        (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)
        (@Exists.intro.{0}
          (Fact
            (Cardinal.IsRegular.{w}
              (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
          (fun
              (x :
                Fact
                  (Cardinal.IsRegular.{w}
                    (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k))) =>
            @Exists.{w + 1}
              (@OrderBot.{w}
                (Ordinal.ToType.{w}
                  (Cardinal.ord.{w}
                    (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                (@Preorder.toLE.{w}
                  (Ordinal.ToType.{w}
                    (Cardinal.ord.{w}
                      (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                  (@PartialOrder.toPreorder.{w}
                    (Ordinal.ToType.{w}
                      (Cardinal.ord.{w}
                        (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                    (@SemilatticeInf.toPartialOrder.{w}
                      (Ordinal.ToType.{w}
                        (Cardinal.ord.{w}
                          (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                      (@Lattice.toSemilatticeInf.{w}
                        (Ordinal.ToType.{w}
                          (Cardinal.ord.{w}
                            (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                        (@DistribLattice.toLattice.{w}
                          (Ordinal.ToType.{w}
                            (Cardinal.ord.{w}
                              (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                          (@instDistribLatticeOfLinearOrder.{w}
                            (Ordinal.ToType.{w}
                              (Cardinal.ord.{w}
                                (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P
                                  k)))
                            (linearOrder_toType.{w}
                              (Cardinal.ord.{w}
                                (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P
                                  k))))))))))
              fun
                (x_1 :
                  @OrderBot.{w}
                    (Ordinal.ToType.{w}
                      (Cardinal.ord.{w}
                        (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                    (@Preorder.toLE.{w}
                      (Ordinal.ToType.{w}
                        (Cardinal.ord.{w}
                          (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                      (@PartialOrder.toPreorder.{w}
                        (Ordinal.ToType.{w}
                          (Cardinal.ord.{w}
                            (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                        (@SemilatticeInf.toPartialOrder.{w}
                          (Ordinal.ToType.{w}
                            (Cardinal.ord.{w}
                              (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                          (@Lattice.toSemilatticeInf.{w}
                            (Ordinal.ToType.{w}
                              (Cardinal.ord.{w}
                                (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P
                                  k)))
                            (@DistribLattice.toLattice.{w}
                              (Ordinal.ToType.{w}
                                (Cardinal.ord.{w}
                                  (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P
                                    k)))
                              (@instDistribLatticeOfLinearOrder.{w}
                                (Ordinal.ToType.{w}
                                  (Cardinal.ord.{w}
                                    (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst
                                      P k)))
                                (linearOrder_toType.{w}
                                  (Cardinal.ord.{w}
                                    (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst
                                      P k)))))))))) =>
              @CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.{w, v, u} C inst
                P (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k) x x_1)
          (@Fact.mk
            (Cardinal.IsRegular.{w}
              (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k))
            (@DaggerSmithSolutionSet.CardinalWitness.regular.{w, v, u} C inst P k))
          (@Exists.intro.{w + 1}
            (@OrderBot.{w}
              (Ordinal.ToType.{w}
                (Cardinal.ord.{w}
                  (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
              (@Preorder.toLE.{w}
                (Ordinal.ToType.{w}
                  (Cardinal.ord.{w}
                    (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                (@PartialOrder.toPreorder.{w}
                  (Ordinal.ToType.{w}
                    (Cardinal.ord.{w}
                      (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                  (@SemilatticeInf.toPartialOrder.{w}
                    (Ordinal.ToType.{w}
                      (Cardinal.ord.{w}
                        (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                    (@Lattice.toSemilatticeInf.{w}
                      (Ordinal.ToType.{w}
                        (Cardinal.ord.{w}
                          (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                      (@DistribLattice.toLattice.{w}
                        (Ordinal.ToType.{w}
                          (Cardinal.ord.{w}
                            (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                        (@instDistribLatticeOfLinearOrder.{w}
                          (Ordinal.ToType.{w}
                            (Cardinal.ord.{w}
                              (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                          (linearOrder_toType.{w}
                            (Cardinal.ord.{w}
                              (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P
                                k))))))))))
            (fun
                (x :
                  @OrderBot.{w}
                    (Ordinal.ToType.{w}
                      (Cardinal.ord.{w}
                        (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                    (@Preorder.toLE.{w}
                      (Ordinal.ToType.{w}
                        (Cardinal.ord.{w}
                          (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                      (@PartialOrder.toPreorder.{w}
                        (Ordinal.ToType.{w}
                          (Cardinal.ord.{w}
                            (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                        (@SemilatticeInf.toPartialOrder.{w}
                          (Ordinal.ToType.{w}
                            (Cardinal.ord.{w}
                              (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)))
                          (@Lattice.toSemilatticeInf.{w}
                            (Ordinal.ToType.{w}
                              (Cardinal.ord.{w}
                                (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P
                                  k)))
                            (@DistribLattice.toLattice.{w}
                              (Ordinal.ToType.{w}
                                (Cardinal.ord.{w}
                                  (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P
                                    k)))
                              (@instDistribLatticeOfLinearOrder.{w}
                                (Ordinal.ToType.{w}
                                  (Cardinal.ord.{w}
                                    (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst
                                      P k)))
                                (linearOrder_toType.{w}
                                  (Cardinal.ord.{w}
                                    (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst
                                      P k)))))))))) =>
              @CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.{w, v, u} C inst
                P (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)
                (@Fact.mk
                  (Cardinal.IsRegular.{w}
                    (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k))
                  (@DaggerSmithSolutionSet.CardinalWitness.regular.{w, v, u} C inst P k))
                x)
            (@DaggerSmithSolutionSet.CardinalWitness.orderBot.{w, v, u} C inst P k)
            (@DaggerSmithSolutionSet.CardinalWitness.suitable.{w, v, u} C inst P k))))

theorem DaggerSmithSolutionSet.soaFactorization._proof_1.{u_1, u_2, u_3} :
  ∀ {C : Type u_3} [inst : CategoryTheory.Category.{u_2, u_3} C]
    [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_2, u_3} C inst]
    (P :
      @CategoryTheory.MorphismProperty.{u_2, u_3} C
        (@CategoryTheory.Category.toCategoryStruct.{u_2, u_3} C inst))
    [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_2, u_3} C inst P],
    Fact
      (Cardinal.IsRegular.{u_1}
        (@DaggerSmithSolutionSet.CardinalWitness.κ.{u_1, u_2, u_3} C inst P
          (@DaggerSmithSolutionSet.cardinalWitness.{u_1, u_2, u_3} C inst inst_1 P inst_2))) :=
  fun {C : Type u_3} [inst : CategoryTheory.Category.{u_2, u_3} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{u_1, u_2, u_3} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{u_2, u_3} C
          (@CategoryTheory.Category.toCategoryStruct.{u_2, u_3} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{u_1, u_2, u_3} C inst P] =>
    @Fact.mk
      (Cardinal.IsRegular.{u_1}
        (@DaggerSmithSolutionSet.CardinalWitness.κ.{u_1, u_2, u_3} C inst P
          (@DaggerSmithSolutionSet.cardinalWitness.{u_1, u_2, u_3} C inst inst_1 P inst_2)))
      (@DaggerSmithSolutionSet.CardinalWitness.regular.{u_1, u_2, u_3} C inst P
        (@DaggerSmithSolutionSet.cardinalWitness.{u_1, u_2, u_3} C inst inst_1 P inst_2))

noncomputable def DaggerSmithSolutionSet.soaFactorization.{w, v, u} :
  {C : Type u} →
    [inst : CategoryTheory.Category.{v, u} C] →
      [@CategoryTheory.IsLocallyPresentable.{w, v, u} C inst] →
        (P :
            @CategoryTheory.MorphismProperty.{v, u} C
              (@CategoryTheory.Category.toCategoryStruct.{v, u} C inst)) →
          [@CategoryTheory.MorphismProperty.IsSmall.{w, v, u} C inst P] →
            @CategoryTheory.MorphismProperty.FunctorialFactorizationData.{v, u} C inst
              (@CategoryTheory.MorphismProperty.llp.{v, u} C inst
                (@CategoryTheory.MorphismProperty.rlp.{v, u} C inst P))
              (@CategoryTheory.MorphismProperty.rlp.{v, u} C inst P) :=
  fun {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
      [inst_1 : @CategoryTheory.IsLocallyPresentable.{w, v, u} C inst]
      (P :
        @CategoryTheory.MorphismProperty.{v, u} C
          (@CategoryTheory.Category.toCategoryStruct.{v, u} C inst))
      [inst_2 : @CategoryTheory.MorphismProperty.IsSmall.{w, v, u} C inst P] =>
    let k := @DaggerSmithSolutionSet.cardinalWitness.{w, v, u} C inst inst_1 P inst_2;
    @CategoryTheory.SmallObject.functorialFactorizationData.{w, v, u} C inst P
      (@DaggerSmithSolutionSet.CardinalWitness.κ.{w, v, u} C inst P k)
      (@DaggerSmithSolutionSet.soaFactorization._proof_1.{w, v, u} C inst inst_1 P inst_2)
      (@DaggerSmithSolutionSet.CardinalWitness.orderBot.{w, v, u} C inst P k)
      (@DaggerSmithSolutionSet.CardinalWitness.suitable.{w, v, u} C inst P k)

