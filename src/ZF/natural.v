Require Import AST.natural.natural.
Require Import AST.ZF.ZF.
(* CoreZFをもとに自然数を構築するモジュール *)
Module ZF_natural (core : CoreZF) <: CoreNatural.
    Include ZF core.
    (* 無限樹 *)
    Definition InfiniteTree (x : setType) :=
        x <> EmptySet /\
        forall y : setType, y In x -> Infinite y.
    
    (* 補題1 *)
    Lemma nature_infTree_intersection : forall a : setType, InfiniteTree a -> Infinite (|‾| a).
    Proof.
        intros.
        unfold Infinite.
        split.
        - (* 空集合を含むことの証明 *)
            unfold InfiniteTree in H.
            destruct H.
            apply nature_intersection.
            split.
            + (* aが空集合でないことの証明 *)
                apply not_empty.
                apply H.
            + (* aの任意の元が空集合を含むことの証明 *)
                intros.
                apply H0.
                apply H1.
        - (* 後者が含まれることの証明 *)
            intros.
            unfold InfiniteTree in H.
            destruct H.
            apply nature_intersection in H0.
            destruct H0 as [H2 H3].
            apply nature_intersection.
            split.
            + (* aが空集合でないことの証明 *)
                apply not_empty.
                apply H.
            + (* aの任意の元が後者を含むことの証明 *)
                intros.
                specialize (H1 a0 H0).
                unfold Infinite in H1.
                apply H1.
                apply H3.
                apply H0.
    Qed.

    (* 補題2 *)
    Lemma nature_infTree_include : forall a b : setType,
        InfiniteTree a -> InfiniteTree b ->
        a =| b -> |‾| a |= |‾| b.
    Proof.
        intros.
        apply include_intersection.
        unfold InfiniteTree in H0.
        apply H0.
        apply H1.
    Qed.

    (* 無限集合から無限樹を構成する関数 *)
    Definition InfiniteTreeFromInfinity (X : setType) : setType :=
        <: x In Pow X | Infinite x :>.

    (* 無限集合から構成した無限樹が無限樹であることの証明 *)
    Theorem nature_infinityToInfTree_infiniteTree : forall X : setType,
        Infinite X -> InfiniteTree (InfiniteTreeFromInfinity X).
    Proof.
        intros.
        unfold InfiniteTree.
        split.
        - (* <: x In Pow X | Infinite x :> が空集合でないことの証明 *)
            apply not_empty.
            exists X.
            apply SchemaOfSpecification.
            split.
            + (* X ∈ Pow X の証明 *)
                apply PowerSet.
                apply include_reflexivity.
            + (* X が無限集合であることの証明 *)
                apply H.
        - (* <: x In Pow X | Infinite x :> の任意の元が無限集合であることの証明 *)
            intros.
            apply SchemaOfSpecification in H0.
            apply H0.
    Qed.

    (* 無限集合から自然数集合を構成する関数 *)
    Definition NaturalFromInfinity (X : setType) : setType :=
        |‾| <: x In Pow X | Infinite x :>.

    (* 無限集合から構成した自然数集合が無限集合であることの証明 *)
    Theorem nature_naturalFromInfinity_infinite : forall X : setType,
        Infinite X -> Infinite (NaturalFromInfinity X).
    Proof.
        intros.
        apply nature_infTree_intersection.
        unfold InfiniteTree.
        split.
        - (* <: x In Pow X | Infinite x :> が空集合でないことの証明 *)
            apply not_empty.
            exists X.
            apply SchemaOfSpecification.
            split.
            + (* X ∈ Pow X の証明 *)
                apply PowerSet.
                apply include_reflexivity.
            + (* X が無限集合であることの証明 *)
                apply H.
        - (* <: x In Pow X | Infinite x :> の任意の元が無限集合であることの証明 *)
            intros.
            apply SchemaOfSpecification in H0.
            apply H0.
    Qed.

    (* 自然数集合の唯一性の証明 *)
    Theorem nature_natural_unique : forall A B : setType,
        Infinite A -> Infinite B ->
        NaturalFromInfinity A = NaturalFromInfinity B.
    Proof.
        assert (Hincl1 : forall A B : setType,
            Infinite A -> Infinite B ->
            NaturalFromInfinity A = NaturalFromInfinity (A /‾\ B)).
        {
            intros.
            apply include_eq.
            split.
            - (* 自然数集合Aが自然数集合A∩Bを含むことの証明 *)
                intro.
                intro.
                unfold NaturalFromInfinity.
                apply nature_intersection.
                split.
                + (* <: x In Pow A | Infinite x :> が空集合でないことの証明 *)
                    exists A.
                    apply SchemaOfSpecification.
                    split.
                    * (* A ∈ Pow A の証明 *)
                        apply PowerSet.
                        apply include_reflexivity.
                    * (* A が無限集合であることの証明 *)
                        apply H.
                + (* <: x In Pow A | Infinite x :> の任意の元が自然数集合A∩Bの任意の元を含むことの証明 *)
                    intro x.
                    intro.
                    apply (intersection_include x B).
                    apply nature_intersection in H1.
                    apply H1.
                    apply SchemaOfSpecification.
                    split.
                    * (* x /‾\ B In Pow (A /‾\ B) の証明 *)
                        apply PowerSet.
                        intro.
                        intros.
                        apply nature_intersection.
                        split.
                        -- (* <: A, B :> が空集合でないことの証明 *)
                            exists A.
                            apply pair_in.
                        -- (* A, Bのどちらもz0を含むことの証明 *)
                            intros.
                            apply Pairing in H4.
                            destruct H4.
                            ++ (* a = A の場合 *)
                                apply SchemaOfSpecification in H2.
                                destruct H2.
                                apply PowerSet in H2.
                                rewrite H4.
                                apply H2.
                                apply nature_intersection in H3.
                                apply H3.
                                apply pair_in.
                            ++ (* a = B の場合 *)
                                rewrite H4.
                                apply nature_intersection in H3.
                                apply H3.
                                apply pair_in.
                    * (* x /‾\ B が無限集合であることの証明 *)
                        apply nature_infTree_intersection.
                        unfold InfiniteTree.
                        split.
                        -- (* <: x, B :> が空集合でないことの証明 *)
                            intro.
                            apply Empty with x.
                            rewrite <- H3.
                            apply pair_in.
                        -- (* x, Bどちらも無限集合であることの証明 *)
                            intros.
                            apply Pairing in H3.
                            destruct H3.
                            ++ (* y = x の場合 *)
                                apply SchemaOfSpecification in H2.
                                rewrite H3.
                                apply H2.
                            ++ (* y = B の場合 *)
                                rewrite H3.
                                apply H0.
            - (* 自然数集合A∩Bが自然数集合Aを含むことの証明 *)
                apply nature_infTree_include.
                + (* 無限樹from Aが無限樹であることの証明 *)
                    apply nature_infinityToInfTree_infiniteTree.
                    apply H.
                + (* 無限樹from A /‾\ Bが無限樹であることの証明 *)
                    apply nature_infinityToInfTree_infiniteTree.
                    split.
                    * (* 空集合を含むことの証明 *)
                        apply nature_intersection.
                        split.
                        -- (* <: A, B :> が空集合でないことの証明 *)
                            exists A.
                            apply pair_in.
                        -- (* A, Bのどちらも空集合を含むことの証明 *)
                            intros.
                            apply Pairing in H1.
                            destruct H1.
                            ++ (* a = A の場合 *)
                                rewrite H1.
                                apply H.
                            ++ (* a = B の場合 *)
                                rewrite H1.
                                apply H0.
                    * (* A /‾\ B が後者を含むことの証明 *)
                        intros.
                        apply nature_intersection.
                        split.
                        -- (* <: A, B :> が空集合でないことの証明 *)
                            exists A.
                            apply pair_in.
                        -- (* A, Bのどちらも後者を含むことの証明 *)
                            intros.
                            apply Pairing in H2.
                            destruct H2.
                            ++ (* a = A の場合 *)
                                rewrite H2.
                                apply H.
                                apply nature_intersection in H1.
                                apply H1.
                                apply pair_in.
                            ++ (* a = B の場合 *)
                                rewrite H2.
                                apply H0.
                                apply nature_intersection in H1.
                                apply H1.
                                apply pair_in.
                +   (* 無限樹fromAが無限樹from A /‾\ Bを含むことの証明 *)
                    apply include_spec.
                    apply include_power.
                    intro.
                    intros.
                    apply nature_intersection in H1.
                    apply H1.
                    apply pair_in.
        }
        intros.
        transitivity (NaturalFromInfinity (A /‾\ B)).
        -   apply Hincl1.
            apply H.
            apply H0.
        -   symmetry.
            rewrite pair_symmetry.
            apply Hincl1.
            apply H0.
            apply H.
    Qed.

    (* 自然数集合 *)
    Definition NaturalSet : setType :=
        NaturalFromInfinity InfinitySet.

    (* 自然数型 *)
    Definition natural : Type := memberOf NaturalSet.

    (* 自然数の0 *)
    Definition zero : natural.
    Proof.
        specialize (nature_naturalFromInfinity_infinite InfinitySet).
        intro.
        specialize (H Infinity).
        unfold Infinite in H.
        destruct H.
        apply (memCons NaturalSet EmptySet H).
    Defined.

    (* 自然数の後者 *)
    Definition succ (n : natural) : natural.
    Proof.
        specialize (nature_naturalFromInfinity_infinite InfinitySet).
        intro.
        specialize (H Infinity).
        unfold Infinite in H.
        destruct H.
        specialize (nature_memberOf NaturalSet n).
        intro.
        apply H0 in H1.
        apply (memCons NaturalSet (n \_/ <: n :> ) H1).
    Defined.

    (* 公理の証明 *)

    (* 0が任意の自然数の後者でないことの証明 *)
    Theorem zero_not_succ : forall n : natural, zero <> succ n.
    Proof.
        intros.
        intro.
        apply Empty with n.
        unfold zero in H.
        destruct (nature_naturalFromInfinity_infinite).
        rewrite (inverse_memCons _ _ s).
        unfold NaturalSet in H.
        rewrite H.
        unfold succ.
        destruct (nature_naturalFromInfinity_infinite).
        rewrite <- inverse_memCons.
        apply UnionSet.
        exists <: n :>.
        split.
        apply pair_in.
        apply pair_in.
    Qed.

    (* 後者関数の単射性の証明 *)
    Theorem succ_inj : forall n m : natural, succ n = succ m -> n = m.
    Proof.
        specialize (nature_memberOf).
        intros.
        unfold succ in H0.
        destruct (nature_naturalFromInfinity_infinite).
        specialize (injective_memCons _ _ _ (s0 n (nature_memberOf _ n)) (s0 m (nature_memberOf _ m)) ).
        intro H1.
        specialize (H1 H0).
        assert (forall a, a In a \_/ <: a :> ).
        {
            intros.
            apply UnionSet.
            exists <: a :>.
            split.
            - apply pair_in.
            - apply pair_in.
        }
        assert (H3 : n In n \_/ <: n :> ) by apply H2.
        assert (H4 : m In m \_/ <: m :> ) by apply H2.
        rewrite H1 in H3.
        rewrite <- H1 in H4.
        apply UnionSet in H3.
        apply UnionSet in H4.
        destruct H3.
        destruct H4.
        destruct H3.
        destruct H4.
        apply Pairing in H3.
        apply Pairing in H4.
        destruct H3.
        destruct H4.
        - (* m In n /\ n In m -> False を証明する *)
            exfalso.
            specialize (Regularity <: n, m :> ).
            intro.
            destruct H7.
            apply not_empty.
            exists n.
            apply pair_in.
            destruct H7.
            subst x0.
            subst x.
            apply Pairing in H7.
            destruct H7.
            + (* x = n の場合 *)
                subst x1.
                apply Empty with m.
                rewrite <- H8.
                apply nature_intersection.
                split.
                exists <: n, m :>.
                apply pair_in.
                intros.
                apply Pairing in H3.
                destruct H3.
                rewrite H3.
                apply pair_in.
                rewrite H3.
                apply H6.
            + (* x = m の場合 *)
                subst x1.
                apply Empty with n.
                rewrite <- H8.
                apply nature_intersection.
                split.
                exists <: n, m :>.
                apply pair_in.
                intros.
                apply Pairing in H3.
                destruct H3.
                rewrite H3.
                apply pair_in.
                rewrite H3.
                apply H5.
        -
            subst x0.
            apply singleton_eq in H6.
            apply injective_memCast.
            apply H6.
        -
            subst x.
            apply singleton_eq in H5.
            apply injective_memCast.
            symmetry.
            apply H5.
    Qed.

    (* 数学的帰納法の公理の証明 *)
    Theorem nat_induction : forall (P : natural -> Prop),
        P zero ->
        (forall n : natural, P n -> P (succ n)) ->
        forall n : natural, P n.
    Proof.
        intros P H0 H1 n.
        specialize (nature_memberOf NaturalSet n).
        intro.
        replace NaturalSet with (<: x In NaturalSet | P x :>) in H.
        -   apply SchemaOfSpecification in H.
            destruct H.
            destruct H2.
            rewrite <- inverse_memCast in H2.
            apply H2.
        -   apply include_eq.
            split.
            +   (* 自然数のうちPを満たすものの集合は、自然数を包含することを示す *)
                intro.
                intro.
                assert (P_set_inf : Infinite (<: x In NaturalSet | P x :> )).
                {
                    unfold Infinite.
                    split.
                    +   (* 空集合を含むことの証明 *)
                        apply SchemaOfSpecification.
                        split.
                        *   (* EmptySet ∈ NaturalSet の証明 *)
                            specialize (nature_memberOf _ zero).
                            intro.
                            unfold zero in H3.
                            destruct (nature_naturalFromInfinity_infinite).
                            rewrite <- (inverse_memCons NaturalSet _ s) in H3.
                            apply H3.
                        *   (* EmptySet がPを満たすことの証明 *)
                            unfold zero in H0.
                            destruct (nature_naturalFromInfinity_infinite).
                            exists s.
                            apply H0.
                    +   (* <: x In NaturalSet | P x :> が後者をもつことの証明 *)
                        intros.
                        apply SchemaOfSpecification.
                        apply SchemaOfSpecification in H3.
                        destruct H3.
                        split.
                        apply nature_naturalFromInfinity_infinite.
                        *   apply Infinity.
                        *   apply H3.
                        *   (* succ y がPを満たすことの証明 *)
                            unfold succ in H1.
                            destruct H4.
                            replace y with (memCast NaturalSet (memCons NaturalSet y x)).
                            destruct (nature_naturalFromInfinity_infinite).
                            eexists.
                            apply H1.
                            apply H4.
                            symmetry.
                            apply inverse_memCons.
                    
                }
                assert (z In NaturalFromInfinity <: x In NaturalSet | P x :> ).
                {
                    rewrite <- (nature_natural_unique InfinitySet (<: x In NaturalSet | P x :> ) ).
                    -   apply H2.
                    -   apply Infinity.
                    -   (* <: x In NaturalSet | P x :> が無限集合であることの証明 *)
                        apply P_set_inf.
                }
                unfold NaturalFromInfinity in H3.
                apply nature_intersection in H3.
                apply H3.
                apply SchemaOfSpecification.
                split.
                *   apply PowerSet.
                    apply include_reflexivity.
                *   apply P_set_inf.
            +   (* 自然数のうちPを満たすものの集合は、自然数に包含されることを示す *)
                intro.
                intro.
                apply SchemaOfSpecification in H2.
                apply H2.
    Qed.
End ZF_natural.