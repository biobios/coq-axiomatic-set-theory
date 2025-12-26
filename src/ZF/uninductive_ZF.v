Require ZF.

Module uninductive_ZF <: ZF.CoreZF.
    Parameter setType : Type.
    Parameter set_in : setType -> setType -> Prop.
    Parameter Specification : setType -> (setType->Prop) -> setType.
    Parameter Pair : setType -> setType -> setType.
    Parameter Union : setType -> setType.
    Parameter Replacement : (setType -> setType) -> setType -> setType.
    Parameter Power : setType -> setType.
    Definition Intersection (A:setType) : setType := Specification (Union A) (fun z => forall a, set_in a A -> set_in z a).
    Record _memberOf (A:setType) : Type := {
        elem : setType;
        _ : set_in elem A
    }.

    Axiom set_in_eq : forall (a A:setType) (P1 P2:set_in a A), P1 = P2.

    Definition memberOf (A:setType) : Type := _memberOf A.

    Definition memCast : forall A:setType, memberOf A -> setType.
    Proof.
        intros.
        destruct X.
        exact elem0.
    Defined.
    
    Definition memCons : forall A a:setType, set_in a A -> memberOf A.
    Proof.
        intros.
        exact (Build__memberOf A a H).
    Defined.

    Coercion memCast : memberOf >-> setType.

    Definition set_include (a b:setType) := forall z, set_in z a -> set_in z b.
    
    Theorem nature_memberOf : forall (A:setType) (a:memberOf A), set_in a A.
    Proof.
        intros.
        destruct a.
        simpl.
        exact s.
    Qed.

    Theorem inverse_memCast : forall (A:setType) (a:memberOf A) Pa, a = memCons A (memCast A a) Pa.
    Proof.
        intros.
        destruct a.
        unfold memCons.
        simpl.
        f_equal.
        apply set_in_eq.
    Qed.

    Theorem inverse_memCons : forall (A a:setType) Pa, a = memCast A (memCons A a Pa).
    Proof.
        intros.
        unfold memCast.
        unfold memCons.
        reflexivity.
    Qed.

    Theorem injective_memCons : forall X a b Pa Pb, memCons X a Pa = memCons X b Pb -> a = b.
    Proof.
        intros.
        inversion H.
        reflexivity.
    Qed.

    Theorem injective_memCast : forall X a b, memCast X a = memCast X b -> a = b.
    Proof.
        intros.
        destruct a.
        destruct b.
        simpl in H.
        generalize s0.
        intros.
        revert s s1.
        induction H.
        intros.
        f_equal.
        apply set_in_eq.
    Qed.

    (* 外延性の公理 *)
    Axiom Extensionality : forall A B, (forall z, set_in z A <-> set_in z B) -> A = B.
    (* 分出公理 *)
    Axiom SchemaOfSpecification : forall (A x:setType) (P:(setType->Prop)),(set_in x (Specification A P))<->(set_in x A /\ P x).
    (* 対の公理 *)
    Axiom Pairing : forall x y t,((set_in t (Pair x y))<->(t = x \/ t = y)).
    (* 和集合の公理 *)
    Axiom UnionSet : forall X t,((set_in t (Union X))<->exists x,(set_in x X /\ set_in t x)).
    (* 冪集合公理 *)
    Axiom PowerSet : forall X t,set_in t (Power X) <-> set_include t X.
    Parameter InfinitySet : setType.
    Definition EmptySet : setType := Specification InfinitySet (fun x => False).
    (* 空集合の定理 *)
    Theorem Empty : forall a, (set_in a EmptySet -> False).
    Proof.
        intros.
        unfold EmptySet in H.
        apply SchemaOfSpecification in H.
        apply H.
    Qed.
    (* 無限公理 *)
    Axiom Infinity : set_in EmptySet InfinitySet /\ forall y, set_in y InfinitySet -> set_in (Union (Pair y (Pair y y))) InfinitySet.
    (* 正則性公理 *)
    Axiom Regularity : forall x, (x <> EmptySet) -> exists y, set_in y x /\ Intersection (Pair x y) = EmptySet.
    (* 置換公理 *)
    Axiom SchemaOfReplacement : forall (F:setType->setType) (A Fa:setType), set_in Fa (Replacement F A) <-> exists a, set_in a A /\ F a = Fa.
    (* 積集合の性質 *)
    Theorem nature_intersection : forall A z, set_in z (Intersection A) <-> (exists a,set_in a A) /\ forall a, set_in a A -> set_in z a.
    Proof.
        intros.
        split.
        -   intros.
            unfold Intersection in H.
            apply SchemaOfSpecification in H.
            split.
            +   destruct H as [H1 H2].
                apply UnionSet in H1.
                destruct H1.
                exists x.
                apply H.
            +   destruct H as [H1 H2].
                intros.
                apply H2.
                apply H.
        -   intros.
            unfold Intersection.
            apply SchemaOfSpecification.
            destruct H as [H1 H2].
            split.
            +   destruct H1 as [a H1].
                apply UnionSet.
                exists a.
                split.
                *   apply H1.
                *   apply H2.
                    apply H1.
            +   apply H2.
    Qed.
End uninductive_ZF.