Require Import AST.common.util.
Require AST.common.clasical.

Module Type CoreZF.
    Parameter setType : Type.
    Parameter set_in : setType -> setType -> Prop.
    Parameter Specification : setType -> (setType->Prop) -> setType.
    Parameter Pair : setType -> setType -> setType.
    Parameter Union : setType -> setType.
    Parameter Replacement : (setType -> setType) -> setType -> setType.
    Parameter Power : setType -> setType.
    Parameter Intersection : setType -> setType.
    Parameter memberOf : setType -> Type.
    Parameter memCast : forall A:setType, memberOf A -> setType.
    Parameter memCons : forall A a:setType, set_in a A -> memberOf A.
    Coercion memCast : memberOf >-> setType.

    Definition set_include (a b:setType) := forall z, set_in z a -> set_in z b.

    Axiom nature_memberOf : forall (A:setType) (a:memberOf A), set_in a A. 
    Axiom inverse_memCast : (forall (A:setType) (a:memberOf A) Pa, a = memCons A (memCast A a) Pa).
    Axiom inverse_memCons : forall (A a:setType) Pa, a = memCast A (memCons A a Pa).
    Axiom injective_memCons : forall X a b Pa Pb, memCons X a Pa = memCons X b Pb -> a = b.
    Axiom injective_memCast : forall X a b, memCast X a = memCast X b -> a = b.
    Axiom Extensionality : forall A B, (forall z, set_in z A <-> set_in z B) -> A = B.
    Axiom SchemaOfSpecification : forall (A x:setType) (P:(setType->Prop)),(set_in x (Specification A P))<->(set_in x A /\ P x).
    Axiom Pairing : forall x y t,((set_in t (Pair x y))<->(t = x \/ t = y)).
    Axiom UnionSet : forall X t,((set_in t (Union X))<->exists x,(set_in x X /\ set_in t x)).
    Axiom PowerSet : forall X t,set_in t (Power X) <-> set_include t X.
    Parameter InfinitySet : setType.
    Parameter EmptySet : setType.
    Axiom Empty : forall a, (set_in a EmptySet -> False).
    Axiom Infinity : set_in EmptySet InfinitySet /\ forall y, set_in y InfinitySet -> set_in (Union (Pair y (Pair y y))) InfinitySet.
    Axiom Regularity : forall x, (x <> EmptySet) -> exists y, set_in y x /\ Intersection (Pair x y) = EmptySet.
    Axiom SchemaOfReplacement : forall (F:setType->setType) (A Fa:setType), set_in Fa (Replacement F A) <-> exists a, set_in a A /\ F a = Fa.
    Axiom nature_intersection : forall A z, set_in z (Intersection A) <-> (exists a,set_in a A) /\ forall a, set_in a A -> set_in z a.
End CoreZF.

Module Util_Notations_ZF (core:CoreZF).
    Import core.
    Declare Scope bioSet_scope.
    Delimit Scope bioSet_scope with bioSet.
    Open Scope bioSet_scope.
    Bind Scope bioSet_scope with setType.

    Class SpecRouter (Z:Type) := {
        SpecificationRouter : setType -> (Z->Prop) -> setType
    }.

    #[export]Instance NormalSpec : SpecRouter setType := {
        SpecificationRouter := Specification
    }.

    #[export]Instance SpecForMemberOf : forall (X:setType), SpecRouter (memberOf X) := {
        SpecificationRouter A P := Specification A (fun y=>exists Pin:set_in y X, P (memCons X y Pin))
    }.

    Notation "x 'In' y" := (set_in x y) (at level 70) : bioSet_scope.
    Notation "x '|=' y" := (set_include x y) (at level 70) : bioSet_scope.
    Notation "x '=|' y" := (set_include y x) (at level 70) : bioSet_scope.
    Notation "'<:' x 'In' X '|' P ':>'" := (SpecificationRouter X (fun x=>P)) (at level 0, x at level 0, X at level 99, P at level 99) : bioSet_scope.
    Notation "'<:' x ',' y ':>'" := (Pair x y)(at level 0, x at level 0, y at level 0) : bioSet_scope.
    Notation "'<:' x ':>'" := (Pair x x) (at level 0, x at level 0) : bioSet_scope.
    Notation "'|_|' X" := (Union X) (at level 45) : bioSet_scope.
    Notation "x '\_/' y" := (|_| <: x , y :>) (at level 50) : bioSet_scope.
    Notation "'|‾|' X" := (Intersection X) (at level 45) : bioSet_scope.
    Notation "x '/‾\' y" := (|‾| <: x , y :>) (at level 50) : bioSet_scope.
    Notation "'Pow' X" := (Power X) (at level 30) : bioSet_scope.
    Notation "F '[' A ']'" := (Replacement F A) (at level 70) : bioSet_scope.
End Util_Notations_ZF.

Module ZF (core:CoreZF).
    Include core.
    Include AST.common.clasical.
    Include Util_Notations_ZF core.

    Definition Infinite (x:setType) := EmptySet In x/\ forall y, y In x -> y \_/ <: y :> In x.

    Theorem not_empty : forall A, A <> EmptySet <-> exists a, a In A.
    Proof.
        intros.
        split.
        intros.
        specialize (Law_of_excluded_middle (exists a, a In A)).
        intros.
        destruct H0.
        apply H0.
        assert (forall a, a In A -> False).
        intros.
        apply H0.
        exists a.
        apply H1.
        exfalso.
        apply H.
        apply Extensionality.
        split.
        intros.
        exfalso.
        apply H1 with z.
        apply H2.
        intros.
        exfalso.
        apply Empty with z.
        apply H2.
        intros.
        intro.
        destruct H.
        apply Empty with x.
        rewrite <- H0.
        apply H.
    Defined.
    
    Theorem not_empty_memberOf : forall A, A <> EmptySet <-> exists a:memberOf A, a In A.
    Proof.
        intros.
        split.
        intros.
        specialize (not_empty A).
        intro.
        apply not_empty in H.
        destruct H.
        apply memCons in H as a.
        exists a.
        apply nature_memberOf.
        intros.
        apply not_empty.
        destruct H.
        exists (memCast A x).
        apply H.
    Defined.

    Theorem empty_spec : forall (P:setType->Prop), <: x In EmptySet | P x :> = EmptySet.
    Proof.
        intros.
        apply Extensionality.
        split.
        intros.
        apply SchemaOfSpecification in H.
        apply H.
        intros.
        exfalso.
        apply (Empty z).
        apply H.
    Defined.

    Theorem empty_union : |_| EmptySet = EmptySet.
    Proof.
        apply Extensionality.
        split.
        intros.
        apply UnionSet in H.
        exfalso.
        destruct H.
        apply Empty with x.
        apply H.
        intros.
        exfalso.
        apply Empty with z.
        apply H.
    Defined.

    Theorem empty_intersection : |‾| EmptySet = EmptySet.
    Proof.
        apply Extensionality.
        split.
        intros.
        apply nature_intersection in H.
        destruct H.
        destruct H.
        exfalso.
        apply Empty with x.
        apply H.
        intros.
        exfalso.
        apply Empty with z.
        apply H.
    Defined.

    Theorem include_eq : forall a b, a =| b /\ a |= b -> a = b.
    Proof.
        intros.
        apply Extensionality.
        split.
        intros.
        apply H.
        apply H0.
        intros.
        apply H.
        apply H0.
    Defined.

    Theorem empty_power : Pow EmptySet = <: EmptySet :>.
    Proof.
        apply Extensionality.
        split.
        intros.
        apply PowerSet in H.
        apply Pairing.
        apply P_or_P.
        apply Extensionality.
        split.
        intros.
        apply H.
        apply H0.
        intros.
        exfalso.
        apply Empty with z0.
        apply H0.
        intros.
        apply Pairing in H.
        apply PowerSet.
        unfold set_include.
        intros.
        apply (P_or_P (z = EmptySet)) in H.
        rewrite <- H.
        apply H0.
    Defined.
    
    Theorem include_reflexivity : forall a, a |= a.
    Proof.
        intros.
        intro.
        intro.
        apply H.
    Defined.

    Theorem include_transitivity : forall a b c, a =| b /\ b =| c -> a =| c.
    Proof.
        intros.
        intro.
        intro.
        apply H.
        apply H.
        apply H0.
    Defined.

    Theorem include_spec : forall a b (P:setType -> Prop), a =| b -> <: x In a | P x :> =| <: x In b | P x :>.
    Proof.
        intros.
        intro.
        intro.
        apply SchemaOfSpecification.
        apply SchemaOfSpecification in H0.
        split.
        apply H.
        apply H0.
        apply H0.
    Defined.

    Theorem include_power : forall a b, a =| b -> Pow a =| Pow b.
    Proof.
        intros.
        intro.
        intro.
        apply PowerSet.
        apply PowerSet in H0.
        apply (include_transitivity a b z).
        split.
        apply H.
        apply H0.
    Defined.

    Theorem include_union : forall a c, a In c -> a |= |_| c.
    Proof.
        intros.
        intro.
        intro.
        apply UnionSet.
        exists a.
        split.
        apply H.
        apply H0.
    Defined.

    Theorem include_intersection : forall a b, b <> EmptySet /\ a =| b -> |‾| a |= |‾| b.
    Proof.
        intros.
        intro.
        intros.
        apply nature_intersection.
        split.
        destruct H.
        apply not_empty in H.
        apply H.
        apply nature_intersection in H0.
        intros.
        apply H0.
        apply H.
        apply H1.
    Defined.

    Theorem intersection_include : forall a b, a =| (a /‾\ b).
    Proof.
        intros.
        intro.
        intro.
        apply nature_intersection in H.
        apply H.
        apply Pairing.
        left.
        reflexivity.
    Defined.

    Definition OrderedPair (a b:setType) := <: <: a :> , <: a, b :> :>.
    Notation "'(' a ',' b ')'" := (OrderedPair a b).
    Definition π1 (p:setType) := |_| (|‾| p).
    Definition π2 (p:setType) := |_| <: y In (|_| p) | (|‾| p = |_| p) \/ (y = π1 p -> False) :>.

    Theorem pair_symmetry : forall a b, <: a, b :> = <: b, a :>.
    Proof.
        intros.
        apply Extensionality.
        split.
        intros.
        apply Pairing.
        apply Pairing in H.
        destruct H.
        right.
        apply H.
        left.
        apply H.
        intros.
        apply Pairing.
        apply Pairing in H.
        destruct H.
        right.
        apply H.
        left.
        apply H.
    Defined.

    Theorem pair_in : forall a b, a In <: a, b :> /\ b In <: a, b :>.
    Proof.
        split.
        apply Pairing.
        left.
        reflexivity.
        apply Pairing.
        right.
        reflexivity.
    Defined.

    Theorem pair_eq : forall a b c, <: a, b :> = <: a, c :> -> b = c.
    Proof.
        intros.
        specialize (pair_in a b).
        specialize (pair_in a c).
        intros.
        destruct H0.
        destruct H1.
        rewrite <- H in H2.
        rewrite H in H3.
        apply Pairing in H2.
        apply Pairing in H3.
        destruct H2.
        destruct H3.
        transitivity a.
        apply H3.
        symmetry.
        apply H2.
        apply H3.
        symmetry.
        apply H2.
    Defined.

    Theorem singleton_eq : forall a b, b In <: a :> <-> a = b.
    Proof.
        split.
        intros.
        apply Pairing in H.
        apply P_or_P with (b=a) in H.
        symmetry.
        apply H.
        intros.
        apply Pairing.
        left.
        symmetry.
        apply H.
    Defined.

    Theorem singleton_intersection : forall a, a = |‾| <: a :>.
    Proof.
        intros.
        apply Extensionality.
        split.
        intros.
        apply nature_intersection.
        split.
        exists a.
        apply pair_in.
        intros.
        apply singleton_eq in H0.
        rewrite <- H0.
        apply H.
        intros.
        apply nature_intersection in H.
        apply H.
        apply pair_in.
    Defined.

    Theorem singleton_union : forall a, a = |_| <: a :>.
    Proof.
        intros.
        apply Extensionality.
        split.
        intros.
        apply UnionSet.
        exists a.
        split.
        apply pair_in.
        apply H.
        intros.
        apply UnionSet in H.
        destruct H.
        destruct H.
        apply singleton_eq in H.
        rewrite H.
        apply H0.
    Defined.

    Theorem spec_singleton : forall A (P:setType->Prop), (exists! a:setType, a In A /\ P a) -> exists a:memberOf A, <: a :> = <: x In A | P x :>.
    Proof.
        intros.
        destruct H.
        destruct H.
        destruct H.
        exists (memCons A x H).
        apply Extensionality.
        split.
        intros.
        apply SchemaOfSpecification.
        apply singleton_eq in H2.
        rewrite <- (inverse_memCons A x H) in H2.
        rewrite <- H2.
        split.
        apply H.
        apply H1.
        intros.
        apply SchemaOfSpecification in H2.
        apply H0 in H2.
        rewrite <- H2.
        apply singleton_eq.
        symmetry.
        apply inverse_memCons.
    Defined.

    Theorem o_pair_eq : forall a b c d, (a, b) = (c, d) <-> a = c /\ b = d.
    Proof.
        intros.
        split.
        intros.
        specialize (pair_in <: c :> <: c , d :>).
        intros.
        destruct H0.
        unfold OrderedPair in H.
        rewrite <- H in H0.
        apply Pairing in H0.
        rewrite <- H in H1.
        apply Pairing in H1.
        destruct H0.
        specialize (pair_in a a).
        intro.
        destruct H2.
        rewrite <- H0 in H2.
        apply singleton_eq in H2.
        split.
        symmetry.
        apply H2.
        rewrite H2 in H.
        apply pair_eq in H.
        apply pair_eq in H.
        apply H.
        specialize (pair_in a b).
        intro.
        destruct H2.
        rewrite <- H0 in H2.
        apply singleton_eq in H2.
        split.
        symmetry.
        apply H2.
        rewrite H2 in H.
        apply pair_eq in H.
        apply pair_eq in H.
        apply H.
        intros.
        f_equal.
        apply H.
        apply H.
    Defined.
        

    Theorem nature_π1 : forall a b:setType, a = π1 ( a , b ).
    Proof.    
        intros.
        apply Extensionality.
        split.
        intros.
        unfold π1.
        apply UnionSet.
        exists a.
        split.
        apply nature_intersection.
        split.
        exists <: a :>.
        apply pair_in.
        intros.
        apply Pairing in H0.
        destruct H0.
        rewrite H0.
        apply pair_in.
        rewrite H0.
        apply pair_in.
        apply H.
        intros.
        apply UnionSet in H.
        destruct H.
        destruct H.
        apply nature_intersection in H.
        destruct H.
        assert (a = x).
        apply singleton_eq.
        apply H1.
        apply pair_in.
        rewrite H2.
        apply H0.
    Defined.

    Theorem nature_π2 : forall a b:setType, b = π2 (a , b).
    Proof.
        assert (forall a b, |‾| ((a, b)) = |_| (a, b) -> a = b).
        intros.
        apply (pair_eq a a b).
        transitivity (|‾| (a,b)).
        apply Extensionality.
        split.
        intros.
        apply nature_intersection.
        split.
        exists <: a :>.
        apply pair_in.
        intros.
        apply singleton_eq in H0.
        rewrite <- H0.
        apply Pairing in H1.
        destruct H1.
        rewrite H1.
        apply pair_in.
        rewrite H1.
        apply pair_in.
        intros.
        apply nature_intersection in H0.
        destruct H0.
        apply H1.
        apply pair_in.
        transitivity (|_| (a,b)).
        apply H.
        apply Extensionality.
        split.
        intros.
        apply UnionSet in H0.
        destruct H0.
        destruct H0.
        apply Pairing in H0.
        destruct H0.
        rewrite H0 in H1.
        apply singleton_eq in H1.
        rewrite H1.
        apply pair_in.
        rewrite H0 in H1.
        apply H1.
        intros.
        apply UnionSet.
        exists <:a, b:>.
        split.
        apply pair_in.
        apply H0.
        intros.
        apply Extensionality.
        split.
        intros.
        unfold π2.
        apply UnionSet.
        exists b.
        split.
        apply SchemaOfSpecification.
        split.
        apply UnionSet.
        exists <: a, b :>.
        split.
        apply pair_in.
        apply pair_in.
        specialize (Law_of_excluded_middle (b = π1 (a, b))).
        intros.
        destruct H1.
        left.
        specialize (nature_π1 a b).
        intros.
        apply Extensionality.
        split.
        intros.
        apply UnionSet.
        exists <: a :>.
        split.
        apply pair_in.
        apply nature_intersection in H3.
        destruct H3.
        apply H4.
        apply pair_in.
        intros.
        apply nature_intersection.
        split.
        exists <: a :>.
        apply pair_in.
        intros.
        apply UnionSet in H3.
        destruct H3.
        destruct H3.
        apply Pairing in H3.
        destruct H3.
        rewrite H3 in H5.
        apply singleton_eq in H5.
        apply Pairing in H4.
        destruct H4.
        rewrite <- H5.
        rewrite H4.
        apply pair_in.
        rewrite <- H5.
        rewrite H4.
        apply pair_in.
        rewrite H3 in H5.
        apply Pairing in H5.
        apply Pairing in H4.
        destruct H5.
        destruct H4.
        rewrite H5.
        rewrite H4.
        apply pair_in.
        rewrite H5.
        rewrite H4.
        apply pair_in.
        assert (a=b).
        transitivity (π1 (a, b)).
        apply H2.
        symmetry.
        apply H1.
        rewrite H6 in H4.
        apply P_or_P with (a0 = <:b:>)in H4.
        rewrite H5.
        rewrite H4.
        apply pair_in.
        right.
        apply H1.
        apply H0.
        intros.
        unfold π2 in H0.
        apply UnionSet in H0.
        destruct H0 as [maybe_b].
        destruct H0.
        apply SchemaOfSpecification in H0.
        destruct H0.
        apply UnionSet in H0.
        destruct H0 as [maybe_a_b].
        destruct H0.
        apply Pairing in H0.
        assert (maybe_b = a -> z In b).
        intros.
        destruct H2.
        apply H in H2.
        rewrite <- H2.
        rewrite <- H4.
        apply H1.
        exfalso.
        apply H2.
        transitivity a.
        apply H4.
        apply nature_π1.
        destruct H0.
        rewrite H0 in H3.
        apply singleton_eq in H3.
        symmetry in H3.
        apply H4 in H3.
        apply H3.
        rewrite H0 in H3.
        apply Pairing in H3.
        destruct H3.
        apply H4.
        apply H3.
        rewrite <- H3.
        apply H1.
    Defined.

    Definition DirectProduct (a b:setType) : setType := <: o In (Pow Pow (a \_/ b)) | (exists c d, o = (c, d) /\ c In a /\ d In b) :>.
    Notation "x * y" := (DirectProduct x y) (at level 40, left associativity):bioSet_scope.
    Theorem directProduct_in : forall (A B:setType) (a:memberOf A) (b:memberOf B), (a,b) In (A * B).
    Proof.
        intros.
        apply SchemaOfSpecification.
        split.
        apply PowerSet.
        intro.
        intros.
        apply PowerSet.
        intro.
        intros.
        apply UnionSet.
        apply Pairing in H.
        assert (z0 = a -> exists x:setType, x In <: A , B :> /\ z0 In x).
        intro.
        rewrite H1.
        exists A.
        split.
        apply pair_in.
        apply nature_memberOf.
        destruct H.
        rewrite H in H0.
        apply singleton_eq in H0.
        apply H1.
        symmetry.
        apply H0.
        rewrite H in H0.
        apply Pairing in H0.
        destruct H0.
        apply H1.
        apply H0.
        rewrite H0.
        exists B.
        split.
        apply pair_in.
        apply nature_memberOf.
        exists a.
        exists b.
        split.
        apply f_equal.
        reflexivity.
        split.
        apply nature_memberOf.
        apply nature_memberOf.
    Defined.

    Theorem nature_π : forall (A B:setType) (p:memberOf (A * B)), memCast (A * B) p = (π1 p, π2 p).
    Proof.
        intros.
        specialize (nature_memberOf (A * B) p).
        intro.
        apply SchemaOfSpecification in H.
        destruct H.
        destruct H0 as [a].
        destruct H0 as [b].
        destruct H0.
        rewrite H0.
        apply o_pair_eq.
        split.
        apply nature_π1.
        apply nature_π2.
    Defined.
        
    Definition dom (f:setType) := <: a In (|_| (|_| f)) | (exists p:memberOf f, a = π1 p) :>.
    Definition ran (f:setType) := <: o In (|_| (|_| f)) | (exists p:memberOf f, o = π2 p) :>.

    Definition setOfMapping (X Y :setType) := <: f In Pow (X * Y) | (forall (x:memberOf X), (exists y:memberOf Y, (x,y) In f /\ (forall y':memberOf Y, (x,y') In f -> y = y'))) :>.
    Notation "y ^ x" := (setOfMapping x y) : bioSet_scope.
    Notation "x → y" := (memberOf (y ^ x)) (at level 80):bioSet_scope.
    Lemma nature_substitution : forall (X Y:setType) (f:X → Y) (x : memberOf X), (π2 (|_| <: m In f | (memCast X x = π1 m) :>)) In Y.
    Proof.
        intros.
        specialize (nature_memberOf (Y ^ X) f).
        intro.
        apply SchemaOfSpecification in H.
        destruct H.
        specialize (H0 x).
        destruct H0 as [y].
        assert (memCast Y y = π2 (|_| <: m In f | (memCast X x = π1 m) :>)).
        transitivity (π2 (x, y)).
        apply nature_π2.
        f_equal.
        transitivity (|_| <: (x,y) :>).
        apply Extensionality.
        split.
        intros.
        apply UnionSet.
        exists (x,y).
        split.
        apply pair_in.
        apply H1.
        intros.
        apply UnionSet in H1.
        destruct H1.
        destruct H1.
        apply singleton_eq in H1.
        rewrite H1.
        apply H2.
        f_equal.
        apply Extensionality.
        intro z.
        split.
        intros bioH0.
        apply singleton_eq in bioH0.
        rewrite <- bioH0.
        apply SchemaOfSpecification.
        split.
        apply H0.
        apply nature_π1.
        intros bioH0.
        apply singleton_eq.
        transitivity (π1 z, π2 z).
        apply SchemaOfSpecification in bioH0.
        destruct bioH0 as [bioH1 bioH2].
        f_equal.
        apply bioH2.
        generalize bioH1.
        intro bioH99.
        apply (PowerSet (X * Y) (memCast (Y ^ X) f)) in H.
        apply H in bioH1.
        apply SchemaOfSpecification in bioH1.
        destruct bioH1 as [bioH0 bioH1].
        destruct bioH1 as [x' bioH1].
        destruct bioH1 as [y' bioH1].
        transitivity (π2 (x', y')).
        transitivity (y').
        destruct bioH1 as [bioH3 bioH1].
        destruct bioH1 as [bioH4 bioH1].
        transitivity (memCast Y (memCons Y y' bioH1)).
        f_equal.
        apply H0.
        assert ((x,memCons Y y' bioH1) = z).
        transitivity (x', y').
        f_equal.
        transitivity (π1 z).
        apply bioH2.
        transitivity (π1 (x', y')).
        f_equal.
        apply bioH3.
        symmetry.
        apply nature_π1.
        symmetry.
        apply (inverse_memCons).
        symmetry.
        apply bioH3.
        rewrite H1.
        apply bioH99.
        symmetry.
        apply inverse_memCons.
        apply nature_π2.
        f_equal.
        symmetry.
        apply bioH1.
        apply SchemaOfSpecification in bioH0.
        destruct bioH0 as [bioH0 bioH1].
        apply PowerSet in H.
        apply H in bioH0.
        apply SchemaOfSpecification in bioH0.
        destruct bioH0 as [bioH0 bioH2].
        destruct bioH2 as [x' bioH2].
        destruct bioH2 as [y' bioH2].
        transitivity (x', y').
        f_equal.
        transitivity (π1 (x', y')).
        f_equal.
        apply bioH2.
        symmetry.
        apply nature_π1.
        transitivity (π2 (x',y')).
        f_equal.
        apply bioH2.
        symmetry.
        apply nature_π2.
        symmetry.
        apply bioH2.
        rewrite <- H1.
        apply nature_memberOf.
    Defined.
    Definition substitution {X Y:setType} (f : X → Y) (x : memberOf X) : memberOf Y := memCons Y (π2 (|_| <: m In f | (memCast X x = π1 m) :>)) (nature_substitution X Y f x).

    Notation "f ← x" := (substitution f x) (at level 50):bioSet_scope.
    
    Lemma func_memberOf : forall (A B:setType) (f: A → B) (a: memberOf A) (b: memberOf B), (a, b) In f <-> (b = f ← a).
    Proof.
        intros.
        split.
        intros.
        unfold substitution.
        apply injective_memCast.
        rewrite <- (inverse_memCons B (π2 (|_| <: m In f | (memCast A a = π1 m) :>)) (nature_substitution A B f a)).
        transitivity (π2 (a, b)).
        apply nature_π2.
        f_equal.
        transitivity (|_| <: (a, b) :>).
        apply singleton_union.
        f_equal.
        apply Extensionality.
        split.
        intros.
        apply SchemaOfSpecification.
        apply singleton_eq in H0.
        split.
        rewrite <- H0.
        apply H.
        rewrite <- H0.
        apply nature_π1.
        intros.
        apply SchemaOfSpecification in H0.
        apply singleton_eq.
        specialize (nature_memberOf (B ^ A) f).
        intro.
        apply SchemaOfSpecification in H1.
        destruct H1.
        specialize (H2 a).
        destruct H2 as [b'].
        transitivity (π1 z, π2 z).
        apply o_pair_eq.
        split.
        apply H0.
        transitivity (b').
        symmetry.
        destruct H2.
        f_equal.
        apply H3.
        apply H.
        apply PowerSet in H1.
        destruct H0.
        specialize (H1 z H0).
        apply SchemaOfSpecification in H1.
        destruct H1.
        destruct H4 as [a'].
        destruct H4 as [b''].
        specialize (nature_memberOf (B ^ A) f).
        intro.
        apply SchemaOfSpecification in H5.
        destruct H5.
        destruct H4.
        destruct H7.
        specialize (H6 (memCons A a' H7)).
        rewrite <- (inverse_memCons A a' H7) in H6.
        transitivity (b'').
        destruct H2.
        apply (injective_memCons B b' b'' (nature_memberOf B b') H8).
        rewrite <- (inverse_memCast B b' (nature_memberOf B b')).
        apply H9.
        assert (memCast A a = a').
        transitivity (π1 z).
        apply H3.
        symmetry.
        rewrite H4.
        apply nature_π1.
        rewrite H10.
        rewrite <- (inverse_memCons B b'' H8).
        rewrite <- H4.
        apply H0.
        rewrite H4.
        apply nature_π2.
        symmetry.
        apply PowerSet in H1.
        destruct H0.
        specialize (H1 z H0).
        rewrite (inverse_memCons (A * B) z H1).
        apply nature_π.
        intros.
        specialize (nature_memberOf (B ^ A) f).
        intro.
        apply SchemaOfSpecification in H0.
        destruct H0.
        specialize (H1 a).
        destruct H1 as [b'].
        destruct H1.
        assert (b' = f ← a).
        unfold substitution.
        apply injective_memCast.
        rewrite <- (inverse_memCons B (π2 (|_| <: m In f | (memCast A a = π1 m) :>)) (nature_substitution A B f a)).
        transitivity (π2 (a, b')).
        apply nature_π2.
        f_equal.
        transitivity (|_| <: (a, b') :>).
        apply singleton_union.
        f_equal.
        apply Extensionality.
        split.
        intros.
        apply SchemaOfSpecification.
        apply singleton_eq in H3.
        split.
        rewrite <- H3.
        apply H1.
        rewrite <- H3.
        apply nature_π1.
        intros.
        apply SchemaOfSpecification in H3.
        apply singleton_eq.
        transitivity (π1 z, π2 z).
        apply o_pair_eq.
        split.
        apply H3.
        apply PowerSet in H0.
        destruct H3.
        specialize (H0 z H3).
        apply SchemaOfSpecification in H0.
        destruct H0.
        destruct H5 as [a'].
        destruct H5 as [b''].
        destruct H5.
        destruct H6.
        rewrite H5.
        rewrite <- (nature_π2 a' b'').
        apply (injective_memCons B b' b'' (nature_memberOf B b') H7).
        rewrite <- (inverse_memCast B b' (nature_memberOf B b')).
        apply H2.
        rewrite <- (inverse_memCons B b'' H7).
        assert (memCast A a = a').
        transitivity (π1 z).
        apply H4.
        symmetry.
        rewrite H5.
        apply nature_π1.
        rewrite H8.
        rewrite <- H5.
        apply H3.
        symmetry.
        apply PowerSet in H0.
        destruct H3.
        specialize (H0 z H3).
        rewrite (inverse_memCons (A * B) z H0).
        apply nature_π.
        rewrite H.
        rewrite <- H3.
        apply H1.
    Defined.

    Lemma ex_func : forall (A B:setType), A <> EmptySet -> B <> EmptySet -> (B ^ A) <> EmptySet.
    Proof.
        intros.
        intro.
        apply not_empty in H.
        apply not_empty in H0.
        destruct H as [a].
        destruct H0 as [b].
        apply (Empty (<: p In (A * B) | (exists a', (a',b) = p) :>)).
        rewrite <- H1.
        apply SchemaOfSpecification.
        split.
        apply PowerSet.
        intro.
        intro.
        apply SchemaOfSpecification in H2.
        apply H2.
        intros.
        exists (memCons B b H0).
        split.
        apply SchemaOfSpecification.
        split.
        apply SchemaOfSpecification.
        split.
        apply PowerSet.
        intro.
        intro.
        apply PowerSet.
        intro.
        intro.
        apply Pairing in H2.
        apply UnionSet.
        destruct H2.
        rewrite H2 in H3.
        apply singleton_eq in H3.
        rewrite <- H3.
        exists A.
        split.
        apply pair_in.
        apply nature_memberOf.
        rewrite H2 in H3.
        apply Pairing in H3.
        destruct H3.
        rewrite H3.
        exists A.
        split.
        apply pair_in.
        apply nature_memberOf.
        exists B.
        split.
        apply pair_in.
        rewrite H3.
        rewrite <- (inverse_memCons B b H0).
        apply H0.
        exists x.
        exists b.
        split.
        f_equal.
        symmetry.
        apply inverse_memCons.
        split.
        apply nature_memberOf.
        apply H0.
        exists x.
        f_equal.
        apply inverse_memCons.
        intros.
        apply SchemaOfSpecification in H2.
        destruct H2.
        destruct H3.
        apply o_pair_eq in H3.
        rewrite (inverse_memCast B y' (nature_memberOf B y')).
        apply (injective_memCast).
        rewrite <- (inverse_memCons B b H0).
        rewrite <- (inverse_memCons B y' (nature_memberOf B y')).
        apply H3.
    Defined.

    Definition DefFunc {A B:setType} (Pa:A <> EmptySet) (Pb:B <> EmptySet) (P:A → B -> Prop) (Pe:exists f, P f /\ forall f', P f' -> f = f') : A → B.
    Proof.
        assert (|_| <: f In (B ^ A) | (exists Pf, P (memCons (B ^ A) f Pf)) :> In (B ^ A)).
        destruct Pe.
        assert (memCast (B ^ A) x = |_| <: f In (B ^ A) | (exists Pf, P (memCons (B ^ A) f Pf)) :> ).
        rewrite (singleton_union x).
        f_equal.
        apply Extensionality.
        split.
        intros.
        apply SchemaOfSpecification.
        apply singleton_eq in H0.
        rewrite <- H0.
        split.
        apply nature_memberOf.
        exists (nature_memberOf (B ^ A) x).
        rewrite <- (inverse_memCast (B^A) x (nature_memberOf (B ^ A) x)).
        apply H.
        intros.
        apply SchemaOfSpecification in H0.
        destruct H0.
        destruct H1.
        apply singleton_eq.
        apply H in H1.
        transitivity (memCons (B^A) z x0).
        f_equal.
        apply H1.
        symmetry.
        apply inverse_memCons.
        rewrite <- H0.
        apply nature_memberOf.
        apply (memCons (B ^ A) (|_| <: f In (B ^ A) | (exists Pf, P (memCons (B ^ A) f Pf)) :>) H).
    Defined.

    Theorem RelPowSpec : forall (A: setType) (R: setType -> Prop), <: x In A | R x :> In Pow A.
    Proof.
        intros.
        apply PowerSet.
        intro.
        intro.
        apply SchemaOfSpecification in H.
        apply H.
    Defined.

    Goal forall (A B:setType) (P:memberOf A->memberOf B->Prop), (forall a, exists! b, P a b) -> (exists! f:A → B, (forall a, P a (f←a))).
        intros.
        assert (<: z In (A * B) | (exists (a:memberOf A) (b:memberOf B), (a,b) = z /\ P a b) :> In (B ^ A)).
        apply SchemaOfSpecification.
        split.
        apply (RelPowSpec (A * B) (fun z => exists (a:memberOf A) (b:memberOf B), (a,b) = z /\ P a b)).
        intro.
        specialize (H x).
        destruct H.
        exists x0.
        split.
        apply SchemaOfSpecification.
        split.
        apply directProduct_in.
        exists x.
        exists x0.
        split.
        f_equal.
        destruct H.
        apply H.
        intros.
        apply SchemaOfSpecification in H0.
        destruct H0.
        destruct H1.
        destruct H1.
        destruct H1.
        apply o_pair_eq in H1.
        destruct H1.
        destruct H.
        apply H4.
        apply injective_memCast in H1.
        apply injective_memCast in H3.
        rewrite <- H1.
        rewrite <- H3.
        apply H2.
        exists (memCons (B ^ A) <: z In (A * B) | (exists (a:memberOf A) (b:memberOf B), (a,b) = z /\ P a b) :> H0).
        split.
        intros.
        unfold substitution.
        specialize (H a).
        destruct H as [b].
        destruct H.
        assert (b = (memCons B (π2 (|_| <: m In memCons (B ^ A) <: z In A * B | (exists (a0:memberOf A) (b0 : memberOf B), (a0, b0) = z /\ P a0 b0) :> H0 | (memCast A a = π1 m) :>)) (nature_substitution A B (memCons (B ^ A) <: z In A * B | (exists (a0:memberOf A) (b0 : memberOf B), (a0, b0) = z /\ P a0 b0) :> H0) a))).
        apply injective_memCast.
        rewrite <- (inverse_memCons B (π2 (|_| <: m In memCons (B ^ A) <: z In A * B | (exists (a0:memberOf A) (b0 : memberOf B), (a0, b0) = z /\ P a0 b0) :> H0 | (memCast A a = π1 m) :>)) (nature_substitution A B (memCons (B ^ A) <: z In A * B | (exists (a0:memberOf A) (b0 : memberOf B), (a0, b0) = z /\ P a0 b0) :> H0) a)).
        transitivity (π2 (a,b)).
        apply nature_π2.
        f_equal.
        apply Extensionality.
        split.
        intro.
        apply UnionSet.
        exists (a, b).
        split.
        apply SchemaOfSpecification.
        split.
        rewrite <- (inverse_memCons (B ^ A) <: z0 In A * B | (exists (a0 : memberOf A) (b0 : memberOf B), (a0, b0) = z0 /\ P a0 b0) :> H0).
        apply SchemaOfSpecification.
        split.
        apply directProduct_in.
        exists a.
        exists b.
        split.
        reflexivity.
        apply H.
        apply nature_π1.
        apply H2.
        intros.
        apply UnionSet in H2.
        destruct H2 as [op].
        destruct H2.
        apply SchemaOfSpecification in H2.
        destruct H2.
        rewrite <- (inverse_memCons (B ^ A) <: z In A * B | (exists (a0 : memberOf A) (b0 : memberOf B), (a0, b0) = z /\ P a0 b0) :> H0) in H2.
        apply SchemaOfSpecification in H2.
        destruct H2.
        destruct H5 as [a'].
        destruct H5 as [b'].
        assert ((a,b) = op).
        transitivity (a', b').
        f_equal.
        transitivity (π1 op).
        apply H4.
        destruct H5.
        symmetry.
        rewrite <- H5.
        apply nature_π1.
        f_equal.
        apply H1.
        assert (a = a').
        apply injective_memCast.
        transitivity (π1 (a',b')).
        destruct H5.
        rewrite H5.
        apply H4.
        symmetry.
        apply nature_π1.
        rewrite H6.
        apply H5.
        apply H5.
        rewrite H6.
        apply H3.
        rewrite <- H2.
        apply H.
        intros.
        apply injective_memCast.
        rewrite <- (inverse_memCons).
        apply Extensionality.
        split.
        intros.
        specialize (nature_memberOf (B ^ A) x').
        intro.
        apply SchemaOfSpecification in H3.
        destruct H3.
        apply SchemaOfSpecification in H2.
        destruct H2.
        destruct H5 as [a'].
        destruct H5 as [b'].
        destruct H5.
        rewrite <- H5.
        specialize (H4 a').
        destruct H4 as [b''].
        destruct H4.
        apply func_memberOf.
        specialize (H a').
        specialize (H1 a').
        assert (b'' = x' ← a').
        apply func_memberOf.
        apply H4.
        destruct H as [b'''].
        destruct H.
        apply H9 in H1.
        apply H9 in H6.
        rewrite <- H1.
        symmetry.
        apply H6.
        intros.
        apply SchemaOfSpecification.
        split.
        specialize (nature_memberOf (B ^ A) x').
        intro.
        apply SchemaOfSpecification in H3.
        destruct H3.
        apply PowerSet in H3.
        apply H3.
        apply H2.
        specialize (Law_of_excluded_middle (A = EmptySet)).
        intros.
        destruct H3.
        exfalso.
        specialize (nature_memberOf (B ^ A) x').
        intro.
        apply SchemaOfSpecification in H4.
        destruct H4.
        apply PowerSet in H4.
        specialize (H4 z H2).
        apply SchemaOfSpecification in H4.
        destruct H4.
        apply PowerSet in H4.
        destruct H6.
        destruct H6.
        destruct H6.
        specialize (H4 <: x :>).
        rewrite H6 in H4.
        specialize (Pairing x x0).
        intro.
        apply (Empty x).
        rewrite <- H3.
        apply H7.
        apply not_empty_memberOf in H3.
        destruct H3 as [a].
        specialize (nature_memberOf (B ^ A) x').
        intro.
        apply SchemaOfSpecification in H4.
        destruct H4.
        apply PowerSet in H4.
        specialize (H4 z H2).
        apply SchemaOfSpecification in H4.
        destruct H4.
        destruct H6 as [a'].
        destruct H6 as [b'].
        destruct H6.
        destruct H7.
        exists (memCons A a' H7).
        exists (memCons B b' H8).
        split.
        rewrite <- (inverse_memCons A a' H7).
        rewrite <- (inverse_memCons B b' H8).
        symmetry.
        apply H6.
        assert (memCons B b' H8 = x' ← memCons A a' H7).
        apply func_memberOf.
        rewrite <- (inverse_memCons A a' H7).
        rewrite <- (inverse_memCons B b' H8).
        rewrite <- H6.
        apply H2.
        rewrite H9.
        apply H1.
    Defined.
End ZF.