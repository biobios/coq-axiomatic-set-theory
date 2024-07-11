Axiom Law_of_excluded_middle : forall P:Prop, P \/ (P->False).
Theorem contrapositive : forall P Q:Prop, (P -> Q) <-> ((Q->False) -> (P->False)).
Proof.
    intros.
    split.
    intros.
    apply H0.
    apply H.
    apply H1.
    intros.
    specialize (Law_of_excluded_middle Q).
    intros.
    destruct H1.
    apply H1.
    apply H in H1.
    destruct H1.
    apply H0.
Defined.