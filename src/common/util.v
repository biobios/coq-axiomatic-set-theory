Theorem P_or_P : forall P:Prop, P \/ P <-> P.
Proof.
    intros.
    split.
    intros.
    destruct H.
    apply H.
    apply H.
    intros.
    left.
    apply H.
Defined.

Theorem P_and_P : forall P:Prop, P /\ P <-> P.
Proof.
    split.
    intros.
    apply H.
    intros.
    split.
    apply H.
    apply H.
Defined.