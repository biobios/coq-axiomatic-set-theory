Module Type CoreNatural.
    Parameter natural : Type.
    Parameter zero : natural.
    Parameter succ : natural -> natural.
    Axiom zero_not_succ : forall n : natural, zero <> succ n.
    Axiom succ_inj : forall n m : natural, succ n = succ m -> n = m.
    (* 数学的帰納法の公理 *)
    Axiom nat_induction : forall (P : natural -> Prop),
        P zero ->
        (forall n : natural, P n -> P (succ n)) ->
        forall n : natural, P n.
End CoreNatural.