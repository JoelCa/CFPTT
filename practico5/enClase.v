Section EnClase.

Inductive Arbol_bin(A:Set):Set :=
    arbol_nil
  | node: Arbol_bin A -> A -> Arbol_bin A -> Arbol_bin A.


Inductive isomorfismo(A:Set):Arbol_bin A -> Arbol_bin A -> Prop :=
    isomorfismo0 : isomorfismo A (arbol_nil A) (arbol_nil A)
  | isomorfismoS : forall (t1 t2 t1' t2':Arbol_bin A) (a b : A), isomorfismo A t1 t1' -> isomorfismo A t2 t2' -> isomorfismo A (node A t1 a t2) (node A t1' b t2').


Lemma unlema:forall (A:Set) (t1 t2 t3:Arbol_bin A), isomorfismo A t1 t2 -> isomorfismo A t2 t3 -> isomorfismo A t1 t3.
Proof.
  induction t1; intros.
    inversion_clear H in H0.
    assumption.

    inversion_clear H in H0.
    inversion_clear  H0.
    constructor.
      exact((IHt1_1 t1' t1'0) H1 H). (* el "->" NO tiene un constructor? *)

      exact((IHt1_2 t2' t2'0) H2 H3).
Qed.

(*forall (x: nat)(H : Even x), e0 <> ess x H.*)

Inductive Even : nat -> Prop :=
  | e0 : Even 0
  | eSS : forall n:nat, Even n -> Even (S (S n)).

Check Even 1 = Even 0.

Theorem t: forall x:nat, Even (x) <-> x=0 \/ exists y:nat, (x = (S (S y)) /\ Even (y)).
Proof.
  unfold iff; intros; split.
    intro.
    induction H.
      left; reflexivity.
      elim IHEven; intro; clear IHEven.
        right.
        rewrite H0.
        exists 0.
        split; [reflexivity | constructor].

        elim H0; intros.
        elim H1; intros; clear H1.
        right.
        exists (S (S x)).
        rewrite H2.
        split; [reflexivity | constructor; assumption].

    intro.
    elim H; intro; clear H.
    rewrite H0; constructor.
    elim H0; intros; clear H0.
    elim H; intros; clear H.
    rewrite H0; constructor; assumption.
Qed.

End EnClase.

Print and.

Theorem tt : forall (A B:Prop), and A B -> A.
Proof.
  intros.
  induction H.
  assumption.
Qed.