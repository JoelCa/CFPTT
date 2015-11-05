(* Práctico 6 *)

(* Section Ejercicio1.*)

(* 1.1 *)
Lemma predspec : forall n : nat, {m : nat | n = 0 /\ m = 0 \/ n = S m}.
Proof.
  intros.
  case n.
    exists 0.
    left.
    split; reflexivity.

    intros.
    exists n0.
    right.
    reflexivity.
Qed.

(* 1.2 *)
Extraction Language Haskell.
Extraction "predecesor" predspec.

(* Ejercicio 2 *)
Section Ejercicio2.


Inductive bintree(A:Set):Set :=
    btree_nil
  | node: bintree A -> A -> bintree A -> bintree A.

Inductive mirror(A:Set):bintree A -> bintree A -> Prop :=
    mirror0 : mirror A (btree_nil A) (btree_nil A) 
  | mirrorS : forall (t1 t2 t1' t2':bintree A) (a b : A), a = b -> mirror A t1 t2' -> mirror A t2 t1' -> mirror A (node A t1 a t2) (node A t1' b t2').

Lemma MirrorC: forall (A:Set) (t:bintree A),
{t':bintree A|(mirror A t t')} .
Proof.
  intros.
  induction t.
    exists (btree_nil A).
    constructor.

    elim IHt1; elim IHt2; intros.
    exists (node A x a x0).
    constructor.
      reflexivity.
      assumption.
      assumption.
Qed.

Fixpoint inverse (A:Set) (t:bintree A):bintree A :=
  match t with
  | btree_nil => btree_nil A
  | node t1 a t2 => node A (inverse A t2) a (inverse A t1)
  end.

Hint Constructors mirror.

Lemma MirrorInv: forall (A:Set) (t:bintree A),
{t':bintree A|(mirror A t t') /\ inverse A t = t'} .
Proof.
  intros.

  
exists (inverse A t).

  
  
Qed.

