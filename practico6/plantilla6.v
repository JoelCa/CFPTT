(* Práctico 6 *)

(* Ejercicio 1 *)
Section Ejercicio1.

(* 1.1 *)
Lemma predspec : forall n : nat, {m : nat | n = 0 /\ m = 0 \/ n = S m}.
Proof.
  intros.
  destruct n.
    exists 0.
    left.
    split; reflexivity.

    exists n.
    right.
    reflexivity.
Qed.
End Ejercicio1.

(* 1.2 *)
(*Extraction Language Haskell.
Extraction "predecesor" predspec.*)

(* Ejercicio 2 *)
Section Ejercicio2.

Inductive bintree(A:Set):Set :=
    btree_nil
  | node: bintree A -> A -> bintree A -> bintree A.

Inductive mirror(A:Set):bintree A -> bintree A -> Prop :=
    mirrorB : mirror A (btree_nil A) (btree_nil A) 
  | mirrorI : forall (t1 t2 t1' t2':bintree A) (a b : A), a = b -> mirror A t1 t2' -> mirror A t2 t1' -> mirror A (node A t1 a t2) (node A t1' b t2').

(* 2.1 *)
Lemma MirrorC: forall (A:Set) (t:bintree A), {t':bintree A|(mirror A t t')} .
Proof.
  intros; induction t.
    exists (btree_nil A).
    constructor.

    elim IHt1; elim IHt2; intros; clear IHt1; clear IHt2.
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
Functional Scheme inverse_ind := Induction for inverse Sort Prop. (* Está bien? *)
Check inverse_ind.

(* 2.2 *)
(* Al probarlo, puedo concluir que inverse construye el arbol espejo de su entrada? *)
Lemma MirrorInv: forall (A:Set) (t:bintree A), {t':bintree A | mirror A t t'} .
Proof.
  intros.
  exists (inverse A t).
  functional induction (inverse A t); auto.
Qed.

End Ejercicio2.

(* 2.3 *)
(* Extraigo el 2.1 o 2.2 ? *)
Extraction Language Haskell.
Extraction "/home/joel/facultad/Construcción Formal de Programas en Teoría de Tipos/practico6/mirror_function" MirrorInv.


(* Ejercicio 3 *)
Section Ejercicio3.

Definition Value := bool.

Inductive BoolExpr : Set :=
  | bbool : bool -> BoolExpr
  | or : BoolExpr -> BoolExpr -> BoolExpr
  | bnot : BoolExpr -> BoolExpr.

Inductive BEval : BoolExpr -> Value -> Prop :=
  | ebool : forall b : bool, BEval (bbool b) (b:Value)
  | eorl : forall e1 e2 : BoolExpr, BEval e1 true -> BEval (or e1 e2) true
  | eorr : forall e1 e2 : BoolExpr, BEval e2 true -> BEval (or e1 e2) true
  | eorrl : forall e1 e2 : BoolExpr, BEval e1 false -> BEval e2 false -> BEval (or e1 e2) false
  | enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
  | enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true.

Fixpoint beval (e : BoolExpr) : Value :=
  match e with
  | bbool b => b
  | or e1 e2 =>
    match beval e1, beval e2 with
    | false, false => false
    | _, _ => true
    end
  | bnot e1 => if beval e1 then false else true
  end.

Fixpoint sbeval (e : BoolExpr) : Value :=
  match e with
  | bbool b => b
  | or e1 e2 =>
    match sbeval e1 with
    | true => true
    | _ => sbeval e2
    end
  | bnot e1 => if sbeval e1 then false else true
  end.

Functional Scheme beval_ind := Induction for beval Sort Prop. (* Está bien? *)
Functional Scheme sbeval_ind := Induction for sbeval Sort Prop.
Check beval_ind.

(* 3.1 *)
(* Se puede usar "functional induction"? *)
Theorem BevalInv : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intros; exists (beval e).
  functional induction (beval e).
    constructor.

    rewrite e3 in IHv.
    apply eorl; assumption.

    rewrite e4 in IHv0.
    apply eorr; assumption.

    rewrite e3 in IHv; rewrite e4 in IHv0.
    constructor; assumption.

    rewrite e2 in IHv; constructor; assumption.

    rewrite e2 in IHv; constructor; assumption.
Qed.

Theorem SbevalInv : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intros; exists (sbeval e).
  functional induction (sbeval e).
    constructor.

    rewrite e3 in IHv.
    apply eorl; assumption.

    rewrite e3 in IHv.
    destruct (sbeval e2).
      apply eorr; assumption.

      constructor; assumption.

    rewrite e2 in IHv; constructor; assumption.

    rewrite e2 in IHv; constructor; assumption.
Qed.


Hint Constructors BEval.

(* 3.2 *)
Theorem BevalInvAuto : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intros; exists (beval e).
  functional induction (beval e); auto.
    rewrite e3 in IHv; auto.
    rewrite e4 in IHv0; auto.
    rewrite e3 in IHv; rewrite e4 in IHv0; auto.
    rewrite e2 in IHv; auto.
    rewrite e2 in IHv; auto.
Qed.

Theorem SbevalInvAuto : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intros; exists (sbeval e).
  functional induction (sbeval e); auto.
    rewrite e3 in IHv; auto.

    rewrite e3 in IHv.
    destruct (sbeval e2); auto.

    rewrite e2 in IHv; auto.

    rewrite e2 in IHv; auto.
Qed.

End Ejercicio3.

(* 3.3 *)
(* El código de beval y sbeval NO varía, está bien? *)
Extraction Language Haskell.
Extraction "/home/joel/facultad/Construcción Formal de Programas en Teoría de Tipos/practico6/beval_function" BevalInvAuto.

Extraction "/home/joel/facultad/Construcción Formal de Programas en Teoría de Tipos/practico6/sbeval_function" SbevalInvAuto.

Extract Inductive bool => "bool" [ "true" "false" ].

Extraction "/home/joel/facultad/Construcción Formal de Programas en Teoría de Tipos/practico6/beval2_function" BevalInvAuto.

Extraction "/home/joel/facultad/Construcción Formal de Programas en Teoría de Tipos/practico6/sbeval2_function" SbevalInvAuto.

(* Ejercicio 4 *)

Section list_perm.

Variable A:Set.

Inductive list : Set :=
  | nil : list
  | cons : A -> list -> list.

Fixpoint append (l1 l2 : list) {struct l1} : list :=
  match l1 with
  | nil => l2
  | cons a l => cons a (append l l2)
  end.

Inductive perm : list -> list ->Prop:=
  |perm_refl: forall l, perm l l
  |perm_cons: forall a l0 l1, perm l0 l1-> perm (cons a l0)(cons a l1)
  |perm_app: forall a l, perm (cons a l) (append l (cons a nil))
  |perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Hint Constructors perm.

(* 2.1 *)
Fixpoint reverse(l:list):list :=
  match l with
  | nil => nil
  | cons x l' => append (reverse l') (cons x nil)
  end.

(* 2.2 *)
Lemma Ej6_4: forall l: list, {l2: list | perm l l2}.
Proof.
  intros; exists (reverse l).
  induction l.
    auto.
    simpl.
    assert (perm (cons a l) (cons a (reverse l))).
      apply perm_cons; assumption.
    apply (perm_trans (cons a l) (cons a (reverse l)) (append (reverse l) (cons a nil))).
      assumption.
      constructor.
Qed.

End list_perm.

(* Ejercicio 5 *)
Section Ejercicio5.

Inductive Le:nat -> nat -> Prop :=
  | menorB : forall (n:nat), Le 0 n
  | menorI : forall (n m:nat), Le n m -> Le (S n) (S m).

Inductive Gt:nat -> nat -> Prop :=
  | mayorB : forall (n:nat), Gt n 0
  | mayorI : forall (n m: nat), Gt n m -> Gt (S n) (S m).

Fixpoint leBool(n m:nat) {struct n}:bool:=
  match n, m with
  | 0, _ => true
  | S x, 0 => false
  | S x, S y => leBool x y
  end.


Functional Scheme leBool_ind := Induction for leBool Sort Prop.
Check leBool_ind.


(* NO puedo hacer "functional induction" directamente sobre {A}+{B}. *)
Theorem Le_Gt_dec: forall n m:nat, {(Le n m)}+{(Gt n m)}.
Proof.
  intros.
  case_eq (leBool n m); intros.
  left.
  functional induction (leBool n m).
    constructor.
    discriminate H.
    constructor; exact (IHb H).

    right.
    functional induction (leBool n m).
    discriminate H.
    constructor.
    constructor; exact (IHb H).
Qed.

End Ejercicio5.





















