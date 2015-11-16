(* Práctico 6 *)

(* Ejercicio 1 *)
Section Ejercicio1.

(* 1.1 *)
Lemma predspec : forall n : nat, {m : nat | n = 0 /\ m = 0 \/ n = S m}.
Proof.
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
  | nodeB: bintree A -> A -> bintree A -> bintree A.

Inductive mirror(A:Set):bintree A -> bintree A -> Prop :=
    mirrorB : mirror A (btree_nil A) (btree_nil A) 
  | mirrorI : forall (t1 t2 t1' t2':bintree A) (a b : A), a = b -> mirror A t1 t2' -> mirror A t2 t1' -> mirror A (nodeB A t1 a t2) (nodeB A t1' b t2').

(* 2.1 *)
Lemma MirrorC: forall (A:Set) (t:bintree A), {t':bintree A|(mirror A t t')} .
Proof.
  induction t.
    exists (btree_nil A).
    constructor.

    elim IHt1; elim IHt2; intros; clear IHt1; clear IHt2.
    exists (nodeB A x a x0).
    constructor.
      reflexivity.
      assumption.
      assumption.
Qed.

Fixpoint inverse (A:Set) (t:bintree A):bintree A :=
  match t with
  | btree_nil => btree_nil A
  | nodeB t1 a t2 => nodeB A (inverse A t2) a (inverse A t1)
  end.

Hint Constructors mirror.

Functional Scheme inverse_ind := Induction for inverse Sort Prop.
Check inverse_ind.

(* 2.2 *)
(* Al probarlo, puedo concluir que inverse construye el arbol espejo de su entrada? Sí *)
Lemma MirrorInv: forall (A:Set) (t:bintree A), {t':bintree A | mirror A t t'} .
Proof.
  intros.
  exists (inverse A t).
  functional induction (inverse A t); auto.
Qed.

End Ejercicio2.

(* 2.3 *)
(* Extraigo el 2.1 o 2.2 ? *)
(* Extraction Language Haskell.
Extraction "/home/joel/facultad/Construcción Formal de Programas en Teoría de Tipos/practico6/mirror_function" MirrorInv.
*)

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

Functional Scheme beval_ind := Induction for beval Sort Prop.
Functional Scheme sbeval_ind := Induction for sbeval Sort Prop.
Check beval_ind.

(* 3.1 *)
(* Se puede usar "functional induction"? *)
Theorem LazyBEval : forall e:BoolExpr, {b:Value |(BEval e b)}.
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

Theorem EagerBEval : forall e:BoolExpr, {b:Value |(BEval e b)}.
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
Theorem ej3_2_lazy : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intros; exists (beval e).
  functional induction (beval e); auto.
    rewrite e3 in IHv; auto.

    rewrite e4 in IHv0; auto.

    rewrite e3 in IHv; rewrite e4 in IHv0; auto.

    rewrite e2 in IHv; auto.

    rewrite e2 in IHv; auto.
Qed.

Theorem ej3_2_eager : forall e:BoolExpr, {b:Value |(BEval e b)}.
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
(*
Coq hace optimizaciones, por eso el código tanto de beval como sbeval es el mismo.
Eval compute in (beval (or (bbool true) (bbool false))).
*)

Extraction Language Haskell.
Unset Extraction Optimize.
Extraction "beval" LazyBEval EagerBEval ej3_2_lazy ej3_2_eager.

(* Borrar la línea "import qualified Prelude" *)
Extract Inductive bool => "Bool" [ "True" "False" ].
Extraction "beval_bool" LazyBEval EagerBEval ej3_2_lazy ej3_2_eager.

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

(* 4.1 *)
Fixpoint reverse(l:list):list :=
  match l with
  | nil => nil
  | cons x l' => append (reverse l') (cons x nil)
  end.

(* 4.2 *)
Lemma Ej6_4_2: forall l: list, {l2: list | perm l l2}.
Proof.
  intros; exists (reverse l).
  induction l; auto.
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

Function leBool(n m:nat) {struct n}:bool:=
  match n, m with
  | 0, _ => true
  | S x, 0 => false
  | S x, S y => leBool x y
  end.

(* 5.2 *)
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

(* 5.3 *)
(* Omega resuelve algunas ecuaciones aritméticas decidibles *)
Require Import Omega.

Theorem le_gt_dec: forall n m:nat, {(le n m)}+{(gt n m)}.
Proof.
  intros.
  case_eq (leBool n m); intros.  
    left.
    functional induction (leBool n m).
      omega.
      discriminate H.
      assert (le x y).
      exact (IHb H).
      omega.

    right.
    functional induction (leBool n m).
      discriminate.
      omega.
      assert (gt x y).
      exact (IHb H).
      omega.
Qed.

End Ejercicio5.



(* Ejercicio 6 *)
Section Ejercicio6.

Require Import Omega.
Require Import DecBool. 
Require Import Compare_dec.
Require Import Plus.
Require Import Mult.

Definition spec_res_nat_div_mod (a b:nat) (qr:nat*nat) :=
  match qr with
    (q,r) => (a = b*q + r) /\ r < b
  end.

(* Por qué cuando se define nat_div_mod, espera una prueba?*)
Definition nat_div_mod :
  forall a b:nat, not(b=0) -> {qr:nat*nat | spec_res_nat_div_mod a b qr}.
Proof.
  intros.
  induction a.
    exists (pair 0 0).
    simpl.
    omega.

    elim IHa; intros; clear IHa.
    unfold  spec_res_nat_div_mod in p.
    rewrite (surjective_pairing x) in p. (* De ésta forma me deshago del LET *)
    elim p; intros; clear p.
    elim (le_lt_dec (S (S (snd x))) b); intro.
      exists (((fst x), S (snd x))).
      simpl.
      split.
        rewrite <- (plus_Snm_nSm (b * fst x) (snd x)).
        simpl.
        apply f_equal.
        assumption.

        unfold lt in H1.
        elim ((le_lt_or_eq (S(snd x)) b) H1); intro.
          auto.

          rewrite H2 in a0.
          elim ((le_Sn_n b) a0).

      exists (S(fst x), 0).
      simpl.
      unfold lt in *.
      assert (le (S(S (snd x))) (S b)).
      exact ((le_n_S (S(snd x)) b) H1).
      assert ((S (S (snd x))) = S b).
      exact (le_antisym  (S (S (snd x))) (S b) H2 b0).
      injection H3; intro.
      rewrite <- H4.
      split.
        simpl.
        apply f_equal.
        rewrite <- H4 in H0.
        simpl in H0.
        rewrite (mult_succ_r (snd x) (fst x)).
        omega.

        omega.
Qed.

End Ejercicio6.



(* Ejercicio 7 *)
Section Ejercicio7.

Inductive tree (A:Set) : Set :=
  | leaf : tree A
  | node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A:Set) (t:tree A) : tree A -> Prop :=
  | tree_sub1 : forall (t':tree A) (x:A), tree_sub A t (node A x t t')
  | tree_sub2 : forall (t':tree A) (x:A), tree_sub A t (node A x t' t).

(* Extra: Prueba extraida del libro *)
Theorem lt_Acc : forall n:nat, Acc lt n.
Proof.
  induction n.
    constructor.
    intros p H. 
    inversion H.
    constructor.
    intros y H0.
    (*inversion IHn.*)
    Print le_lt_or_eq.
    case (le_lt_or_eq _ _ H0).
      intro H1.
      apply Acc_inv with n; auto with arith.
      
      intro e; injection e; intro e1; rewrite e1; assumption.
Qed.


Theorem well_founded_tree_sub : forall A:Set, well_founded (tree_sub A).
Proof.
  unfold well_founded.
  induction a.
    constructor.
    intros y H.
    inversion H.

    constructor.
    intros y H.
    inversion_clear H; assumption.
Qed.

End Ejercicio7.



(* Ejercicio 8 *)
Section Ejercicio8.

(* Esta bien que cuente los constructores? Sí *)
(* 8.1 *)
Fixpoint size (e:BoolExpr):nat :=
  match e with
  | bbool b => 1
  | or e1 e2 => S(size e1 + size e2)
  | bnot e1 => S(size e1)
  end. 

Definition elt (e1 e2 : BoolExpr) := size e1 < size e2.

(* 8.2 *)
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Wellfounded.Inverse_Image.

Theorem elt_acc : well_founded elt.
Proof.
  unfold well_founded, elt.
  apply (wf_inverse_image).
  apply lt_wf.
Qed.

End Ejercicio8.



(* Ejercicio 9 *)
Section Ejercicio9.

Theorem minus_decrease : forall x y, x >= y -> y<>0 -> x - y < x.
Proof.
  intros; omega.
Qed.

Require Import Coq.Arith.Bool_nat.

(* En "a divmod b", b != 0 *)
Fixpoint divmod_aux (a b: nat) (H:Acc lt a) (H1: b<>0) {struct H}:nat*nat :=
  match lt_ge_dec a b with
  | left _ => (0,a)
  | right x =>
    let (q,r) := divmod_aux (a-b) b (Acc_inv H (a-b) (minus_decrease a b x H1)) H1 in (S q, r)
  end.

Definition divmod (a b:nat) (H:b<>0):nat*nat := divmod_aux a b (lt_wf a) H.

(*
Lemma ll:3<>0.
Proof.
  auto.
Qed.

Eval compute in (divmod 5 3 ll).
*)

End Ejercicio9.



(* Ejercicio 10 *)

Section Ejercicio10.

Definition listN := list nat.

Function insert' (n:nat) (l:listN):listN :=
  match l with
  | nil => cons nat n (nil nat)
  | cons a l' => if leb a n then cons nat a (insert' n l') else cons nat n (cons nat a l')
  end.

Function insert_sort (l:listN):listN :=
  match l with
  | nil => nil nat
  | cons a l' => insert' a (insert_sort l')
  end.

Inductive permutacion (A:Set): list A -> list A ->Prop:=
  |permutacion_refl: forall l, permutacion A l l
  |permutacion_cons: forall a l0 l1, permutacion A l0 l1-> permutacion A (cons A a l0)(cons A a l1)
  |p_ccons: forall a b l, (permutacion A (cons A a (cons A b l)) (cons A b (cons A a l)))
  |permutacion_trans: forall l1 l2 l3, permutacion A l1 l2 -> permutacion A l2 l3 -> permutacion A l1 l3.

Inductive sorted (A:Set):(A->A->Prop) -> list A -> Prop :=
  | sortedBNil : forall R:A->A->Prop, sorted A R (nil A)
  | sortedBUnit : forall (R:A->A->Prop) (a:A) (l:list A), sorted A R (cons A a (nil A))
  | sortedI : forall (R:A->A->Prop) (a b : A) (l:list A),
      sorted A R (cons A b l) -> R a b -> sorted A R (cons A a (cons A b l)).


Lemma tailSort : forall (l:listN) (a:nat), sorted nat le (cons nat a l) -> sorted nat le l.
Proof.
  destruct l.
    intros.
    constructor.

    intros.
    inversion_clear H.
    assumption.
Qed.

Lemma permInsert : forall (l:listN) (a:nat), permutacion nat (cons nat a l) (insert' a l).
Proof.
  destruct l; intro a.
    simpl.
    constructor.

    functional induction (insert' a (cons nat n l)).
      constructor.

      assert (permutacion nat (cons nat a0 (cons nat a l')) (cons nat a0 (insert' a l'))).
      constructor; assumption.
      assert (permutacion nat (cons nat a (cons nat a0 l')) (cons nat a0 (cons nat a l'))).
      constructor.
      apply permutacion_trans with (cons nat a0 (cons nat a l')); assumption.

      constructor.
Qed.

Theorem SORT: forall l:(list nat), {s:(list nat) | (sorted nat le s) /\ (permutacion nat l s)}.
Proof.
  intro l; exists (insert_sort l).
  split.
    induction l.
      simpl.
      constructor.

      simpl.
      functional induction (insert' a (insert_sort l)).
        constructor. (* ME DEJA: list nat*)
        auto.
        
        assert (sorted nat le (insert' a l')); [exact (IHl1 (tailSort l' a0 IHl))|idtac].
        clear IHl1.
        functional induction (insert' a l').
          constructor.
            constructor; auto.
            apply leb_complete; assumption.

          inversion_clear IHl.
          constructor; assumption.

          constructor.
            assumption.
            apply leb_complete; assumption.

        constructor.
          assumption.
          assert (a < a0); [exact (leb_complete_conv a a0 e0)|idtac]. 
          omega.

    induction l.
      simpl; constructor.
      simpl. 

      functional induction (insert' a (insert_sort l)).
        constructor; assumption.

        clear IHl1.
        assert (permutacion nat (cons nat a0 (cons nat a l')) (cons nat a0 (insert' a l'))).
        constructor.
        apply permInsert.
        assert (permutacion nat (cons nat a (cons nat a0 l')) (cons nat a0 (cons nat a l'))).
        constructor.
        assert (permutacion nat (cons nat a l) (cons nat a (cons nat a0 l'))).
        constructor; assumption.
        apply permutacion_trans with (cons nat a0 (cons nat a l')).
          apply permutacion_trans with (cons nat a (cons nat a0 l')).
            assumption.
            assumption.
          assumption.

        constructor.
        assumption.
Qed.

End Ejercicio10.


(* Ejercicio 10 *)
(* Versión sin cambiar el constructor "perm_app" INCOMPLETA *)
(*
Section Ejercicio10.

Definition listN := list nat.

Fixpoint insert' (n:nat) (l:listN):listN :=
  match l with
  | nil => cons nat n (nil nat)
  | cons a l' => if leb a n then cons nat a (insert' n l') else cons nat n (cons nat a l')
  end.

Fixpoint insert_sort (l:listN):listN :=
  match l with
  | nil => nil nat
  | cons a l' => insert' a (insert_sort l')
  end.

Functional Scheme insert_sort_ind := Induction for insert_sort Sort Prop.
Functional Scheme insert'_ind := Induction for insert' Sort Prop.


Inductive sorted (A:Set):(A->A->Prop) -> list A -> Prop :=
  | sortedBNil : forall R:A->A->Prop, sorted A R (nil A)
  | sortedBUnit : forall (R:A->A->Prop) (a:A) (l:list A), sorted A R (cons A a (nil A))
  | sortedI : forall (R:A->A->Prop) (a b : A) (l:list A),
      sorted A R (cons A b l) -> R a b -> sorted A R (cons A a (cons A b l)).

Lemma tailSort : forall (l:listN) (a:nat), sorted nat le (cons nat a l) -> sorted nat le l.
Proof.
  destruct l.
    intros.
    constructor.

    intros.
    inversion_clear H.
    assumption.
Qed.

(*  PROBAR *)
Parameter appendAsoc : forall (A : Set) (l m n : list A), append A l (append A m n) = append A (append A l m) n.

Lemma permInversion : forall (A : Set) (l : list A) (a0 a1 : A),
  perm A (cons A a0 (cons A a1 l)) (append A l (cons A a0 (cons A a1 (nil A)))).
Proof.
    intros.
    assert (perm A (cons A a0 (cons A a1 l)) (append A (cons A a1 l) (cons A a0 (nil A)))).
    constructor.
    assert (perm A (append A (cons A a1 l) (cons A a0 (nil A)))
      (cons A a1 (append A l (cons A a0 (nil A))))).
    simpl; constructor.
    assert (perm A (cons A a1 (append A l (cons A a0 (nil A))))
      (append A (append A l (cons A a0 (nil A))) (cons A a1 (nil A)))).
    constructor.
    assert (perm A (append A (append A l (cons A a0 (nil A))) (cons A a1 (nil A)))
      (append A l (cons A a0 (cons A a1 (nil A))))).
    rewrite <- (appendAsoc A l (cons A a0 (nil A)) (cons A a1 (nil A))).
    simpl; constructor.
    apply perm_trans with (append A (append A l (cons A a0 (nil A))) (cons A a1 (nil A))).
    apply perm_trans with (cons A a1 (append A l (cons A a0 (nil A)))).
    apply perm_trans with (append A (cons A a1 l) (cons A a0 (nil A))).
    assumption.
    assumption.
    assumption.
    assumption.
Qed.

(* NO ME SALE *)
Lemma permInversion2: forall (A : Set) (l : list A) (a : A),
  perm A (append A l (cons A a (nil A))) (cons A a l).
Proof.
  intros.
  induction l.
    simpl.
    constructor.
    simpl.
    apply (perm_trans A ((cons A a0 (append A l (cons A a (nil A))))) (cons _ a0 (cons _ a l)) _).
    constructor.
    assumption.
Qed.


(* PROBAR *)
Lemma permSimetria : forall (A : Set) (l l': list A), perm A l l' -> perm A l' l.
Proof.
  intros.
    induction H.
      constructor.
      constructor; assumption.
      simpl.
      induction l.
        simpl.
        constructor.
        simpl.
        assert (perm A (append A (cons A a0 l) (cons A a (nil A))) (cons A a (cons A a0 l))).
        apply permInversion2.
        assert (perm A (cons A a0 (append A l (cons A a (nil A)))) (append A (cons A a0 l) (cons A a (nil A)))).
        simpl.
        constructor.
        apply perm_trans with (append A (cons A a0 l) (cons A a (nil A))).
        assumption.
        assumption.
        apply perm_trans with l2; assumption.
Qed.

Lemma permLema : forall (A:Set) (l:list A) (a0 a1:A),
  perm A (cons A a0 (cons A a1 l)) (cons A a1 (cons A a0 l)) <->
    (perm A (append A l (cons A a0 (cons A a1 (nil A))))
      (append A l (cons A a1 (cons A a0 (nil A))))).
Proof.
  intros; unfold iff.
  split; intro H.
    assert (perm A (append A l (cons A a0 (cons A a1 (nil A)))) (cons A a0 (cons A a1 l))).
    apply permSimetria.
    apply permInversion.
    assert (perm A (cons A a1 (cons A a0 l)) (append A l (cons A a1 (cons A a0 (nil A))))).
    apply permInversion.
    apply perm_trans with (cons A a1 (cons A a0 l)).
    apply perm_trans with (cons A a0 (cons A a1 l)).
    assumption.
    assumption.
    assumption.

    assert (perm A (cons A a0 (cons A a1 l)) (append A l (cons A a0 (cons A a1 (nil A))))).
    apply permInversion.
    assert (perm A (append A l (cons A a1 (cons A a0 (nil A)))) (cons A a1 (cons A a0 l))).
    apply permSimetria; apply permInversion.
    apply perm_trans with (append A l (cons A a1 (cons A a0 (nil A)))).
    apply perm_trans with (append A l (cons A a0 (cons A a1 (nil A)))).
    assumption.
    assumption.
    assumption.
Qed.


Lemma permSwap : forall (l:listN) (a a0:nat), perm nat (cons nat a (cons nat a0 l)) (cons nat a0 (cons nat a l)).
Proof.
  induction l; intros.
     apply perm_app.

      assert (perm nat (cons nat a0 (cons nat a1 l)) (cons nat a1 (cons nat a0 l))).
      apply IHl.
      assert (perm nat (append nat l (cons nat a0 (cons nat a1 (nil nat))))
        (append nat l (cons nat a1 (cons nat a0 (nil nat))))).
      Print proj2.
      apply (proj1 (permLema nat l a0 a1)); assumption.
      assert (perm nat (cons nat a (append nat l (cons nat a0 (cons nat a1 (nil nat)))))
        (cons nat a (append nat l (cons nat a1 (cons nat a0 (nil nat)))))).
      constructor; assumption.
      apply (permLema nat (cons nat a l) a0 a1).
      simpl; assumption.
Qed.

Lemma permInsert : forall (l:listN) (a:nat), perm nat (cons nat a l) (insert' a l).
Proof.
  destruct l; intro a.
    simpl.
    constructor.

    functional induction (insert' a (cons nat n l)).
      constructor.

      assert (perm nat (cons nat a0 (cons nat a l')) (cons nat a0 (insert' a l'))).
      constructor; assumption.
      assert (perm nat (cons nat a (cons nat a0 l')) (cons nat a0 (cons nat a l'))).
      apply permSwap.
      apply perm_trans with (cons nat a0 (cons nat a l')); assumption.

      constructor.
Qed.

Theorem SORT: forall l:(list nat), {s:(list nat) | (sorted nat le s) /\ (perm nat l s)}.
Proof.
  intro l; exists (insert_sort l).
  split.
    induction l.
      simpl.
      constructor.

      simpl.
      functional induction (insert' a (insert_sort l)).
        constructor. (* ME DEJA: list nat*)
        auto.
        
        assert (sorted nat le (insert' a l')); [exact (IHl1 (tailSort l' a0 IHl))|idtac].
        clear IHl1.
        functional induction (insert' a l').
          constructor.
            constructor; auto.
            apply leb_complete; assumption.

          inversion_clear IHl.
          constructor; assumption.

          constructor.
            assumption.
            apply leb_complete; assumption.

        constructor.
          assumption.
          assert (a < a0); [exact (leb_complete_conv a a0 e0)|idtac]. 
          omega.

    induction l.
      simpl; constructor.
      simpl. 

      functional induction (insert' a (insert_sort l)).
        apply perm_cons; assumption.

        clear IHl1.
        assert (perm nat (cons nat a0 (cons nat a l')) (cons nat a0 (insert' a l'))).
        constructor.
        apply permInsert.
        assert (perm nat (cons nat a (cons nat a0 l')) (cons nat a0 (cons nat a l'))).
        apply permSwap.
        assert (perm nat (cons nat a l) (cons nat a (cons nat a0 l'))).
        constructor; assumption.
        apply perm_trans with (cons nat a0 (cons nat a l')).
          apply perm_trans with (cons nat a (cons nat a0 l')).
            assumption.
            assumption.
          assumption.

        constructor.
        assumption.
Qed.        

End Ejercicio10.
*)