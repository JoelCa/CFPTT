(* Práctico 5 *)

(* Ejercicio 1 *)
Require Import Coq.Lists.List.

Section Ejercicio1.

Inductive LE : nat -> nat -> Prop :=
  | Le_O : forall n : nat, LE 0 n
  | Le_S : forall n m : nat, LE n m -> LE (S n) (S m).

(* NO acepta "cons A a x", por que uso las listas de coq *)
Inductive Mem (A : Set) (a : A) : list A -> Prop :=
  | here : forall x : list A, Mem A a (cons a x)
  | there : forall x : list A, Mem A a x -> forall b : A, Mem A a (cons b x).

(* 1.1 *)
Theorem not_sn_le_o: forall n:nat, ~ LE (S n) O.
Proof.
  unfold not; intros.
   inversion H.
Qed.

(* 1.2 *)
(* NO acepta "nil A", por que uso las listas de coq *)
Theorem nil_empty: forall (A:Set) (a:A), ~ Mem A a nil.
Proof.
  unfold not; intros; inversion H.
Qed.

(* 1.3 *)
Theorem ej1_3 : ~LE 4 3.
Proof.
  unfold not; intro H.
  inversion_clear H; inversion_clear H0; inversion_clear H; inversion_clear H0.
Qed.

(* 1.4 *)
Theorem ej1_4 : forall (n:nat), ~LE (S n) n.
Proof.
  unfold not; induction n; intro H.
    inversion H.

    apply IHn.
    inversion_clear H; assumption.
Qed.

(* 1.5 *)
Theorem ej1_5 : forall (n m r:nat), LE n m /\ LE m r -> LE n r.
Proof.
  induction n; intros.
    exact (Le_O r).

    elim H; intros; clear H.
    inversion_clear H0 in H1.
    inversion_clear H1.
    exact(Le_S n m1 (IHn m0 m1 (conj H H0))).
Qed.

(* 1.6 *)
(* Tengo que definir el pertenece y el append? NO es necesario, puedo usar los de la librería *)
(* "pertenece a la concatenación de esta lista con cualquier otra", tengo que
considerar las dos concatenaciones posibles? NO *)
Theorem ej1_6 : forall (A:Set) (a:A) (l1 l2:list A), In a l1 -> In a (app l1 l2).
Proof.
  induction l1.
    intros.
    simpl in H; elim H.

    intros.
    simpl in *.
    elim H; intro H'.
      left; assumption.

      right; exact ((IHl1 l2) H').
Qed.

End Ejercicio1.



(* Ejercicio 2 *)
Section Ejercicio2.

Inductive bintree(A:Set):Set :=
    btree_nil
  | node: bintree A -> A -> bintree A -> bintree A.

Inductive isomorfismo(A:Set):bintree A -> bintree A -> Prop :=
    isomorfismoB : isomorfismo A (btree_nil A) (btree_nil A)
  | isomorfismoI : forall (t1 t2 t1' t2':bintree A) (a b : A), isomorfismo A t1 t1' -> isomorfismo A t2 t2' -> isomorfismo A (node A t1 a t2) (node A t1' b t2').

Fixpoint inverse (A:Set) (t:bintree A):bintree A :=
  match t with
  | btree_nil => btree_nil A
  | node t1 a t2 => node A (inverse A t2) a (inverse A t1)
  end.

(* 2.1 *)
Theorem ej2_1 : forall (A:Set) (t:bintree A), ~t = btree_nil A -> ~isomorfismo A (btree_nil A) t.
Proof.
  unfold not in *; intros.
  inversion H0.
  apply H; symmetry; assumption.
Qed.

(* 2.2 *)
Theorem ej2_2 : forall (A:Set) (t1 t2 t3 t4:bintree A) (a b:A), isomorfismo A (node A t1 a t2) (node A t3 b t4) -> isomorfismo A t1 t3 /\ isomorfismo A t2 t4.
Proof.
  intros.
  inversion_clear H.
  split; assumption.
Qed.

(* 2.3 *)
Theorem ej2_3 : forall (A:Set) (t1 t2 t3:bintree A), isomorfismo A t1 t2 -> isomorfismo A t2 t3 -> isomorfismo A t1 t3.
Proof.
  induction t1; intros.
    inversion_clear H in H0.
    assumption.

    inversion_clear H in H0.
    inversion_clear H0.
    constructor.
      exact((IHt1_1 t1' t1'0) H1 H).

      exact((IHt1_2 t2' t2'0) H2 H3).
Qed.

(* 2.4 *)
Theorem ej2_4 : forall (A:Set) (t1 t2:bintree A), isomorfismo A t1 t2 -> isomorfismo A (inverse A t1) (inverse A t2).
Proof.
  induction t1.
    intros.
    inversion_clear H.
    simpl; exact (isomorfismoB A).

    intros.
    inversion_clear H.
    assert (isomorfismo A (inverse A t1_1) (inverse A t1')); [exact ((IHt1_1 t1') H0)|idtac].
    assert (isomorfismo A (inverse A t1_2) (inverse A t2')); [exact ((IHt1_2 t2') H1)|idtac].
    simpl.
    exact ((isomorfismoI A (inverse A t1_2) (inverse A t1_1) (inverse A t2') (inverse A t1') a b) H2 H).
Qed.

End Ejercicio2.



(* Ejercicio 3 *)
Section Ej5_3.

Variable A : Set.

Parameter equal : A -> A -> bool.

Axiom equal1 : forall x y : A, equal x y = true -> x = y.

Axiom equal2 : forall x : A, equal x x <> false.

Inductive List : Set :=
  | nullL : List
  | consL : A -> List -> List.

Inductive MemL (a : A) : List -> Prop :=
  | hereL : forall x : List, MemL a (consL a x)
  | thereL : forall x : List, MemL a x -> forall b : A, MemL a (consL b x).

(* 3.1 *)
Inductive isSet : List -> Prop :=
  | isSetB : isSet nullL
  | isSetI : forall (l:List) (a:A), ~MemL a l -> isSet l -> isSet (consL a l).

(* 3.2 *)
Fixpoint deleteAll (a:A) (l:List):List :=
  match l with
  | nullL => nullL
  | consL x l' => if equal x a then deleteAll a l' else consL x (deleteAll a l')
  end.

(* 3.3 *)
(* equal se podría haber definido inductivamente? No, no se puede hacer "inductive" sobre
una relacion que dé bool *)
(* NO lo uso, se puede borrar *)
Lemma equal_lema1 : forall (a b:A), a = b -> equal a b = true.
Proof.
  intros.
  assert(equal a b = true \/ equal a b = false).
  destruct (equal a b); [left|right]; reflexivity.
  elim H0; intro H'; clear H0.
    assumption.
    rewrite H'.
    assert (False -> false = true); [intro H''; elim H''|idtac].
    apply H0; rewrite H in H'.
    exact ((equal2 b) H').
Qed.

(* NO lo uso, se puede borrar *)
Theorem equal_lema2 : forall (a b:A), equal a b = false -> ~a=b.
Proof.
  unfold not; intros.
  assert (equal a b = true); [exact ((equal_lema1 a b) H0)|idtac].
  rewrite H in H1; discriminate H1.
Qed.

Lemma DeleteAllNotMember : forall (l : List) (x : A), ~ MemL x (deleteAll x l).
Proof.
  unfold not; induction l; intros.
    simpl in H.
    inversion H.

    simpl in H.
    case_eq (equal a x); intro H'.
      rewrite H' in H.
      apply (IHl x); assumption.

      rewrite H' in H.
      inversion_clear H in H'.
        apply (equal2 a); assumption.

        apply (IHl x); assumption.
Qed.

(* 3.4 *)
Fixpoint delete (a:A) (l:List):List :=
  match l with
  | nullL => nullL
  | consL x l' => if equal x a then l' else consL x (delete a l')
  end.

(* 3.5 *)
Lemma DeleteNotMember : forall (l : List) (x : A), isSet l -> ~ MemL x (delete x l).
Proof.
  unfold not; induction l; intros.
    simpl in H0; inversion H0.

    simpl in H0.
    case_eq (equal a x); intro.
      rewrite H1 in H0.
      rewrite ((equal1 a x) H1) in H.
      inversion_clear H.
      absurd (MemL x l); assumption.

      rewrite H1 in H0.
      inversion_clear H.
      inversion_clear H0 in H1.
        apply (equal2 a); assumption.

        apply (IHl x); assumption.
Qed.

End Ej5_3.



(* Ejercicio 4 *)
Section Ej5_4.

Variable A : Set.

Inductive AB: Set :=
  | null : AB
  | cons: A -> AB-> AB -> AB.

(* 5.a *)
Inductive Pertenece (a:A) : AB -> Prop :=
  | perteneceB : forall (t1 t2:AB), Pertenece a (cons a t1 t2)
  | perteneceI_izq : forall (x:A) (t1 t2:AB), Pertenece a t1 -> Pertenece a (cons x t1 t2)
  | perteneceI_der : forall (x:A) (t1 t2:AB), Pertenece a t2 -> Pertenece a (cons x t1 t2).

(* 5.b *)
Parameter eqGen: A->A->bool.

Fixpoint Borrar (ab :AB) (x:A):AB :=
  match ab with
  | null => null
  | cons x' l r => if eqGen x x' then null else cons x' (Borrar l x) (Borrar r x)
  end.

(* 5.c *)
Axiom eqGen1: forall (x:A), ~(eqGen x x)=false.

(* NO lo uso, se puede borrar *)
Lemma eqGen_lema : forall (x y:A), eqGen x y = false -> ~x=y.
Proof.
  unfold not; intros.
  rewrite H0 in H.
  apply (eqGen1 y).
  assumption.
Qed.

(* Se puede probar lo que sigue? No *)
(* Lemma eqGen_lema2 : forall x y : A, eqGen x y = true -> x = y.*)

Lemma BorrarNoPertenece: forall (x:AB) (a:A), ~(Pertenece a (Borrar x a)).
Proof.
  unfold not; induction x; intros.
    simpl in H; inversion H.

    simpl in H.
    case_eq (eqGen a0 a); intro.
      rewrite H0 in H.
      inversion H.

      rewrite H0 in H.
      inversion_clear H in H0.
        apply (eqGen1 a); assumption.
        apply (IHx1 a0); assumption.
        apply (IHx2 a0); assumption.
Qed.

(* 5.d *)
Inductive SinRepetidos : AB -> Prop :=
  | sinRNull : SinRepetidos null
  | sinRB1 : forall (t:AB) (a:A), ~Pertenece a t -> SinRepetidos (cons a t null)
  | sinRB2 : forall (t:AB) (a:A), ~Pertenece a t -> SinRepetidos (cons a null t)
  | sinRI : forall (t1 t2:AB) (a:A), (forall x:A, Pertenece x t1 -> ~Pertenece x t2) ->
      SinRepetidos t1 -> SinRepetidos t2 -> ~Pertenece a t1 -> ~Pertenece a t2 -> SinRepetidos (cons a t1 t2).

End Ej5_4.



(* Ejercicio 5 *)
Section Ejercicio5.

(* Está bien? Si*)
(* 5.1 *)
Definition Var := nat.

Inductive BoolExpr : Set :=
  | var : Var -> BoolExpr
  | booleano : bool -> BoolExpr
  | disyuncion : BoolExpr -> BoolExpr -> BoolExpr
  | negacion : BoolExpr -> BoolExpr.

(* 5.2 *)
Definition Valor := bool.
Definition Memoria := Var -> Valor.
Definition lookup (m:Memoria) (v:Var):Valor := m v.

Inductive BEval : BoolExpr -> Memoria -> Valor -> Prop :=
  | evar : forall (m:Memoria) (x:Var), BEval (var x) m (lookup m x)
  | eboolt : forall (m:Memoria), BEval (booleano true) m true
  | eboolf : forall (m:Memoria), BEval (booleano false) m false
  | eorl : forall (m:Memoria) (e1 e2:BoolExpr), BEval e1 m true ->  BEval (disyuncion e1 e2) m true
  | eorr : forall (m:Memoria) (e1 e2:BoolExpr), BEval e2 m true ->  BEval (disyuncion e1 e2) m true
  | eorrl : forall (m:Memoria) (e1 e2:BoolExpr), BEval e1 m false -> BEval e2 m false -> BEval (disyuncion e1 e2) m false
  | enott : forall (m:Memoria) (e:BoolExpr), BEval e m true -> BEval (negacion e) m false
  | enotf : forall (m:Memoria) (e:BoolExpr), BEval e m false -> BEval (negacion e) m true.

(* 5.3 *)
(* 5.3.a*)
Lemma ej5_3_a : forall (m:Memoria), ~BEval (booleano true) m false.
Proof.
  unfold not; intros.
  inversion H.
Qed.

(* 5.3.b *)
Lemma ej5_3_b : forall (m:Memoria) (e1 e2:BoolExpr) (w:Valor), BEval e1 m false -> BEval e2 m w -> BEval (disyuncion e1 e2) m w.
Proof.
  destruct w.
    intros; apply eorr; assumption.

    intros; apply eorrl; assumption.
Qed.

(* 5.3.c *)
Lemma ej5_3_c : forall (m:Memoria) (e:BoolExpr) (w1 w2:Valor), BEval e m w1 -> BEval e m w2 -> w1=w2.
Proof.
  induction e; intros.
    inversion_clear H.
    inversion_clear H0.
    reflexivity.

    inversion_clear H in H0.
      inversion_clear H0.
      reflexivity.

      inversion_clear H0.
      reflexivity.
    
    inversion_clear H.
      inversion_clear H0.
        reflexivity.
        reflexivity.
        apply (IHe1 true false); assumption.

      inversion_clear H0.
        reflexivity.
        reflexivity.
        apply (IHe2 true false); assumption.

      inversion_clear H0.
        apply (IHe1 false true); assumption.
        apply (IHe2 false true); assumption.
        reflexivity.

    inversion_clear H.
      inversion_clear H0.
        reflexivity.
        apply (IHe false true); assumption.

      inversion_clear H0.
        apply (IHe true false); assumption.
        reflexivity.
Qed.

(* Prueba alternativa del ej. 5.3.c *)
Lemma ej5_3_c' : forall (m:Memoria) (e:BoolExpr) (w1:Valor), BEval e m w1 -> forall (w2:Valor), BEval e m w2 -> w1=w2.
Proof.
  intros m' e' w1' H.
  induction H; intros.
    inversion_clear H; reflexivity.

    inversion_clear H; reflexivity.

    inversion_clear H; reflexivity.

    inversion H0; [reflexivity|reflexivity|idtac].
    exact ((IHBEval false) H3).

    inversion H0; [reflexivity|reflexivity|idtac].
    exact ((IHBEval false) H6).

    inversion H1.
    exact ((IHBEval1 true) H6).
    exact ((IHBEval2 true) H6).
    reflexivity.

    inversion H0.
    reflexivity.
    symmetry.
    exact ((IHBEval false) H2).

    inversion_clear H0.
    symmetry.
    exact ((IHBEval true) H1).
    reflexivity.
Qed.

(* 5.3.d *)
Lemma ej5_3_d : forall (m:Memoria) (e1 e2:BoolExpr), BEval e1 m true -> ~ BEval (negacion (disyuncion e1 e2)) m true.
Proof.
  unfold not; intros.
  inversion_clear H0.
  inversion_clear H1.
  discriminate (ej5_3_c m e1 true false H H0).
Qed.

(* 5.4 *)
Fixpoint beval (m:Memoria) (e:BoolExpr):Valor :=
  match e with
  | var x => lookup m x
  | booleano b => b
  | disyuncion e1 e2 => 
    match beval m e1, beval m e2 with
      | false,false => false
      | _,_ => true
    end
  | negacion e1 => negb (beval m e1)
  end.

(* 5.5 *)
Lemma ej5_5 : forall (m:Memoria) (e:BoolExpr), BEval e m (beval m e).
Proof.
  induction e; simpl.
    constructor.

    case b; constructor.

    destruct (beval m e1); simpl.
      constructor; assumption.
      destruct (beval m e2).
        apply eorr; assumption.
        constructor; assumption.

    destruct (beval m e); simpl.
      constructor; assumption.
      constructor; assumption.
Qed.

End Ejercicio5.



(* Ejercicio 6 *)
Section Ejercicio6.

(* 6.1 *)
Inductive Instr : Set :=
  | skip : Instr
  | asignacion : Var -> BoolExpr -> Instr
  | ifThenElse : BoolExpr -> Instr -> Instr -> Instr
  | while : BoolExpr -> Instr -> Instr
  | begin : LInstr -> Instr

with LInstr : Set :=
  | vacio : LInstr
  | secuencia : Instr -> LInstr -> LInstr.

(* 6.2 *)
(* Por qué tiene que asociar a derecha? Por así como se define el constructor "secuencia" en la gramática *)
Infix ";" := secuencia (at level 80, right associativity).

(* Como la variable es un natural, puedo poner cualquier número para representar v1? No *)
Variables v1 v2 aux: Var.

(* 6.2.a *)
Definition PP := begin ((asignacion v1 (booleano true)) ; (asignacion v2 (negacion (var v1))) ; vacio).
Check PP.

(* 6.2.b *)
Definition swap := begin ((asignacion aux (var v1)) ; (asignacion v1 (var v2)) ; (asignacion v2 (var aux)); vacio).
Check swap.

(* 6.3 *)
(* Puedo usar beq_nat? Si *)
Require Import Coq.Arith.EqNat.

Definition update := fun (m:Memoria) (v:Var) (w:Valor) (x:Var) => if beq_nat x v then w else lookup m x.

End Ejercicio6.



(* Ejercicio 7 *)
Section Ejercicio7.

(* 7.1 *)
Inductive Execute : Instr -> Memoria -> Memoria -> Prop :=
  | xAss : forall (e:BoolExpr) (m:Memoria) (w:Valor) (v:Var), BEval e m w -> Execute (asignacion v e) m (update m v w)
  | xSkip : forall (m:Memoria), Execute skip m m
  | xIFthen : forall (c:BoolExpr) (m m1:Memoria) (p1 p2:Instr), BEval c m true ->  Execute p1 m m1 -> Execute (ifThenElse c p1 p2) m m1
  | xIFelse : forall (c:BoolExpr) (m m2:Memoria) (p1 p2:Instr), BEval c m false ->  Execute p2 m m2 -> Execute (ifThenElse c p1 p2) m m2
  | xWhileTrue : forall (c:BoolExpr) (m m1 m2:Memoria) (p :Instr), BEval c m true -> Execute p m m1 -> Execute (while c p) m1 m2 -> Execute (while c p) m m2
  | xWhileFalse : forall (c:BoolExpr) (m :Memoria) (p :Instr), BEval c m false -> Execute (while c p) m m
  | xBeginEnd : forall (c:BoolExpr) (m m1:Memoria) (p :LInstr), LExecute p m m1 -> Execute (begin p) m m1
 
with LExecute : LInstr -> Memoria -> Memoria -> Prop :=
  | xEmptyblock : forall (m:Memoria), LExecute vacio m m
  | xNext : forall (i:Instr) (li:LInstr) (m m1 m2:Memoria), Execute i m m1 -> LExecute li m1 m2 -> LExecute (secuencia i li) m m2.

(* 7.2 *)
Lemma ej7_2 : forall (e1 e2:Instr) (m m':Memoria), Execute (ifThenElse (negacion (booleano true)) e1 e2) m m' -> Execute (ifThenElse (booleano true) e2 e1) m m'.
Proof.
  intros.
  inversion_clear H.
    inversion_clear H0.
    inversion_clear H.

    inversion_clear H0.
    apply xIFthen; assumption.
Qed.

(* 7.3 *)
Lemma ej7_3 : forall (e1 e2:Instr) (m m':Memoria) (c:BoolExpr), Execute (ifThenElse (negacion c) e1 e2) m m' -> Execute (ifThenElse c e2 e1) m m'.
Proof.
  intros.
  inversion_clear H.
    inversion_clear H0.
    apply xIFelse; assumption.

    inversion_clear H0.
    apply xIFthen; assumption.
Qed.

(* 7.4 *)
Lemma ej7_4 : forall (p: Instr) (m m':Memoria), Execute (while (booleano false) p) m m' -> m = m'.
Proof.
  intros.
  inversion_clear H.
    inversion H0.
    reflexivity.
Qed.

(* 7.5 *)
Lemma ej7_5 : forall (c:BoolExpr) (p:Instr) (m m':Memoria), Execute (begin (secuencia (ifThenElse c p skip) (secuencia (while c p) vacio))) m m' -> Execute (while c p) m m'.
Proof.
  intros.
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H2 in H0.
  inversion_clear H.
    apply (xWhileTrue c m m1 m'); assumption.

    inversion_clear H2.
    assumption.
Qed.

(* 7.6 *)
Require Import Coq.Arith.EqNat.
Check beq_nat_false_iff.

Lemma ej7_6 : forall (m m':Memoria) (v1 v2:Var), ~v1=v2 -> Execute (PP v1 v2) m m' -> lookup m' v2 = false /\ lookup m' v1 = true.
Proof.
  intros.
  inversion_clear H0.
  inversion_clear H1.
  inversion H0.
  inversion_clear H6 in H5.
  rewrite <- H5 in H2.
  inversion_clear H2.
  inversion_clear H7 in H6.
  inversion_clear H6.
  inversion_clear H2.
    unfold update, lookup.
    rewrite <- (beq_nat_refl v2).
    rewrite -> (proj2 (beq_nat_false_iff v1 v2) H).
    rewrite <- (beq_nat_refl v1).
    split; reflexivity.

    inversion H6.
    unfold update, lookup in H9.
    rewrite <- (beq_nat_refl v1) in H9.
    discriminate H9.
Qed.

End Ejercicio7.