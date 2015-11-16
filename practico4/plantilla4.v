(* Práctica 4 *)

(* Ejercicio 1 *)
Section Ejercicio1.

(* 1.1 *)
Inductive list (A: Set) :  Set :=
    nil
  | cons : A -> list A -> list A. (* se puede hacer: forall A:Set...? solo si se definio como list: Set -> Set *)

Check nil.
Check cons.

Inductive bintree(A:Set):Set :=
    btree_nil
  | node: bintree A -> A -> bintree A -> bintree A.

Check bintree_ind.

(* 1.2 *)
Inductive Array (A:Set): nat -> Set :=
    array_nil : Array A 0
  | array_cons : forall n:nat, A -> Array A n -> Array A (S n).

Inductive Matrix (A:Set): nat -> nat -> Set :=
    matrix_nil : Matrix A 0 0
  | ins_fila : forall n m:nat, Array A m -> Matrix A n m -> Matrix A (S n) m.

(* 1.3 *)
Inductive leq : nat -> nat -> Prop :=
    leq0 : forall n:nat, leq 0 n
  | leqS : forall n m:nat, leq n m -> leq (S n) (S m).

(* 1.4 *)
Inductive eq_list (A:Set):list A -> list A -> Prop :=
    eq0 : eq_list A (nil A) (nil A)
  | eqS : forall (a b:A) (l1 l2:list A), eq_list A l1 l2 -> a = b -> eq_list A (cons A a l1) (cons A b l2).
(* Alternativamente podría hacer forall (a:A) (l1 l2:list A), eq_list A l1 l2 -> eq_list A (cons A a l1) (cons A a l2),
pero deja "implicita" la igual, hay casos donde NO podría aplicarse, dado que la igualdad no es obvia *)

(* 1.5 *)
Inductive sorted (A:Set):(A->A->Prop) -> list A -> Prop :=
  | sortedBNil : forall R:A->A->Prop, sorted A R (nil A)
  | sortedBUnit : forall (R:A->A->Prop) (a:A) (l:list A), sorted A R (cons A a (nil A))
  | sortedI : forall (R:A->A->Prop) (a b : A) (l:list A),
      sorted A R (cons A b l) -> R a b -> sorted A R (cons A a (cons A b l)).

(* 1.6 *)
Inductive mirror(A:Set):bintree A -> bintree A -> Prop :=
    mirror0 : mirror A (btree_nil A) (btree_nil A) 
  | mirrorS : forall (t1 t2 t1' t2':bintree A) (a b : A), a = b -> mirror A t1 t2' -> mirror A t2 t1' -> mirror A (node A t1 a t2) (node A t1' b t2').

(* 1.7 *)
(* isomorfismo entre arboles binarios *)
Inductive isomorfismo(A:Set):bintree A -> bintree A -> Prop :=
    isomorfismo0 : isomorfismo A (btree_nil A) (btree_nil A)
  | isomorfismoS : forall (t1 t2 t1' t2':bintree A) (a b : A), isomorfismo A t1 t1' -> isomorfismo A t2 t2' -> isomorfismo A (node A t1 a t2) (node A t1' b t2').

(* 1.8 *)
(* está bien? *)
Inductive
 Gtree(A:Set):Set :=
     empty_gtree : Gtree A
   | node_gtree : A -> Forest A -> Gtree A
with
 Forest(A:Set):Set :=
    empty_forest : Forest A
  | branch_forest : Gtree A -> Forest A -> Forest A.

End Ejercicio1.


(* Ejercicio 2 *)
Section Ejercicio2.

(* 2.1 *)
Definition Or (a:bool) (b:bool):bool :=
  match a with
  | false => b
  | _ => true
  end.

Definition And (a:bool) (b:bool):bool :=
  match a with
  | true => b
  | _ => false
  end.

Definition Not (a:bool):bool :=
  match a with
  | true => false
  | _ => true
  end.

Definition Xor (a:bool) (b:bool):bool :=
  match b with
  | false => a
  | _ => Not a
  end.

(* 2.2 *)
Definition is_nil (A:Set)(a:list A):bool :=
  match a with
  | nil => true
  | _ => false
  end.
End Ejercicio2.


(* Ejercicio 3 *)
Section Ejercicio3.
(* 3.1 *)
(* El "struc" indica el argumento que será estructuralmente menor
en la llamada recursiva, en general no es necesario. *)
Fixpoint sum (n m:nat) {struct n}: nat :=
  match n with
  | 0 => m
  | S k => S (sum k m)
  end.

(* 3.2 *)
Fixpoint prod (n m:nat) {struct n}: nat :=
  match n with
  | 0 => 0
  | S k => sum m (prod k m)
  end.

(* 3.3 *)
Fixpoint pot (n m:nat) {struct m}: nat :=
  match m with
  | 0 => 1
  | S k => prod n (pot n k)
  end.

(* 3.4 *)
Fixpoint leBool (n m:nat): bool :=
  match n , m with
  | 0 , _ => true
  | S k , 0 => false
  | S k, S j => leBool k j
  end.
End Ejercicio3.


(* Ejercicio 4 *)
Section Ejercicio4.

(* 4.1 *)
Fixpoint length (A:Set) (l:list A):nat :=
  match l with
  | nil => 0
  | cons _ l => 1 + length A l
  end.

(* 4.2 *)
Fixpoint append (A:Set) (l1:list A) (l2:list A):list A :=
  match l1, l2 with
  | nil, ll => ll
  | ll, nil => ll
  | cons a ll, lll => cons A a (append A ll lll)
  end.

(* 4.3 *)
Fixpoint reverse (A:Set) (l:list A):list A :=
  match l with
  | nil => nil A
  | cons a ll => append A (reverse A ll) (cons A a (nil A)) 
  end.

(* 4.4 *)
Fixpoint filter (A:Set) (f:A -> bool) (l:list A):list A :=
  match l with
  | nil => nil A
  | cons a l' => if f a then cons A a (filter A f l') else filter A f l'
  end.

(* 4.5 *)
Fixpoint map (A B:Set) (f:A -> B) (l:list A):list B :=
  match l with
  | nil => nil B
  | cons a l' => cons B (f a) (map A B f l')
  end.

(* 4.6 *)
Fixpoint exists_ (A: Set) (f:A -> bool) (l:list A):bool :=
  match l with
  | nil => false
  | cons a l' => if f a then true else exists_ A f l'
  end.
End Ejercicio4.


(* Ejercicio 5 *)
Section Ejercicio5.

(* 5.1 *)
Fixpoint inverse (A:Set) (t:bintree A):bintree A :=
  match t with
  | btree_nil => btree_nil A
  | node t1 a t2 => node A (inverse A t2) a (inverse A t1)
  end.

(* 5.2 *)
Fixpoint nodos_internos (A:Set) (t:Gtree A) :nat :=
  match t with
    empty_gtree => 0
  | node_gtree a f => S (nodos_internos' A f)
  end
with nodos_internos' (A:Set) (f:Forest A):nat :=
  match f with
   empty_forest => 0
  | branch_forest t f' => plus (nodos_internos A t) (nodos_internos' A f')
  end.

Fixpoint nodos_externos (A:Set) (t:Gtree A) :nat :=
  match t with
    empty_gtree => 0
  | node_gtree a f => nodos_externos' A f
  end
with nodos_externos' (A:Set) (f:Forest A):nat :=
  match f with
   empty_forest => 1
  | branch_forest t f' => plus (nodos_externos A t) (nodos_externos' A f')
  end.

(* Está bien? *)
Definition hayMas_nodos_internos (A:Set) (t:Gtree A):bool :=
  Not (leBool (nodos_internos A t) (nodos_externos A t)).

End Ejercicio5.


(* Ejercicio 6 *)
Section Ejercicio6.

(* 6.1 *)
Require Import Coq.Arith.EqNat.
Definition listN := list nat.

Print listN.

(* Puedo importar librerias? Sí *)
Fixpoint member (n:nat) (l:listN):bool :=
  match l with
  | nil => false
  | cons a l' => if beq_nat a n then true else member n l'
  end.

(* 6.2 *)
Fixpoint delete (l:listN) (n:nat):listN :=
  match l with
  | nil => nil nat
  | cons a l' => if beq_nat a n then delete l' n else cons nat a (delete l' n)
  end.

(* 6.3 *)
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

(* Generalización *)
Fixpoint memberG (A:Set) (eqA:A->A->bool) (x:A) (l:list A):bool :=
  match l with
  | nil => false
  | cons a l' => if eqA a x then true else memberG A eqA x l'
  end.

Fixpoint deleteG (A:Set) (eqA:A->A->bool) (l:list A) (x:A):list A :=
  match l with
  | nil => nil A
  | cons y l' => if (eqA x y) then deleteG A eqA l' x else cons A y (deleteG A eqA l' x)
  end.

Fixpoint insertG' (A:Set) (leA:A->A->bool) (x:A) (l:list A):list A :=
  match l with
  | nil => nil A
  | cons a l' => if leA a x then insertG' A leA a l' else cons A x (cons A a l')
  end.

Fixpoint insert_sortG (A:Set) (leA:A->A->bool) (l:list A):list A :=
  match l with
  | nil => nil A
  | cons a l' => insertG' A leA a (insert_sortG A leA l')
  end.

End Ejercicio6.


(* Ejercicio 7 *)
Section Ejercicio7.

(* 7.1 *)
Inductive Exp (A:Set):Set :=
    mas: A -> A -> Exp A
  | producto: A -> A -> Exp A
  | menos_unario: A -> Exp A.

(* 7.2 *)
Definition expNat (e:Exp nat):nat :=
  match e with
  | mas x y => plus x y
  | producto x y => prod x y
  | menos_unario x => x
  end.

(* 7.3 *)
Definition expBool (e:Exp bool):bool :=
  match e with
  | mas x y =>
    match x with
    | true => true
    | _ => x
    end
  | producto x y =>
    match x with
    | false => false
    | _ => y
    end
  | menos_unario x =>
    match x with
    | true => false
    | false => true
    end
  end.

End Ejercicio7.


(* Ejercicio 8 *)
Section Ejercicio8.

(* 8.1 *)
(* Uso induction o case? En este caso son lo mismo *)
Lemma conmutatividadAnd : forall a b:bool, And a b = And b a.
Proof.
  intros x y.
  unfold And.
  case x; case y; reflexivity.
Qed.

Lemma conmutatividadOr : forall a b:bool, Or a b = Or b a.
Proof.
  intros x y.
  unfold Or.
  case x; case y; reflexivity.
Qed.

Lemma asociatidadAnd : forall a b c:bool, And (And a b) c = And a (And b c).
Proof.
  intros x y c.
  unfold And.
  case x; reflexivity.
Qed.

Lemma asociatividadOr : forall a b c:bool, Or (Or a b) c = Or a (Or b c).
Proof.
  intros x y c.
  unfold Or.
  case x; reflexivity.
Qed.

(* 8.2 *)
Lemma LAnd : forall a b : bool, And a b = true <-> a = true /\ b = true.
Proof.
  intros x y.
  unfold iff, And.
  split.
    intro H; split.
      destruct x.
        reflexivity.

        assumption.
      destruct x.
        assumption.
     
        discriminate H.
    intro H; elim H.
    intros H' H''; clear H.
    induction x; assumption.
Qed.

(* 8.3 *)
Lemma LOr1 : forall a b : bool, Or a b = false <-> a = false /\ b = false.
Proof.
  intros x y; unfold iff, Or; split; intro H.
    split; destruct x.
      discriminate H.
    
      reflexivity.

      discriminate H.
  
      assumption.
    elim H; intros H' H''; clear H.
    destruct x.
      discriminate H'.
  
      assumption.
Qed.

(* 8.4 *)
(* Por qué cuando aplico "induction x", tambien modifica las hipotesis que tiene a x?
Por que cuando cambia las expresiones que tienen x en el gol, tambien debería modificar
las expresiones que están en las hipótesis.
 Por qué "case x" NO modifica las hipótesis, pero "destruct x" si lo hace? *)
Lemma LOr2 : forall a b : bool, Or a b = true <-> a = true \/ b = true.
Proof.
  intros x y; unfold iff, Or.
  split; intro H.
    destruct x.
      left; reflexivity.
  
      right; assumption.
    elim H; intro H'; clear H; destruct x.
      reflexivity.

      discriminate H'.

      reflexivity.

      assumption.
Qed.

(* 8.5 *)
Lemma LXor : forall a b : bool, Xor a b = true <-> a <> b.
Proof.
  intros x y; unfold iff, Xor, Not, not; split.
    intros H H'.
    destruct y, x.
        discriminate H.  
        discriminate H'.
        discriminate H'.
        discriminate H.
    intro H.
    destruct y, x.
        elim (H (eq_refl true)).
        reflexivity.
        reflexivity.
        elim (H (eq_refl false)).
Qed.


(* 8.6 *)
Lemma LNot : forall b : bool, Not (Not b) = b.
Proof.
  intro x; unfold Not.
  case x; reflexivity.
Qed.

End Ejercicio8.


(* Ejercicio 9 *)
Section Ejercicio9.

(* 9.1 *)
(* Está bien usar "induction" para probar sobre Fixpoint? Si*)
Lemma SumO : forall n : nat, sum n 0 = n.
Proof.
  intro x.
  induction x.
    simpl.
    reflexivity.

    simpl.
    rewrite -> IHx.
    reflexivity.
Qed.

(* 9.2 *)
Lemma SumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
  intros x y.
  induction x.
    simpl; reflexivity.

    simpl.
    rewrite -> IHx.
    reflexivity.
Qed.

(* 9.3 *)
(* Hay una táctica que sirva como éste lema? Si, apply f_equal. O sino, usar "rewrite". *)
(* No lo uso, se puede BORRAR *)
Lemma aux:forall n m:nat, n=m -> S n = S m.
Proof.
  intros x y H.
  induction x; induction y.
  reflexivity.
  rewrite <- H.
  reflexivity.
  rewrite -> H.
  reflexivity.
  rewrite <- H.
  reflexivity.
Qed.

(* Está bien hacer induction sobre una variable de un para todo? Sí*)
(* Por qué si primero hago intros, y luego doble induccion, el último caso tiene
una hipotesis inductiva con un implica? *)
Lemma SumConm : forall n m : nat, sum n m = sum m n.
Proof.
  induction n.
    induction m.
      simpl; reflexivity.
      simpl; rewrite <- IHm; reflexivity.
    induction m.
      simpl.
      rewrite (IHn 0).
      simpl; reflexivity.

      rename m into m'.
      simpl.
      rewrite <- IHm.
      rewrite (IHn (S m')).
      simpl.
      rewrite (IHn m').
      reflexivity.
Qed.


(* 9.4 *)
Lemma SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
  intros x y z.
  induction x.
    simpl.
    reflexivity.
  
    simpl.
    rewrite -> IHx.
    reflexivity.
Qed.

(* 9.5 *)
Lemma ProdConm : forall n m : nat, prod n m = prod m n.
Proof.
  induction n; induction m.
    reflexivity.

    simpl.
    rewrite <- IHm; simpl; reflexivity.
  
    simpl.
    rewrite (IHn 0).
    simpl; reflexivity.  (* Cuando hago doble inducción, en el último caso tengo "dos m", hace falta que renombre? No. *)

    simpl; rewrite <- IHm.
    rewrite (IHn (S m)).
    simpl.
    rewrite (IHn m).
    rewrite -> (SumAsoc m n (prod m n)).
    rewrite -> (SumAsoc n m (prod m n)).
    rewrite (SumConm n m).
    reflexivity.
Qed.

(* 9.7 *)
(* Puedo hacer éste ejercicio antes del 9.6? Sí *)
Lemma ProdDistr : forall n m p : nat, prod n (sum m p) = sum (prod n m) (prod n p).
Proof.
  induction n.
    intros; simpl; reflexivity.

    intros m' p'; simpl.
    rewrite <- (SumAsoc m' (prod n m') (sum p' (prod n p'))).
    rewrite (SumAsoc (prod n m') p' (prod n p')).
    rewrite (SumConm (prod n m') p').
    rewrite <- (SumAsoc p' (prod n m') (prod n p')).
    rewrite (SumAsoc m' p' (sum (prod n m') (prod n p'))).
    rewrite (IHn m' p').
    reflexivity.
Qed.

(* 9.6 *)
Lemma ProdAsoc : forall n m p : nat, prod n (prod m p) = prod (prod n m) p.
Proof.
  induction n.
    intros; simpl; reflexivity.

    simpl.
    intros m' p'.
    rewrite (IHn m' p').
    rewrite (ProdConm m' p').
    rewrite (ProdConm (prod n m') p').
    rewrite (ProdConm (sum m' (prod n m')) p').
    symmetry; exact(ProdDistr p' m' (prod n m')).
Qed.

End Ejercicio9.


(* Ejercicio 10 *)
Section Ejercicio10.

(* 10.1 *)
Lemma L1 : forall (A : Set) (l : list A), append A l (nil A) = l.
Proof.
  intros; destruct l; simpl; reflexivity.
Qed.

(* 10.2 *)
(* Está bien usar "discriminate"? Sí *)
Lemma L2 : forall (A : Set) (l : list A) (a : A), ~(cons A a l) = nil A.
Proof.
  intros; unfold not; intro H.
  discriminate H.
Qed.

(* 10.3 *)
Lemma L3 : forall (A : Set) (l m : list A) (a : A), cons A a (append A l m) = append A (cons A a l) m.
Proof.
  destruct l; intros; destruct m; simpl; reflexivity.
Qed.

(* 10.4 *)
Lemma L4 : forall (A : Set) (l m : list A),
length A (append A l m) = sum (length A l) (length A m).
Proof.
  induction l; intro m'.
    simpl; reflexivity.

    destruct m'.
      simpl.
      rewrite (SumConm (length A l) 0).
      simpl; reflexivity.
    
      simpl.
      rewrite (IHl (cons A a0 m')).
      simpl; reflexivity.
Qed.

(* 10.5 *)
Lemma L5:forall (A : Set) (l : list A), length A (reverse A l) = length A l.
Proof.
  induction l.
    simpl; reflexivity.

    simpl.
    rewrite <- IHl.
    rewrite (L4 A (reverse A l) (cons A a (nil A))).
    simpl.
    rewrite (SumConm (length A (reverse A l)) 1).
    simpl; reflexivity.
Qed.

(* 11.3 *)
(* Puedo usar éste lema antes? Sí *)
Lemma L9 : forall (A : Set) (l m n : list A),
append A l (append A m n) = append A (append A l m) n.
Proof.
  induction l.
    intros; simpl; reflexivity.

    intros m' n'.
    rewrite <- (L3 A l m' a).
    rewrite <- (L3 A (append A l m') n' a).
    rewrite <- (IHl m' n').
    rewrite -> (L3 A l (append A m' n') a).
    reflexivity.
Qed.

(* 10.6 *)
Lemma L6 : forall (A : Set) (l m : list A),
reverse A (append A l m) = append A (reverse A m) (reverse A l).
Proof.
  induction l.
    intro m'.
    simpl.
    rewrite (L1 A (reverse A m')); reflexivity.

    intro m'; rewrite <- (L3 A l m').
    simpl.
    rewrite (L9 A (reverse A m') (reverse A l) (cons A a (nil A))).
    rewrite (IHl m'); reflexivity.
Qed.

End Ejercicio10.



(* Ejercicio 11  *)
Section Ejercicio11.

(* 11.1 *)
Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B), map A B f (append A l m) = append B (map A B f l) (map A B f m).
Proof.
  induction l.
    simpl; reflexivity.

    intros m' f'.
    destruct m'.
      simpl; reflexivity.

      simpl.
      assert(map A B f' (append A l (cons A a0 m')) = append B (map A B f' l) (map A B f' (cons A a0 m'))); [exact(IHl (cons A a0 m') f') | idtac].
      rewrite H.
      simpl; reflexivity.
Qed.

(* 11.2 *)
Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool),
filter A P (append A l m) = append A (filter A P l) (filter A P m).
Proof.
  induction l.
    intros; simpl; reflexivity.

    intros m' P'.
    rewrite <- (L3 A l m' a).
    simpl.
    destruct (P' a).
      rewrite <- (L3 A (filter A P' l) (filter A P' m')).
      rewrite (IHl m' P'); reflexivity.

      rewrite (IHl m' P'); reflexivity.
Qed.

(* 11.3, está echo en la sección Ejercicio10 *)

(* 11.4 *)
Lemma L10 : forall (A : Set) (l : list A), reverse A (reverse A l) = l.
Proof.
  induction l.
    simpl; reflexivity.

    simpl.
    rewrite (L6 A (reverse A l) (cons A a (nil A))).
    rewrite IHl.
    simpl reverse.
    rewrite <- (L3 A (nil A) l a).
    simpl; reflexivity.
Qed.

End Ejercicio11.


(* Ejercicio 12 *)
Section Ejercicio12.

Fixpoint filterMap (A B : Set) (P : B -> bool) (f : A -> B) (l : list A) {struct l} : list B :=
  match l with
  | nil => nil B
  | cons a l1 =>
    match P (f a) with
    | true => cons B (f a) (filterMap A B P f l1)
    | false => filterMap A B P f l1
    end
  end.

Lemma FusionFilterMap : forall (A B : Set) (P : B -> bool) (f : A -> B) (l : list A),
  filter B P (map A B f l) = filterMap A B P f l.
Proof.
  induction l.
    simpl; reflexivity.

    simpl.
    destruct (P (f a)); rewrite IHl; reflexivity.
Qed.

End Ejercicio12.

(* Ejercicio 13 *)
Section Ejercicio13.

(* Puedo interpretar a éste lema como: inverse cumple su especificación? Si *)
Lemma arbol_espejo : forall (A:Set) (b:bintree A), mirror A (inverse A b) b.
Proof.
  induction b.
    simpl.
    exact (mirror0 A).

    simpl.
    exact(mirrorS A (inverse A b2) (inverse A b1) b1 b2 a a (eq_refl a) IHb2 IHb1).
Qed.

End Ejercicio13.


(* Ejercicio 14 *)
Section Ejercicio14.

(* 14.1 *)
Definition arbol_id (A:Set) (b:bintree A):bintree A := b.

Lemma arbol_id_isomorfo : forall (A:Set) (b:bintree A), isomorfismo A (arbol_id A b) b.
Proof.
  induction b.
    unfold arbol_id.
    exact (isomorfismo0 A).

    unfold arbol_id.
    exact (isomorfismoS A b1 b2 b1 b2 a a IHb1 IHb2).
Qed.

(* 14.2 *)
Lemma isomorfismo_reflexividad : forall (A:Set) (b:bintree A), isomorfismo A b b.
Proof.
  induction b.
    exact (isomorfismo0 A).

    exact(isomorfismoS A b1 b2 b1 b2 a a IHb1 IHb2).
Qed.

Lemma ismorfismo_simetria : forall (A:Set) (b b':bintree A), isomorfismo A b b' -> isomorfismo A b' b.
Proof.
  intros.
  induction H.
  (* Si tuviese (node ..) en lugar de b', está bien aplicar induction H, y que (node ..) se pise?
     Si no lo necesito esta bien. Para preservar el (node ..), hago una nueva hipotesis: b'' = node .., y
     hago induccion sobre " isomorfismo A b b'' ", dejando el isomorfismo lo mas generico posible.*)
    exact (isomorfismo0 A).

    exact (isomorfismoS A t1' t2' t1 t2 b a IHisomorfismo1 IHisomorfismo2).
Qed.

End Ejercicio14.


(* Ejercicio 15 *)
Section Ejercicio15.

Inductive Tree (A:Set):Set :=
    leaf : A -> Tree A
  | tnode : Tree A -> Tree A -> Tree A.


(* 15.1 *)
Fixpoint mapTree (A B:Set) (t:Tree A) (f:A->B) {struct t}:Tree B :=
  match t with
  | leaf x => leaf B (f x)
  | tnode t1 t2 => tnode B (mapTree A B t1 f) (mapTree A B t2 f)
  end.

(* 15.2 *)
Fixpoint num_hojas (A:Set) (t:Tree A) {struct t}:nat :=
  match t with
  | leaf x => 1
  | tnode t1 t2 => sum (num_hojas A t1) (num_hojas A t2)
  end.

(* 15.3 *)
Lemma ej15_3 : forall (A B:Set) (f:A->B) (t:Tree A), num_hojas A t = num_hojas B (mapTree A B t f).
Proof.
  induction t.
    simpl; reflexivity.

    simpl.
    rewrite <- IHt1, IHt2; reflexivity.
Qed.

(* 15.4 *)
Fixpoint hojas (A:Set) (t:Tree A):list A :=
  match t with
  | leaf x => cons A x (nil A)
  | tnode t1 t2 => append A (hojas A t1) (hojas A t2)
  end.

Lemma ej15_4 : forall (A:Set) (t:Tree A), num_hojas A t = length A (hojas A t).
Proof.
  induction t.
    simpl; reflexivity.

    simpl.
    rewrite (L4 A (hojas A t1) (hojas A t2)).
    rewrite <- IHt1, IHt2; reflexivity.
Qed.

End Ejercicio15.

Section Ejercicio16.

(* 16.1 *)
(* posfijo l1 l2 <-> l1 es un posfijo de l2 *)
Inductive posfijo (A:Set):list A -> list A -> Prop :=
    posfijoB : forall (l :list A), posfijo A l l
  | posfijoC : forall (l1 l2:list A) (a:A), posfijo A l1 l2 -> posfijo A l1 (cons A a l2).

(* 16.2 *)
Lemma ej16_2a : forall (A:Set) (l1 l2 l3:list A), l2 = append A l3 l1 -> posfijo A l1 l2.
Proof.
  induction l2.
    intros; simpl.
    destruct l1.
      exact (posfijoB A (nil A)).
      destruct l3.
        simpl in H; discriminate H.
        rewrite <- (L3 A l3 (cons A a l1) a0) in H; discriminate H.

   intros l3' H.
   destruct l3'.
     simpl in H; rewrite H; exact (posfijoB A l1).
     rewrite <- (L3 A l3' l1 a0) in H.
     injection H; intros; clear H.
     exact (posfijoC A l1 l2 a ((IHl2 l3') H0)).
Qed.

(* En ésta forma se hace induccion sobre l3, pero antes de hacer induccion se reescribe l2 y se borra la igualdad *)
Lemma ej16_2a' : forall (A:Set) (l1 l2 l3:list A), l2 = append A l3 l1 -> posfijo A l1 l2.
Proof.
  intros.
  rewrite H; clear H.
  induction l3.
    simpl; exact (posfijoB A l1).

    rewrite <- (L3 A l3 l1 a).
    apply (posfijoC A l1 (append A l3 l1)).
    assumption.
Qed.


Lemma ej16_2b : forall (A:Set) (l1 l2:list A), posfijo A l1 l2 -> exists (l3:list A), l2 = append A l3 l1.
Proof.
  intros.
  induction H.
    exists (nil A).
    simpl; reflexivity.

    elim IHposfijo; intros; clear IHposfijo.
    exists (cons A a x).
    rewrite <- (L3 A x l1).
    (* otra forma seria hacer: rewrite H0 *)
    apply f_equal. (* puedo usar f_equal? Si*)
    assumption.
Qed.

(* 16.3 *)
Fixpoint ultimo (A:Set) (l:list A):list A :=
  match l with
  | nil => nil A
  | cons x nil => cons A x (nil A)
  | cons x l'' => ultimo A l''  (* está bien? Si *)
  end.

(* 16.4 *)
Lemma ej16_4aux : forall (A:Set) (l:list A) (a a':A), ultimo A (cons A a (cons A a' l)) = ultimo A (cons A a' l).
Proof.
  intros; simpl; reflexivity.
Qed.

Lemma ej16_4 : forall (A:Set) (l:list A), posfijo A (ultimo A l) l.
Proof.
  induction l.
    simpl.
    exact (posfijoB A (nil A)).

    destruct l.
      simpl.
      exact (posfijoB A (cons A a (nil A))).
      rewrite (ej16_4aux A l a a0).
      exact ((posfijoC A (ultimo A (cons A a0 l)) (cons A a0 l) a) IHl).
Qed.

End Ejercicio16.


(* Ejercicio 17 *)
Section Ejercicio17.

(* 17.1 *)
(* Es un arbol completo, pues las hojas siempre tienen un elemento *)
Inductive ABin (A B:Set):Set :=
  | ABLeaf : B -> ABin A B
  | ABCons : forall (_:A) (ab1 ab2:ABin A B), ABin A B.

(* 17.2 *)
Fixpoint ABhojas (A B:Set) (ab:ABin A B) {struct ab}:nat :=
  match ab with
  | ABLeaf _ => 1
  | ABCons _ ab1 ab2 => sum (ABhojas A B ab1) (ABhojas A B ab2)
  end.

(* 17.3 *)
Fixpoint ABnodos (A B:Set) (ab:ABin A B) {struct ab}:nat :=
  match ab with
  | ABLeaf _ => 0
  | ABCons _ ab1 ab2 => S (sum (ABnodos A B ab1) (ABnodos A B ab2))
  end.

(* 17.4 *)
Lemma ej17_4 : forall (A B:Set) (ab:ABin A B), ABhojas A B ab = S (ABnodos A B ab).
Proof.
  induction ab.
    simpl; reflexivity.

    simpl.
    rewrite IHab1, IHab2; simpl.
    rewrite -> (SumConm (ABnodos A B ab1) (S (ABnodos A B ab2))); simpl.
    rewrite -> (SumConm (ABnodos A B ab2) (ABnodos A B ab1)); reflexivity.
Qed.

End Ejercicio17.



(* Ejercicio 18 *)
Section Ej_18.

Variable A : Set.

Inductive Tree_ : Set :=
  | nullT : Tree_
  | consT : A -> Tree_ -> Tree_ -> Tree_.

(* 18.1 *)
(* Por que si uso un \/, el principio de inducción sale mal?
Es conveniente NO hacer definiciones inductivas que tengan \/. *)
Inductive isSubTree : Tree_ -> Tree_ -> Prop :=
  | sb_iguales : forall (t:Tree_), isSubTree t t
  | sb_izq : forall (t t1 t2:Tree_ ) (a:A), isSubTree t t1 -> isSubTree t (consT a t1 t2)
  | sb_der : forall (t t1 t2:Tree_ ) (a:A), isSubTree t t2 -> isSubTree t (consT a t1 t2).

(* 18.2 *)
Lemma isSubTree_ref : forall (t:Tree_), isSubTree t t.
Proof.
  exact (sb_iguales).
Qed.

(* 18.3 *)
Lemma isSubTree_tran : forall (t1 t2 t3:Tree_), isSubTree t1 t2 /\ isSubTree t2 t3 -> isSubTree t1 t3.
Proof.
  intros.
  elim H; intros; clear H.
  Print isSubTree_ind.
  induction H1.
    assumption.
    apply (sb_izq t1 t0 t2 a); exact (IHisSubTree H0).
    apply (sb_der t1 t0 t2 a); exact (IHisSubTree H0).
Qed.

End Ej_18.


(* Ejercicio 19 *)
Section Ejercicio19.

(* 19.1 *)
Inductive ACom (A:Set): nat -> Set :=
  | AComB : A -> ACom A 0
  | AComI : forall (n :nat) (_:A) (ac1 ac2:ACom A n), ACom A (S n).
 
(* 19.2 *)
Fixpoint h (A:Set) (n:nat) (ac:ACom A n) {struct ac}:nat :=
  match ac with
  | AComB _ => 1
  | AComI n _ _ _ => sum (pot 2 n) (pot 2 n)  (* está bien el match? si *)
  end.

(* 19.3 *)
(* Parameter pot: nat -> nat -> nat. *)
Axiom potO : forall n : nat, pot (S n) 0 = 1.
Axiom potS : forall m: nat, pot 2 (S m) = sum (pot 2 m) (pot 2 m).

Lemma ej19_3 : forall (A:Set) (n:nat) (ac:ACom A n), h A n ac = pot 2 n.
Proof.
  intros.
  induction ac.
    simpl h; rewrite (potO 1); reflexivity.
    Check ACom_ind.
    simpl h; rewrite (potS n).
    reflexivity.
Qed.

End Ejercicio19.


(* Ejercicio 20 *)
Section Ejercicio20.

(* 20.1 *)
Inductive AB (A:Set):nat->Set :=
    ABNil : AB A 0
  | ABC : forall (n m:nat) (_:A) (t1:AB A n) (t2:AB A m), AB A (S (max n m)).

(* 20.2 *)
(* Por qué tengo que usar gt_dec, en el if then else? *)
Require Import Coq.Arith.Compare_dec.

Fixpoint camino (A:Set) (n:nat) (ab:AB A n):list A :=
  match ab with
  | ABNil => nil A
  | ABC n m x t1 t2 => if gt_dec m n then cons A x (camino A m t2) else cons A x (camino A n t1)
  end.

(* 20.3 *)
Require Import Coq.Arith.Lt.

Lemma ej20_3 : forall (A:Set) (n:nat) (ab:AB A n), length A (camino A n ab) = n.
Proof.
  induction ab.
    simpl; reflexivity.

    simpl.
      destruct (gt_dec m n).
        simpl.
        rewrite IHab2.
        rewrite (max_r n m (lt_le_weak n m g)).
        reflexivity.

        simpl.
        rewrite IHab1.
        rewrite (max_l n m (not_gt m n n0)).
        reflexivity.
Qed.

End Ejercicio20.
