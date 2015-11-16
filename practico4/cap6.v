Section TiposInductivos.

(* Libro *)
Inductive mes : Set :=
    | enero | febrero | marzo | abril | mayo | junio 
    | julio | agosto | septiembre | octubre | noviembre | diciembre. 

Print mes_rec.
Check mes_rect.
Print mes_ind.

(*Theorem mes_equal:
forall m:mes,m=enero \/ m=febrero \/ m=marzo \/ m = mayo \/ m=junio
\/ m=julio \/ m=agosto \/ m=septiembre \/ m=octubre \/ m=noviembre
\/ m=diciembre.
Proof.
 intro m.
 .
 induction m.
Qed.*)

Definition duracion (bisiesto: bool): mes -> nat
:=
   mes_rec (fun m: mes => nat)
       28 31 (if bisiesto then 29 else 28) 31 31 30 31 31 30 31 30 31.
Check le.
Print le.
Check le_n.
Check le_S.

Definition duracion' (b: bool)(m: mes) :=
  match m with 
  | enero => 31 | febrero => if b then 29 else 28 | marzo => 31
  | abril => 30 | mayo => 31 | junio => 30 | julio => 31
  | agosto => 31 | septiembre => 30 | octubre => 31
  | noviembre => 30 | _ => 34
  end.

Definition duracion'' (b: bool)(m: mes) :=
  match m with 
  | febrero => if b then 29 else 28 
  | abril => 30 | junio => 30 |   septiembre => 30
  | noviembre => 30 
  | _ => 31 
  end.

Check duracion.
Eval compute in  (duracion'' true ). 
Eval compute in  (duracion'' false marzo). 

(****************  *********************)
Inductive estacion: Set := 
  | verano | otonio | invierno | primavera.

Definition ej61: mes -> estacion :=
  mes_rec (fun m: mes => estacion)
         verano verano verano otonio otonio otonio 
         invierno invierno invierno primavera primavera primavera.

Eval compute in (ej61 abril).



Definition prueba :=
   mes_rec (fun m: mes => match m with 
   | enero => nat | febrero => bool | marzo => mes | _ => nat end)
   53 true abril 4 5 6 7 8 9 10 11 12.
                   
 
Eval compute in (prueba enero).
Check (prueba enero).
Check (prueba enero):nat.
Eval compute in (prueba febrero).
Eval compute in (prueba marzo).
Eval compute in (prueba diciembre).

Print mes_rec.
Print mes_ind.
Print mes_rect.

Eval compute in (nat_rec (fun n:nat => nat)).

Check bool_ind.
Check bool_rec.

(*******************  *****************)
Print or_introl.
(*Require Import Coq.Init.Logic.
Print eq_refl.

Theorem bool_equal: forall b: bool, b = true \/ b = false.
Proof (bool_ind 
                       (fun b: bool => b = true \/ b = false)
                       (or_introl (true= false) (refl_equal true)) 
                       (or_intror (false = true) (refl_equal false))
          ).

Theorem bool_equal': forall b: bool, b = true \/ b = false.
Proof.
  intro b.  pattern b.
  Print bool_ind.
  apply bool_ind.
  left; reflexivity.
  right; reflexivity.
Qed.

Print or.
Check or_ind.
Check and_ind.



(* Discriminate: Elementos obtenidos con constructores distintos
   son diferentes *)
Lemma Disc : enero <> febrero.
Proof.
  unfold not; intro eqEF.
  discriminate eqEF.
Qed.

Lemma sin_discriminate : enero <> febrero.
Proof.
  unfold not; intro eqEF.
  change 
   ((fun m: mes => match m with enero => True | _ => False end) febrero).
  rewrite <- eqEF.
  trivial.
Qed.
*)

(* Se puede hacer a mano, si se prueba: *)
Axiom ll:~exists n:nat, n = 0 /\ (exists m:nat, n=S m).

Theorem aa:~forall m:nat,(exists p:nat, m = S p)->m=0.
Proof.
  unfold not; intro H.
  assert(exists p : nat, 1 = S p).
  exists 0;reflexivity.
  assert(1=0);[exact(H 1 H0)|idtac].
  assert(exists p : nat, 0 = S p).
  exists 0;symmetry;assumption.
  assert(0=0);[exact(H 0 H2)|idtac].
  apply ll;exists 0;split;assumption.
Qed.
Lemma disc_nat: forall n: nat, 0 <> S n.
Proof.
  unfold not; intros n Heq.
  change ((fun m: nat => match m with 0 => True | S p => False end) (S n)).
  rewrite <- Heq.
  trivial.
Qed.

Lemma L : forall n : nat, n = 0 <-> ~ exists y : nat, n = (S y).

Proof.
  intros.
  split.
  intros H H1.
  elim H1; intros y H2.
  rewrite H in H2.
  apply (disc_nat y H2).
  
  intros.  

(* Ejercicio: prueba amano discriminate para naturales *)
Definition f := (fun m: nat => match m with 0 => True | S p => False end). 




(**************** Injectividad de constructores ***************)
Variable A B : Set.
Inductive Either: Set :=
  Left : A -> Either | Right : B -> Either.

Lemma inj: forall (x y: A), Left x = Left y -> x = y.
Proof.
  intros x y H.
  injection H.
  intro.
  assumption.
Qed.

Lemma inj_a_mano: forall (x y: A), Left x = Left y -> x = y.
Proof.
  intros x y eq.
  change (let f := (fun v: Either => match v with Left a => a | Right  b => y end) 
                    in f (Left x) = f (Left y)).
  rewrite eq. 
  simpl.
  trivial.
Qed.

(* Ejercicio: Probar "a mano" la inyectividad de los constructores
    de nat *)
Lemma nat_inj : forall (n m: nat), S m = S n -> m = n.
Proof.
  intros n m H.
  change (let f := fun k: nat => match k with 0 => 0 | S p => p end
                 in f (S m) = f (S n)
  ).
  rewrite H.
  simpl.
  trivial.
Qed.
