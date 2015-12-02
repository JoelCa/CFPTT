(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Require Export State.

(* Ejercicio 2 *)
Inductive Action : Set :=
  | Read : vadd -> Action
  | Write : vadd -> value -> Action
  | Chmod : Action.

(* Ejercicio 3 *)
Print  ctxt_vadd_accessible.

Variable context : context.

Check context.(ctxt_vadd_accessible).
Require Import Coq.Bool.Bool.
Check true && false.

(* Está bien? *)
Parameter va_mapped_to_ma : state -> vadd -> madd -> bool.

(* TERMINAR *)
Definition Pre (s:state) (a:Action):Prop :=
  match a with
  | Read x => Is_true (context.(ctxt_vadd_accessible) x)
              /\ s.(aos_activity) = running
              /\ exists ma:madd, Is_true (va_mapped_to_ma s x ma)
  | _ => False
  end.
   

