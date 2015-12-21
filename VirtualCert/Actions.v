(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Require Export State.

Require Export Maps.

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

Check id.

Definition isPage (va:vadd) (ma:madd) (p:option page):Prop :=
  option_elim p
    (fun (p:page) => exists (pt:vadd->option madd), p.(page_content) = PT pt
              /\ option_elim (pt va) (fun (m:madd) => m=ma) False)
    False.

Definition va_mapped_to_ma (s:state) (va:vadd) (ma:madd):Prop :=
  isPage va ma (option_app s.(memory)
    (option_appD (s.(hypervisor) s.(active_os))
      (option_map (fun (s:os) => s.(curr_page)) (s.(oss) s.(active_os))))).

(* la dir. de máquina deberia tener un valor de escritura/lectura? *)
Definition isRW (s:state) (ma:madd):Prop :=
  option_elim (s.(memory) ma) (fun (p:page) =>
    exists ov:option value, p.(page_content) = RW ov
                    /\ option_elim ov (fun (_:value)=> True) False
    ) False.

(* TERMINAR *)
Definition Pre (s:state) (a:Action):Prop :=
  match a with
  | Read v => Is_true (context.(ctxt_vadd_accessible) v)
              /\ s.(aos_activity) = running
              /\ exists ma:madd, va_mapped_to_ma s v ma
  | Write v _ =>  Is_true (context.(ctxt_vadd_accessible) v)
                  /\ s.(aos_activity) = running
                  /\ exists ma:madd, va_mapped_to_ma s v ma
                    /\ isRW s ma

  | _ => False
  end.

(*TERMINAR*)
Definition Post (s:state) (a:Action) (s':state):Prop  :=
  match a with
  | Read x => s=s'
  | Write v x => exists ma:madd,  va_mapped_to_ma s v ma
                                  /\ s'.(memory) = option_update s.(memory) madd_eq ma (Page (RW (Some x)) (OS s.(active_os)))
  | _ => False 
  end. 

