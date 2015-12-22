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
Variable context : context.

Check context.(ctxt_vadd_accessible).
Require Import Coq.Bool.Bool.

(* NO lo puedo poner en Actions.v*)
Notation "'App' c1 '[' c2 ']' c3" :=                                                                                 
      (app c1 c2 c3)(at level 200).

Definition isPage (va:vadd) (ma:madd) (p:option page):Prop :=
  option_elim p
    (fun (p:page) => exists (pt:vadd->option madd), p.(page_content) = PT pt
              /\ App pt [va] (fun (m:madd) => m=ma))
    False.

Definition va_mapped_to_ma (s:state) (va:vadd) (ma:madd):Prop :=
   isPage va ma (option_app s.(memory)
     (option_appD (s.(hypervisor) s.(active_os))
       (option_map (fun (s:os) => s.(curr_page)) (s.(oss) s.(active_os))))).

(* La dir. de máquina deberia tener un valor de escritura/lectura? *)
Definition isRW (s:state) (ma:madd):Prop :=
  App s.(memory) [ma] (fun (p:page) =>
    exists ov:option value, p.(page_content) = RW ov
                    /\ option_elim ov (fun (_:value)=> True) False).

(* Como es la precedencia del exits? *)
Definition Pre (s:state) (a:Action):Prop :=
  match a with
  | Read v => context.(ctxt_vadd_accessible) v = true
              /\ s.(aos_activity) = running
              /\ exists ma:madd, va_mapped_to_ma s v ma
                /\ isRW s ma
  | Write v _ =>  context.(ctxt_vadd_accessible) v = true
                  /\ s.(aos_activity) = running
                  /\ exists ma:madd, va_mapped_to_ma s v ma
                    /\ isRW s ma

  | Chmod =>  s.(aos_activity) = waiting
              /\  App s.(oss) [s.(active_os)] (fun (s:os)=>s.(hcall)=None)
  end.

Check Is_true.


Definition Post (s:state) (a:Action) (s':state):Prop  :=
  match a with
  | Read x => s=s'
  | Write v x => exists ma:madd,  va_mapped_to_ma s v ma
                                  /\ s'.(memory) = option_update s.(memory) madd_eq ma (Page (RW (Some x)) (OS s.(active_os)))
                                  /\ s'.(active_os) = s.(active_os)
                                  /\ s'.(aos_exec_mode) = s.(aos_exec_mode)
                                  /\ s'.(aos_activity) = s.(aos_activity)
                                  /\ s'.(oss) = s.(oss)
                                  /\ s'.(hypervisor)=s.(hypervisor)
  | Chmod =>  (context.(ctxt_oss) s.(active_os) = true
                /\ s'.(aos_exec_mode) = svc
                /\ s'.(aos_activity) = running
                /\ s'.(memory) = s.(memory)
                /\ s'.(active_os) = s.(active_os)
                /\ s'.(oss) = s.(oss)
                /\ s'.(hypervisor) = s.(hypervisor))
              \/  (context.(ctxt_oss) s.(active_os) = false
                /\ s'.(aos_exec_mode) = usr
                /\ s'.(aos_activity) = running
                /\ s'.(memory) = s.(memory)
                /\ s'.(active_os) = s.(active_os)
                /\ s'.(oss) = s.(oss)
                /\ s'.(hypervisor) = s.(hypervisor))
  end. 


(* Ejercicio 4 *)

Definition prop3 (s:state):Prop :=
  (s.(aos_activity)=running -> context.(ctxt_oss) s.(active_os) = true -> s.(aos_exec_mode) = svc)
  \/ s.(aos_activity) = waiting.

Definition prop5 (s:state):Prop :=
  (forall (os:os_ident) (pa:padd),
    App s.(hypervisor) [os] (fun f:padd->option madd =>
      App f [pa] (fun ma:madd =>
        App s.(memory) [ma] (fun p:page => p.(page_owned_by) = OS os))))
  /\ (forall (os:os_ident) (pa1 pa2:padd),
        App s.(hypervisor) [os] (fun f:padd->option madd =>
          ~(f pa1 = None)
          /\ f pa1 = f pa2 -> pa1 = pa2)).

Definition prop6 (s:state):Prop :=
  forall (osi:os_ident),
    App s.(oss) [osi] (fun os_info:os=>
      App s.(hypervisor) [osi] (fun f:padd->option madd =>
        App f [os_info.(curr_page)] (fun ma:madd =>
          App s.(memory) [ma] (fun p:page =>
            exists pt:vadd->option madd, p.(page_content) = PT pt
            /\ forall va:vadd,
                App pt [va] (fun ma':madd =>
                  App s.(memory) [ma'] (fun p':page =>
                    (context.(ctxt_vadd_accessible) va = true -> p'.(page_owned_by) = OS osi)
                    /\ (context.(ctxt_vadd_accessible) va = false -> p'.(page_owned_by) = Hyp))))))).

Definition valid_state (s:state):Prop :=
  prop3 s /\ prop5 s /\ prop6 s.


(* Ejercicio 5 *)

(* Es mejor usar Definition? *)
Inductive one_step_exec (s:state) (a:Action) (s':state) : Prop :=
  | Exec : valid_state(s) -> Pre s a -> Post s a s' -> one_step_exec s a s'.


(* Ejercicio 6 *)
Theorem ej6 : forall (s s':state) (a:Action), one_step_exec s a s' -> prop3 s'.
Proof.
  intros.
  induction H.
  unfold valid_state in H.
  elim H; intros; clear H.
  clear H3.
  induction a.
    unfold Post in H1.
    rewrite <- H1; assumption.

    unfold Post in H1.
    elim H1; intros; clear H1.
    unfold prop3 in *.
    elim H; intros.
    elim H3; intros.
    elim H5;intros.
    elim H7;intros.
    elim H9;intros.
    rewrite H10, H6, H8.
    assumption.

    unfold Post in H1.
    destruct (ctxt_oss context (active_os s)).
      elim H1; intros.
      unfold prop3 in *.
Qed.




















