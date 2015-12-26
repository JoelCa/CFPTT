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

(* Nose si está bien. *)
Definition prop3 (s:state):Prop :=
  (s.(aos_activity)=running -> context.(ctxt_oss) s.(active_os) = true -> s.(aos_exec_mode) = svc).

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
    elim H; intros.
    elim H3; intros.
    elim H5;intros.
    elim H7;intros.
    elim H9;intros.
    unfold prop3 in *.
    rewrite H10, H6, H8.
    assumption.

    unfold Post in H1.
      elim H1; intros.
        elim H; intros.
        elim H4; intros.
        unfold prop3; intros.
        assumption.

        elim H; intros.
        elim H4; intros.
        elim H6; intros.
        elim H8; intros.
        elim H10; intros.
        unfold prop3.
        intros.
        rewrite H11 in H14.
        rewrite H3 in H14.
        discriminate H14.
Qed.


(* Ejercicio 7 *)
Theorem ej7 : forall (s s':state) (va:vadd), one_step_exec s (Read va) s' ->
  exists (ma:madd), va_mapped_to_ma s va ma
  /\ App s.(memory) [ma] (fun p:page =>
    p.(page_owned_by) = OS s.(active_os)).
Proof.
  intros.
  induction H.
  unfold Pre in H0.
  elim H0; intros.
  elim H3; intros.
  elim H5; intros.
  clear H0; clear H3; clear H5.
  elim H6; intros; clear H6.
  exists x; split.
    assumption.

    unfold va_mapped_to_ma in H0.
    unfold option_map in H0.
    case_eq (oss s (active_os s)); intros.
    rewrite H5 in H0.
      unfold option_appD in H0.
      case_eq (hypervisor s (active_os s)); intros.
      rewrite H6 in H0.
      unfold option_app in H0.
      unfold option_elim in H0.
      case_eq (m (curr_page o)); intros.
      rewrite H7 in H0.
      unfold isPage in H0.
      case_eq (memory s m0); intros.
      unfold option_elim in H0.
      rewrite H8 in H0.
      elim H0; intros.
      elim H9; intros; clear H9.
      case_eq (x0 va); intros.
      unfold app, option_elim in H11.
      rewrite H9 in H11.
      clear H0.
      unfold valid_state in H.
      elim H; intros.
      elim H12; intros.
      clear H12; clear H.
      unfold prop6 in H14.
      assert (App oss s [active_os s]
      (fun os_info : os =>
       App hypervisor s [active_os s]
       (fun f : padd -> option madd =>
        App f [curr_page os_info]
        (fun ma : madd =>
         App memory s [ma]
         (fun p : page =>
          exists pt : vadd -> option madd,
            page_content p = PT pt /\
            (forall va : vadd,
             App pt [va]
             (fun ma' : madd =>
              App memory s [ma']
              (fun p' : page =>
               (ctxt_vadd_accessible context va = true ->
                page_owned_by p' = OS (active_os s)) /\
               (ctxt_vadd_accessible context va = false ->
                page_owned_by p' = Hyp))))))))).
      apply (H14 (active_os s)).
      clear H14.
      unfold app in H.
      rewrite H5, H6 in H.
      unfold option_rect in H.
      rewrite H7, H8 in H.
      elim H; intros; clear H.
      elim H12; intros; clear H12.
      rewrite H10 in H.
      injection H; intro.
      assert (match x1 va with
      | Some a =>
          match memory s a with
          | Some a0 =>
              (ctxt_vadd_accessible context va = true ->
               page_owned_by a0 = OS (active_os s)) /\
              (ctxt_vadd_accessible context va = false ->
               page_owned_by a0 = Hyp)
          | None => False
          end
      | None => False
      end).
      apply (H14 va).
      clear H14.
      rewrite H12 in H9.
      rewrite H9 in H15.
      case_eq (memory s m1); intros.
      rewrite H14 in H15.
      elim H15; intros.
      assert (page_owned_by p0 = OS (active_os s)).
      exact (H16 H2).
      clear H15; clear H16; clear H17.
      unfold app.
      rewrite <- H11, H14.
      simpl; assumption.

      rewrite H14 in H15.
      elim H15.

      unfold app in H11.
      rewrite H9 in H11; simpl in H11; elim H11.

      rewrite H8 in H0.
      simpl in H0; elim H0.

      rewrite H7 in H0.
      simpl in H0; elim H0.

      rewrite H6 in H0.
      unfold option_app, option_elim in H0.
      simpl in H0; elim H0.

      rewrite H5 in H0.
      unfold option_appD, option_app, option_elim in H0.
      destruct (hypervisor s (active_os s)); (simpl in H0; elim H0).
Qed.