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

Definition va_mapped_to_ma (s:state) (va:vadd) (ma:madd):Prop :=
  App (oss s) [active_os s] (fun os_info:os =>
    App (hypervisor s) [active_os s] (fun f:mapping padd madd =>
      App f [curr_page os_info] (fun ma':madd =>
        App (memory s) [ma'] (fun p:page =>
          exists (pt:mapping vadd madd), page_content p = PT pt
            /\ App pt [va] (fun (m:madd) => m=ma))))).

(* La dir. de máquina deberia tener un valor de escritura/lectura? *)
Definition isRW (s:state) (ma:madd):Prop :=
  App (memory s) [ma] (fun (p:page) =>
    exists ov:value, (page_content p) = RW (Some ov)).

(* Como es la precedencia del exits? *)
Definition Pre (s:state) (a:Action):Prop :=
  match a with
  | Read v => ctxt_vadd_accessible context v = true
              /\ aos_activity s = running
              /\ exists ma:madd, va_mapped_to_ma s v ma
                /\ isRW s ma
  | Write v _ =>  ctxt_vadd_accessible context v = true
                  /\ aos_activity s = running
                  /\ exists ma:madd, va_mapped_to_ma s v ma
                    /\ isRW s ma

  | Chmod =>  aos_activity s = waiting
              /\  App (oss s) [active_os s] (fun (s:os)=> hcall s = None)
  end.

Definition Post (s:state) (a:Action) (s':state):Prop  :=
  match a with
  | Read x => s = s'
  | Write v x => exists ma:madd,  va_mapped_to_ma s v ma
                                  /\ memory s' = option_update (memory s) madd_eq ma (Page (RW (Some x)) (OS s.(active_os)))
                                  /\ active_os s' = active_os s
                                  /\ aos_exec_mode s' = aos_exec_mode s
                                  /\ aos_activity s' = aos_activity s
                                  /\ oss s' = oss s
                                  /\ hypervisor s'= hypervisor s
  | Chmod =>  (ctxt_oss context (active_os s) = true
                /\ aos_exec_mode s' = svc
                /\ aos_activity s' = running
                /\ memory s' = memory s
                /\ active_os s' = active_os s
                /\ oss s' = oss s
                /\ hypervisor s' = hypervisor s)
              \/  (ctxt_oss context (active_os s) = false
                /\ aos_exec_mode s' = usr
                /\ aos_activity s' = running
                /\ memory s' = memory s
                /\ active_os s' = active_os s
                /\ oss s' = oss s
                /\ hypervisor s' = hypervisor s)
  end. 


(* Ejercicio 4 *)

(* Nose si está bien. *)
Definition prop3 (s:state):Prop :=
  aos_activity s = running -> ctxt_oss context (active_os s) = true -> aos_exec_mode s = svc.

Definition prop5 (s:state):Prop :=
  (forall (os:os_ident) (pa:padd),
    App (hypervisor s) [os] (fun f:padd->option madd =>
      App f [pa] (fun ma:madd =>
        App (memory s) [ma] (fun p:page => page_owned_by p = OS os))))
  /\ (forall (os:os_ident) (pa1 pa2:padd),
        App (hypervisor s) [os] (fun f:padd->option madd =>
          ~(f pa1 = None)
          /\ f pa1 = f pa2 -> pa1 = pa2)).

Definition prop6 (s:state):Prop :=
  forall (osi:os_ident),
    App (oss s) [osi] (fun os_info:os=>
      App (hypervisor s) [osi] (fun f:padd->option madd =>
        App f [curr_page os_info] (fun ma:madd =>
          App (memory s) [ma] (fun p:page =>
            exists pt:vadd->option madd, page_content p = PT pt
            /\ forall va:vadd,
                App pt [va] (fun ma':madd =>
                  App (memory s) [ma'] (fun p':page =>
                    (ctxt_vadd_accessible context va = true -> page_owned_by p' = OS osi)
                    /\ (ctxt_vadd_accessible context va = false -> page_owned_by p' = Hyp))))))).

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
  /\ App (memory s) [ma] (fun p:page =>
    page_owned_by p = OS (active_os s)).
Proof.
  intros.
  destruct H.
  unfold Pre in H0.
  elim H0; intros.
  elim H3; intros.
  elim H5; intros.
  elim H6; intros.
  clear H0; clear H3; clear H5; clear H6.
  exists x; split.
    assumption.

    unfold va_mapped_to_ma in H7.
    unfold app in H7.
    case_eq (oss s (active_os s)); intros.
      rewrite H0 in H7; simpl in H7.
      case_eq (hypervisor s (active_os s)); intros.
        rewrite H3 in H7; simpl in H7.
        case_eq (m (curr_page o)); intros.
          rewrite H5 in H7; simpl in H7.
          case_eq (memory s m0); intros.
            rewrite H6 in H7; simpl in H7.
            elim H7; intros.
            elim H9; intros.
            clear H7; clear H9.
            case_eq (x0 va); intros.
              rewrite H7 in H11; simpl in H11.
              unfold valid_state in H.
              elim H; intros.
              elim H12; intros.
              clear H; clear H12.
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
                exact (H14 (active_os s)).
                
                clear H14.
                unfold app in H.
                rewrite H0, H3 in H; simpl in H.
                rewrite H5 in H; simpl in H.
                rewrite H6 in H; simpl in H.
                elim H; intros.
                elim H12; intros.
                clear H; clear H12.
                rewrite H10 in H14.
                injection H14; intro.
                assert (option_rect (fun _ : option madd => Prop)
                  (fun ma' : madd =>
                  option_rect (fun _ : option page => Prop)
                  (fun p' : page =>
                  (ctxt_vadd_accessible context va = true ->
                  page_owned_by p' = OS (active_os s)) /\
                  (ctxt_vadd_accessible context va = false ->
                  page_owned_by p' = Hyp)) False (memory s ma')) False (x1 va)).
                  exact (H15 va).

                  clear H15.
                  rewrite H in H7.
                  rewrite H7 in H12; simpl in H12.
                  case_eq (memory s m1); intros.
                    rewrite H15 in H12; simpl in H12.
                    elim H12; intros; clear H12.
                    unfold app.
                    rewrite H11 in H15.
                    rewrite H15; simpl.
                    exact (H16 H2).

                    rewrite H15 in H12; simpl in H; elim H12.

              rewrite H7 in H11; simpl in H11; elim H11.

            rewrite H6 in H7; simpl in H7; elim H7.

          rewrite H5 in H7; simpl in H7; elim H7.

        rewrite H3 in H7; simpl in H7; elim H7.

      rewrite H0 in H7; simpl in H7; elim H7.
Qed.