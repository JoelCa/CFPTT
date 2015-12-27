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
      (mapping_app c1 c2 c3)(at level 200).

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
                                  /\ memory s' = mapping_update (memory s) madd_eq ma (Page (RW (Some x)) (OS  (active_os s)))
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
  destruct H.
  unfold valid_state in H.
  elim H; intros; clear H; clear H3.
  destruct a; unfold Post in H1.
    rewrite <- H1; assumption.

    elim H1; intros; clear H1.
    elim H; intros; clear H.
    elim H3; intros; clear H3.
    elim H4;intros; clear H4.
    elim H5;intros; clear H5.
    elim H6;intros; clear H6.
    unfold prop3 in *.
    rewrite H5, H4, H3.
    assumption.

    elim H1; intros; clear H1; (elim H; intros; clear H; (elim H3; intros; clear H3)).
      unfold prop3; intros.
      assumption.

      elim H4; intros; clear H4.
      elim H5; intros; clear H5.
      elim H6; intros; clear H6.
      unfold prop3.
      intros.
      rewrite H5, H1 in H8.
      discriminate H8.
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
  elim H0; intros; clear H0.
  elim H3; intros; clear H3.
  elim H4; intros; clear H4.
  elim H3; intros; clear H3.
  exists x; split.
    assumption.

    unfold va_mapped_to_ma, mapping_app in H4.
    case_eq (oss s (active_os s)); intros.
      rewrite H3 in H4; simpl in H4.
      case_eq (hypervisor s (active_os s)); intros.
        rewrite H6 in H4; simpl in H4.
        case_eq (m (curr_page o)); intros.
          rewrite H7 in H4; simpl in H4.
          case_eq (memory s m0); intros.
            rewrite H8 in H4; simpl in H4.
            elim H4; intros; clear H4.
            elim H9; intros; clear H9.
            case_eq (x0 va); intros.
              rewrite H9 in H10; simpl in H10.
              unfold valid_state in H.
              elim H; intros; clear H.
              elim H12; intros; clear H12.
              unfold prop6 in H13.
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
                exact (H13 (active_os s)).
                
                clear H13.
                unfold mapping_app in H12.
                rewrite H3, H6 in H12; simpl in H12.
                rewrite H7 in H12; simpl in H12.
                rewrite H8 in H12; simpl in H12.
                elim H12; intros; clear H12.
                elim H13; intros; clear H13.
                rewrite H4 in H12.
                injection H12; intro.
                assert (option_rect (fun _ : option madd => Prop)
                  (fun ma' : madd =>
                  option_rect (fun _ : option page => Prop)
                  (fun p' : page =>
                  (ctxt_vadd_accessible context va = true ->
                  page_owned_by p' = OS (active_os s)) /\
                  (ctxt_vadd_accessible context va = false ->
                  page_owned_by p' = Hyp)) False (memory s ma')) False (x1 va)).
                  exact (H14 va).

                  clear H14.
                  rewrite <- H13, H9 in H15; simpl in H15.
                  case_eq (memory s m1); intros.
                    rewrite H14 in H15; simpl in H15.
                    elim H15; intros; clear H15.
                    unfold mapping_app.
                    rewrite <- H10, H14; simpl.
                    exact (H16 H2).

                    rewrite H14 in H15; simpl in H15; elim H15.

              rewrite H9 in H10; simpl in H10; elim H10.

            rewrite H8 in H4; simpl in H4; elim H4.

          rewrite H7 in H4; simpl in H4; elim H4.

        rewrite H6 in H4; simpl in H4; elim H4.

      rewrite H3 in H4; simpl in H4; elim H4.
Qed.