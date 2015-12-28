Set Implicit Arguments.

Section Mapping_Definition.

Definition mapping (A B:Set): Set := A -> option B.

Definition mapping_update (A B:Set) (f:mapping A B) (compare:forall x1 x2 : A, {x1 = x2} + {x1 <> x2}) (x:A) (y:B):A->option B:=
  fun (a:A) => if compare a x then Some y else f a.

(* Utilizamos app cuando se quiere evaluar el predicado g(f(x)), si f(x) no está
* definida, app retorna False *)
Definition mapping_app (A B:Set) (f:A->option B) (x:A) (g:B->Prop):Prop:=
  option_rect (fun _:option B => Prop) g False (f x).

End Mapping_Definition.