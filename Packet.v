Set Implicit Arguments.

Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.

Module Type PACKET.

  Parameter pk fld val : Type.

  Parameter all_fields : list fld.

  Parameter all_vals : list val.

  Axiom finite_fields : forall (f : fld), In f all_fields.

  Axiom finite_vals : forall (v : val), In v all_vals.

  Axiom fld_eqdec : forall (f1 f2 : fld), { f1 = f2 } + { f1 <> f2 }.

  Axiom val_eqdec : forall (v1 v2 : val), { v1 = v2 } + { v1 <> v2 }.
  
  Axiom set_field : fld -> val -> pk -> pk.
 
  Axiom get_field : fld -> pk -> val.

  Section Axioms.

    Variable pk : pk.
    Variable f f' f1 f2 : fld.
    Variable n n' n1 n2 : val.

    Axiom mod_mod_comm : f1 <> f2 ->
      set_field  f1 n1 (set_field f2 n2 pk) = set_field f2 n2 (set_field f1 n1 pk).

    Axiom mod_filter_comm : f <> f' -> 
      get_field f' pk = get_field f' (set_field f n pk).

    Axiom mod_filter : get_field f (set_field f n pk) = n.

    Axiom filter_mod : get_field f pk = n <-> set_field f n pk = pk.

    Axiom mod_mod : set_field f n (set_field f n' pk) = set_field f n pk.

  End Axioms.
  
End PACKET.

Module Packet : PACKET.

  Require Import Coq.Arith.Compare_dec.

  Parameter max_fld max_val : nat.

  Definition fld := { n : nat & n < max_fld }.

  Definition val := { n : nat & n < max_val }.

Check lt_dec.

  Fixpoint iota (n : nat) : list nat :=
     match n with
     | O => [0]
     | S m => cons (n) (iota m)
     end.

  Definition with_bound (max n : nat) : option { n : nat & n < max }:=
    match lt_dec n max with
    | left proof => Some (@existT nat (forall n, n < max) n proof)
    | right _ => None
    end.

  Check with_bound.
  
  Definition all_fields := map (with_bound max_fld) (iota max_fld).
  Defin
  Example iota_test : (iota 5) = [5; 4; 3; 2; 1; 0].
    cbv. reflexivity.
  Qed.

  
  

  

  Fixpoint make_all_fields_help (n stop : nat) : list fld:=
    match stop with 
    | O => (make_all
   


  Fixpoint make_all_fields (n : nat) : list fld :=
    match lt_dec n max_fld with
    | left n_lt_max_fld => n :: (make_all_fields 
