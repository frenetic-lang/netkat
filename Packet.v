Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Lt.
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

  Fixpoint iota (n : nat) : list nat :=
     match n with
     | O => [0]
     | S m => cons (n) (iota m)
     end.

  Example iota_test : (iota 5) = [5; 4; 3; 2; 1; 0].
    cbv. reflexivity.
  Qed.

  Fixpoint with_bound (i max:nat) : list { n : nat & n < max } :=
    match lt_dec i max with
      | left proof => 
        (@existT nat (fun (n:nat) => n < max) i proof) :: 
        ( match i with 
            | 0 => [] 
            | S j => with_bound j max 
          end )
      | right _ => 
        ( match i with 
            | 0 => [] 
            | S j => with_bound j max
          end )
    end.
  
  Definition all_fields := with_bound max_fld max_fld.

  Definition all_vals := with_bound max_val max_val.
  
  Lemma finite_fields_proj : forall (f : fld) (n i : nat), projT1 f = n -> n < i -> 
    i < max_fld ->  
    In f (with_bound i max_fld).
  Proof. 
    intros. induction i.
    + inversion H0.
    + destruct n. destruct i.
      simpl.
      destruct (lt_dec 1 max_fld).
      simpl.
      destruct (lt_dec 0 max_fld).
      simpl.
      right.
      left.
      auto.
      admit.
      admit.
      admit.
      admit.
      admit.
