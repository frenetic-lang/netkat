Set Implicit Arguments.

Require Import Coq.Vectors.Vector.
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

  Inductive fld := 
    | switch : fld
    | inport : fld
    | srcmac : fld
    | dstmac : fld
    | payload : fld.

  Inductive bvector : nat -> Type :=
    | bnil : bvector 0
    | bcons : forall n, bool -> bvector n -> bvector (S n). 

  Definition val := bvector max_val.

  Definition extend_bvector (n:nat) (bv:bvector n) : list (bvector (S n)) :=
    [bcons true bv; bcons false bv].

  Fixpoint flatten (A:Type) (l:list (list A)) : list A := 
    match l with 
      | nil => nil
      | h::t => h ++ flatten t
    end.

  Fixpoint all_vals_aux (i:nat) : list (bvector i) :=
    match i with 
      | 0 => [bnil]
      | S j => flatten (map (fun bv => extend_bvector bv) (all_vals_aux j))
    end.

  Definition all_flds := 
    [ switch; inport; srcmac; dstmac; payload ].

  Definition all_vals := all_vals_aux max_val.

  Lemma finite_fields : forall (f:fld), In f all_flds.
  Proof.
    intros. 
    destruct f; simpl; intuition.
  Qed.

  Lemma in_extend_bvector : 
    forall (n:nat) (b:bool) (bv:bvector n) (l:list (bvector n)),
      In bv l -> 
      In (bcons b bv) (flatten (map (fun bv => extend_bvector bv) l)).
  Proof.
    intros.
    generalize dependent l.
    induction l.
    + simpl; intuition.
    + simpl. intros.
      destruct H.
      - destruct b; rewrite H; intuition.
      - right. right. apply IHl. apply H.
  Qed.
    
  Lemma in_finite_vals_aux:
    forall (i:nat) (bv:bvector i), 
    In bv (all_vals_aux i).
  Proof.
    intros.
    induction bv.
    + simpl. intuition.
    + simpl. apply in_extend_bvector. apply IHbv.
  Qed.
  
  Lemma finite_vals : forall (v:val), In v all_vals.
  Proof.
    apply in_finite_vals_aux.
  Qed.
    
 Lemma fld_eqdec : forall (f1 f2 : fld), { f1 = f2 } + { f1 <> f2 }.
 Proof. 
   decide equality.
 Qed.

Lemma val_eqdec :  forall (v1 v2:val), { v1 = v2 } + { v1 <> v2 }.
Proof.
  admit.
Qed.
