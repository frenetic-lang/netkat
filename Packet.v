Set Implicit Arguments.

Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
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
      set_field f1 n1 (set_field f2 n2 pk) = set_field f2 n2 (set_field f1 n1 pk).

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
    induction bv; simpl.
    + intuition.
    + apply in_extend_bvector. apply IHbv.
  Qed.
  
  Lemma finite_vals : forall (v:val), In v all_vals.
  Proof.
    apply in_finite_vals_aux.
  Qed.
    
 Lemma fld_eqdec : forall (f1 f2 : fld), { f1 = f2 } + { f1 <> f2 }.
 Proof. 
   decide equality.
 Qed.

(* JNF: there has got to be a better way. *)
Lemma bvector_eqdec : forall (n:nat) (bv1 bv2:bvector n), { bv1 = bv2 } + { bv1 <> bv2 }.
Proof with eauto.
  dependent induction bv1; dependent destruction bv2.
  + left. intuition.
  + destruct b; destruct b0.
    - destruct (IHbv1 bv2) as [ eq | neq ].
      * left. rewrite -> eq. intuition.
      * right. unfold not. intros. contradiction neq. dependent destruction H. trivial.
    - right. unfold not. intros. dependent destruction H.
    - right. unfold not. intros. dependent destruction H.
    - destruct (IHbv1 bv2) as [ eq | neq ].
      * left. rewrite -> eq. intuition.
      * right. unfold not. intros. contradiction neq. dependent destruction H. trivial.
Qed.

Lemma val_eqdec : forall (v1 v2:val), {v1 = v2 } + { v1 <> v2 }.
Proof.
  apply bvector_eqdec.
Qed.

Record pk := Packet {
  Pkswitch : val;
  Pkinport : val;
  Pksrcmac : val;
  Pkdstmac : val;
  Pkpayload : val
}.

Definition get_field (f : fld) (p : pk): val :=
  match f with 
    | switch => Pkswitch p
    | inport => Pkinport p
    | srcmac => Pksrcmac p
    | dstmac => Pkdstmac p
    | payload => Pkpayload p
  end.

Definition set_field (f : fld) (v : val) (p : pk) : pk := 
  match f with
    | switch => Packet v (get_field inport p) (get_field srcmac p) (get_field dstmac p) (get_field payload p)
    | inport => Packet (get_field switch p) v (get_field srcmac p) (get_field dstmac p) (get_field payload p)
    | srcmac => Packet (get_field switch p) (get_field inport p) v (get_field dstmac p) (get_field payload p)
    | dstmac => Packet (get_field switch p) (get_field inport p) (get_field srcmac p) v (get_field payload p)
    | payload => Packet (get_field switch p) (get_field inport p) (get_field srcmac p) (get_field dstmac p) v
  end.

Lemma mod_mod_comm : forall (f1 f2 : fld) (v1 v2 : val) (p : pk), f1 <> f2 ->
  set_field f1 v1 (set_field f2 v2 p) = set_field f2 v2 (set_field f1 v1 p).
  intros.
  destruct f1; destruct f2; simpl; try solve [contradiction H; auto]; reflexivity.
Qed. 

