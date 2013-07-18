Set Implicit Arguments.

Require Import Relation.
Require Import Omega.
Require Import Syntax.
Require Import Semantics.
Require Import KAAxioms.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.

 Existing Instances Equivalence_exp.
 Local Open Scope equiv_scope.
 
 Lemma PA_Mod_Mod_Comm_Help: 
   forall (f1 f2 : field) (x : packet) (n1 n2 : nat), ~(f1 = f2) ->
   set_field_p (set_field_p x f1 n1) f2 n2 = set_field_p (set_field_p x f2 n2) f1 n1.
 Proof with auto.
   intros. destruct x. 
   destruct f1; destruct f2; try solve [simpl; auto | contradiction H; auto]. 
 Qed.  

 Lemma PA_Mod_Mod_Comm_Help2:
   forall (f1 f2 : field) (x : history) (n1 n2 : nat), ~(f1 = f2) ->
     set_field (set_field x f1 n1) f2 n2 = set_field (set_field x f2 n2) f1 n1.
 Proof with auto.
   intros.
   destruct x; simpl; rewrite -> PA_Mod_Mod_Comm_Help...
 Qed.
      
 Lemma PA_Mod_Mod_Comm:
   forall (f1 f2 : field) (n1 n2 : nat), ~(f1 = f2) -> 
    (Seq (Mod f1 n1) (Mod f2 n2)) 
     === (Seq (Mod f2 n2) (Mod f1 n1)).
 Proof with auto.
   intros. split.
   + intros. simpl in *. unfold join in *. destruct H0 as [z [H1 H2]].
     subst. exists (set_field x f2 n2). split... apply PA_Mod_Mod_Comm_Help2...
   + intros. simpl in *. unfold join in *. destruct H0 as [z [H1 H2]].
     subst. exists (set_field x f1 n1). split... apply PA_Mod_Mod_Comm_Help2...
 Qed.

 Lemma set_other_field_not_effect:
   forall (f1 f2 : field) (n1 n2 : nat) (x : history), ~(f1 = f2) ->
     (get_Field (get_Packet (set_field x f1 n1)) f2) =
     (get_Field (get_Packet x) f2).
   Proof with auto.
     intros. destruct x. destruct p.
     + destruct f1; destruct f2.
       - contradiction H...
       - simpl...
       - simpl...
       - contradiction H...
     + destruct f1; destruct f2.
       - contradiction H...
       - simpl... 
       - simpl...
       - contradiction H...
 Qed.
    
 Lemma PA_Mod_Filter_Comm:
   forall (f1 f2 : field) (n1 n2 : nat), ~(f1 = f2) ->
     (Seq (Mod f1 n1) (Match f2 n2)) === (Seq (Match f2 n2) (Mod f1 n1)).
 Proof with auto.
   intros. split.
   + intros. simpl in *. unfold join in *. destruct H0 as [z [H1 H2]]. subst.
     remember (beq_nat (get_Field (get_Packet (set_field x f1 n1)) f2) n2).
     destruct b... subst. exists x. split... subst. 
     rewrite set_other_field_not_effect in Heqb. rewrite <- Heqb...
     trivial. trivial. contradiction.
   + intros. simpl in *. unfold join in *. destruct H0 as [z [H1 H2]].
     subst. rewrite <- set_other_field_not_effect with (f1 := f1) (n1 := n1) in H1...
     remember (beq_nat (get_Field (get_Packet (set_field x f1 n1)) f2) n2).
     destruct b. subst. exists (set_field z f1 n1). split... rewrite <- Heqb...
     contradiction.
 Qed.

 Lemma obs_doesnt_matter:
   forall (f1 : field) (n1 : nat) (x : history),
     (get_Field (get_Packet (ConsHist (get_Packet x) x)) f1) = 
     (get_Field (get_Packet x) f1).
   Proof.
     intros.
     simpl... reflexivity.
 Qed.

 Lemma PA_Obs_Filter_Comm:
   forall (f1 : field) (n1 : nat),
     (Seq Obs (Match f1 n1)) === (Seq (Match f1 n1) Obs).
 Proof with auto.
   intros. split.
   + intros. simpl in *. unfold join in *. destruct H as [z [H0 H1]].
     subst. exists x.
    remember (beq_nat (get_Field (get_Packet (ConsHist (get_Packet x) x)) f1) n1).
     destruct b. split... rewrite obs_doesnt_matter in Heqb. rewrite <- Heqb... trivial.
    contradiction.
   + intros. simpl in *. unfold join in *. destruct H as [z [H0 H1]].
     subst. exists (ConsHist (get_Packet x) x). split...
     rewrite <- obs_doesnt_matter in H0.
     remember (beq_nat (get_Field (get_Packet (ConsHist (get_Packet x) x)) f1) n1).
     destruct b. subst... contradiction. trivial.
 Qed.
  
  Lemma always_true:
    forall (f1 : field) (n1 : nat) (x : history), 
     beq_nat (get_Field (get_Packet (set_field x f1 n1)) f1) n1 = true.
  Proof with auto.
    intros. destruct x. destruct p. simpl. unfold set_field_p. simpl. destruct f1.
    simpl... induction n1... simpl... induction n1... destruct p. simpl.
    unfold set_field_p. destruct f1. simpl. induction n1... simpl. induction n1...
 Qed.

  Lemma PA_Mod_Filter:
    forall (f1 : field) (n1 : nat),
      (Seq (Mod f1 n1) (Match f1 n1)) === (Mod f1 n1).
  Proof with auto.
    intros. split.
    + intros. simpl in *. unfold join in H. destruct H as [z [h1 h2]].
      subst. remember (beq_nat (get_Field (get_Packet (set_field x f1 n1)) f1) n1).
      destruct b. subst... contradiction.
    + intros. simpl in *. unfold join. subst. exists (set_field x f1 n1).
      split... rewrite always_true...
  Qed.
  
  Lemma Mod_to_Filter: 
    forall (f1 : field) (n1 : nat) (z : history), 
      (get_Field (get_Packet z) f1) = n1 -> z = set_field z f1 n1.
  Proof with auto.
    intros. destruct z; destruct p. simpl. destruct f1. simpl in *. subst...
    simpl in *. subst... simpl in *. destruct z; destruct p; destruct f1; simpl in *; 
    subst...
  Qed.

  Lemma PA_Filter_Mod:
    forall (f1 : field) (n1 : nat), 
      (Seq (Match f1 n1) (Mod f1 n1)) === (Match f1 n1).
  Proof with auto with arith.
    intros. split.
    + intros. simpl in *. unfold join in *. destruct H as [z [H1 H2]].
      subst. remember (beq_nat (get_Field (get_Packet x) f1) n1).
      destruct b. subst. apply Mod_to_Filter. apply beq_nat_eq in Heqb...
      contradiction.
    + intros. simpl in *. unfold join in *. exists y. split...
      remember (beq_nat (get_Field (get_Packet x) f1) n1).
      destruct b. subst. apply beq_nat_eq in Heqb. apply Mod_to_Filter in Heqb...
      contradiction.
  Qed. 

  Lemma PA_Mod_Mod:
    forall (f1 : field) (n1 n2: nat), 
      (Seq (Mod f1 n1) (Mod f1 n2)) === (Mod f1 n2).
  Proof with auto.
    intros. split.
    + intros. simpl in *. unfold join in H. destruct H as [z [H1 H2]].
      subst. destruct x; destruct p; simpl; destruct f1; simpl...
    + intros. simpl in *. unfold join. subst. exists (set_field x f1 n1). split...
      simpl. destruct x; destruct p; destruct f1; simpl...
  Qed.
      
 
      
     
       
 
