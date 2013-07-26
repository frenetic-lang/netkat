Set Implicit Arguments.

Require Import Arith.
Require Import ArithRing.
Require Import Relation.
Require Import Packet.
Require Import Omega.
Require Import Syntax.
Require Import Semantics.
Require Import KAAxioms.
Require Import BooleanAlgebraAxioms.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

 Existing Instances Equivalence_exp.
 Local Open Scope equiv_scope.
  
 Lemma PA_Mod_Mod_Comm:
   forall (f1 f2 : field) (n1 n2 : val), ~(f1 = f2) -> 
    (Seq (Mod f1 n1) (Mod f2 n2)) 
     === (Seq (Mod f2 n2) (Mod f1 n1)).
 Proof with auto.
   intros. split; intros; simpl in *; unfold join in *; destruct H0 as [z [H1 H2]].
   exists (set_field x f2 n2). split... subst. destruct x; simpl in *; rewrite Packet.mod_mod_comm;  
   try solve [reflexivity]; intuition. 
   exists (set_field x f1 n1). split... subst. destruct x; simpl in *; rewrite Packet.mod_mod_comm;
   try solve [reflexivity]; intuition. 
 Qed. 
    
 Lemma PA_Mod_Filter_Comm:
   forall (f1 f2 : field) (n1 n2 : val), ~(f1 = f2) ->
     (Seq (Mod f1 n1) (Match f2 n2)) === (Seq (Match f2 n2) (Mod f1 n1)).
 Proof with auto.
   intros. split ; intros; simpl in *; unfold join in *; destruct H0 as [z [H1 H2]]; subst.
   remember (Packet.beq_val (Packet.get_field f2 (get_packet (set_field x f1 n1))) n2).
   destruct b... subst. exists x. split...
   + rewrite Packet.mod_filter_comm with (f := f1) (n:= n1). destruct x; simpl in *;
     rewrite <- Heqb; auto.
     trivial. 
   + contradiction. 
   + exists (set_field x f1 n1). split.  reflexivity.
     rewrite Packet.mod_filter_comm with (f:= f1) (n := n1) in H1. 
     remember (Packet.beq_val (Packet.get_field f2 (get_packet (set_field x f1 n1))) n2).
     destruct b; try solve [destruct x;  simpl in *; rewrite <- Heqb in H1; try solve [subst; auto]; auto].
     trivial.
 Qed.

 Lemma PA_Obs_Filter_Comm:
   forall (f1 : field) (n1 : val),
     (Seq Obs (Match f1 n1)) === (Seq (Match f1 n1) Obs).
 Proof with auto.
   intros. split; intros; simpl in *; unfold join in *; destruct H as [z [H0 H1]]; subst;
   remember (Packet.beq_val (Packet.get_field f1 (get_packet (ConsHist (get_packet x) x))) n1);
   destruct b; simpl in *.  
   + exists x. split... rewrite <- Heqb. trivial. 
   + contradiction.
   + exists (ConsHist (get_packet x) x). split... simpl in *.
     rewrite <- Heqb in H0. rewrite <- Heqb. subst...
   + rewrite <- Heqb in H0. contradiction.
 Qed.
  
  Lemma PA_Mod_Filter:
    forall (f1 : field) (n1 : val),
      (Seq (Mod f1 n1) (Match f1 n1)) === (Mod f1 n1).
  Proof with auto.
    intros. split; intros; simpl in *; unfold join in *.
    + destruct H as [z [h1 h2]].
      subst. remember (Packet.beq_val (Packet.get_field f1 (get_packet (set_field x f1 n1))) n1).
      destruct b. subst... contradiction.
    + subst. exists (set_field x f1 n1).
      split... destruct x; simpl; rewrite Packet.mod_filter; assert (n1 = n1); try solve [reflexivity];
      apply Packet.beq_val_true in H; rewrite <- H; reflexivity.
  Qed.

  Lemma PA_Filter_Mod:
    forall (f1 : field) (n1 : val), 
      (Seq (Match f1 n1) (Mod f1 n1)) === (Match f1 n1).
  Proof with auto with arith.
    intros. split; intros; simpl in *; unfold join in *.
    + destruct H as [z [H1 H2]].
      subst. remember (Packet.beq_val (Packet.get_field f1 (get_packet x)) n1).
      destruct b. subst. destruct z; unfold set_field; simpl in *; 
      apply Packet.beq_val_true in Heqb; rewrite Packet.filter_mod in Heqb;
      rewrite Heqb; auto. auto.
    + exists y. split...
      remember (Packet.beq_val (Packet.get_field f1 (get_packet x)) n1).
      destruct b. subst. apply Packet.beq_val_true in Heqb. destruct y; simpl in *;
      rewrite Packet.filter_mod in Heqb; rewrite Heqb; reflexivity. contradiction.
  Qed. 

  Lemma PA_Mod_Mod:
    forall (f1 : field) (n1 n2: val), 
      (Seq (Mod f1 n1) (Mod f1 n2)) === (Mod f1 n2).
  Proof with auto.
    intros. split; intros; simpl in *; unfold join in *.
    + destruct H as [z [H1 H2]].
      subst. destruct x; simpl in *; rewrite Packet.mod_mod; reflexivity.
    + subst. exists (set_field x f1 n1). split...
      simpl. destruct x; simpl in *; rewrite Packet.mod_mod; reflexivity. 
  Qed.
      
  Lemma PA_Contra:
    forall (f1 : field) (n1 n2 : val), (n1 <> n2) ->
      (Seq (Match f1 n1) (Match f1 n2)) === Drop.
  Proof with auto.
    intros. split; intros; simpl in *; unfold join in *.
    + destruct H0 as [z [H0 H1]]. unfold empty.
      remember (Packet.beq_val (Packet.get_field f1 (get_packet x)) n1).
      remember (Packet.beq_val (Packet.get_field f1 (get_packet z)) n2).
      destruct b; destruct b0; subst; destruct y; simpl in *; try solve
      [apply Packet.beq_val_true in Heqb; apply Packet.beq_val_true in Heqb;
      remember (Packet.beq_val (Packet.get_field f1 p) n1); destruct b; try solve
      [try solve [inversion Heqb]; apply Packet.beq_val_true in Heqb1; apply Packet.beq_val_true in Heqb0;
      rewrite Heqb1 in Heqb0; contradiction]]; try solve [contradiction H1]; try solve [contradiction H0].
    + unfold empty in H0. contradiction.
  Qed.

  Fixpoint Add_Matches (l : list val) (f : field) : exp :=
    match l with 
      | nil => Drop
      | h :: t => (Par (Match f h) (Add_Matches t f))
    end.

  Lemma Add_Matches_Only_Match : forall (l : list val) (f : field) (h h': history),
    eval (Add_Matches l f) h h' -> h = h'.
  Proof.
    intros. induction l. simpl in H. unfold empty in H. contradiction.
    simpl in H. unfold union in H. destruct H. remember (Packet.beq_val (Packet.get_field f (get_packet h)) a).
    destruct b. trivial. contradiction. apply IHl. trivial.
  Qed.    
 
  Lemma Add_Matches_Match : forall (l : list val) (f : field) (h:history),
    In (Packet.get_field f (get_packet h)) l -> 
    (eval (Add_Matches l f) h h).
  Proof with auto.
    intros. induction l.
    + inversion H.
    + remember (Packet.beq_val (Packet.get_field f (get_packet h)) a). destruct b; simpl; unfold union.
      - left. rewrite <- Heqb. reflexivity.
      - right. assert (In (Packet.get_field f (get_packet h)) l). simpl in H. destruct H.
        * apply Packet.beq_val_false in Heqb. rewrite <- H in Heqb. contradiction Heqb. reflexivity.
        * trivial.
        * apply IHl. trivial.
  Qed.         

  Lemma PA_Match_All : forall (f : field),
    Add_Matches Packet.all_vals f ===Id.
  Proof.
   intros. split; intros.
   apply Add_Matches_Only_Match in H. simpl. unfold id. trivial.
   simpl in H. unfold id in H. subst. assert (In (Packet.get_field f (get_packet y)) Packet.all_vals).
   apply Packet.finite_vals. apply Add_Matches_Match. trivial.
  Qed.


    
 
   
    
  
   
     
      
     
       
 
