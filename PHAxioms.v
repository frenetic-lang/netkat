Set Implicit Arguments.

Require Import Arith.
Require Import ArithRing.
Require Import Relation.
Require Import Packet.
Require Import Omega.
Require Import Syntax.
Require Import Semantics.
Require Import KAAxioms.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Equality.

 Existing Instances Equivalence_exp.
 Local Open Scope equiv_scope.

 Lemma PA_Mod_Mod_Comm_Help2:
   forall (f1 f2 : field) (x : history) (n1 n2 : val), ~(f1 = f2) ->
     set_field (set_field x f1 n1) f2 n2 = set_field (set_field x f2 n2) f1 n1.
 Proof with auto.
   intros.
   destruct x; simpl; rewrite -> Packet.mod_mod_comm...
 Qed.
      
 Lemma PA_Mod_Mod_Comm:
   forall (f1 f2 : field) (n1 n2 : val), ~(f1 = f2) -> 
    (Seq (Mod f1 n1) (Mod f2 n2)) 
     === (Seq (Mod f2 n2) (Mod f1 n1)).
 Proof with auto.
   intros. split; intros; simpl in *; unfold join in *; destruct H0 as [z [H1 H2]].
   exists (set_field x f2 n2). split... subst. apply PA_Mod_Mod_Comm_Help2...
   exists (set_field x f1 n1). split... subst. apply PA_Mod_Mod_Comm_Help2...
 Qed.

 Lemma set_other_field_not_effect:
   forall (f1 f2 : field) (n1 n2 : val) (x : history), ~(f1 = f2) ->
     (Packet.get_field f2 (get_packet (set_field x f1 n1))) =
     (Packet.get_field f2 (get_packet x)).
   Proof with auto.
     intros. destruct x. destruct p.
     + destruct f1; destruct f2; simpl; auto; try solve [contradiction H; auto].
     + destruct f1; destruct f2; simpl; auto; try solve [contradiction H; auto].
   Qed.
    
 Lemma PA_Mod_Filter_Comm:
   forall (f1 f2 : field) (n1 n2 : val), ~(f1 = f2) ->
     (Seq (Mod f1 n1) (Match f2 n2)) === (Seq (Match f2 n2) (Mod f1 n1)).
 Proof with auto.
   intros. split ; intros; simpl in *; unfold join in *; destruct H0 as [z [H1 H2]]; subst.
     remember (Packet.beq_val (Packet.get_field f2 (get_packet (set_field x f1 n1))) n2).
     destruct b... subst. exists x. split...
     + rewrite set_other_field_not_effect in Heqb.
       remember (Packet.beq_val (Packet.get_field f2 (get_packet x)) n2).
       destruct b. reflexivity. inversion Heqb. trivial. trivial. 
   + contradiction. 
   + rewrite <- set_other_field_not_effect with (f1 := f1) (n1 := n1) in H1...
     remember (Packet.beq_val (Packet.get_field f2 (get_packet (set_field x f1 n1))) n2).
     destruct b. subst. exists (set_field z f1 n1). split... rewrite <- Heqb...
     contradiction.
 Qed.

 Lemma obs_doesnt_matter:
   forall (f1 : field) (n1 : val) (x : history),
     (Packet.get_field f1 (get_packet (ConsHist (get_packet x) x))) = 
     (Packet.get_field f1 (get_packet x)).
   Proof.
     intros. auto.
 Qed.

 Lemma PA_Obs_Filter_Comm:
   forall (f1 : field) (n1 : val),
     (Seq Obs (Match f1 n1)) === (Seq (Match f1 n1) Obs).
 Proof with auto.
   intros. split; intros; simpl in *; unfold join in *; destruct H as [z [H0 H1]]; subst. 
   + exists x.
    remember (Packet.beq_val (Packet.get_field f1 (get_packet (ConsHist (get_packet x) x))) n1).
     destruct b. split... rewrite obs_doesnt_matter in Heqb. rewrite <- Heqb... trivial.
    contradiction.
   + exists (ConsHist (get_packet x) x). split...
     rewrite <- obs_doesnt_matter in H0.
     remember (Packet.beq_val (Packet.get_field f1 (get_packet (ConsHist (get_packet x) x))) n1).
     destruct b. subst... contradiction. trivial.
 Qed.
  
  Lemma always_true:
    forall (f1 : field) (n1 : val) (x : history), 
     Packet.beq_val (Packet.get_field f1 (get_packet (set_field x f1 n1))) n1 = true.
  Proof with auto.
    intros; assert (true = Packet.beq_val n1 n1). rewrite Packet.beq_val_means with (v1 := n1) (v2 := n1); reflexivity.
    destruct x; destruct p; simpl; unfold Packet.set_field; simpl; destruct f1; simpl; rewrite H; reflexivity.
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
      split... rewrite always_true...
  Qed.
  
  Lemma Mod_to_Filter: 
    forall (f1 : field) (n1 : val) (z : history), 
      (Packet.get_field f1 (get_packet z)) = n1 -> z = set_field z f1 n1.
  Proof with auto.
    intros. destruct z; destruct p; simpl; destruct f1; simpl in *; subst...
  Qed.

  Lemma PA_Filter_Mod:
    forall (f1 : field) (n1 : val), 
      (Seq (Match f1 n1) (Mod f1 n1)) === (Match f1 n1).
  Proof with auto with arith.
    intros. split; intros; simpl in *; unfold join in *.
    + destruct H as [z [H1 H2]].
      subst. remember (Packet.beq_val (Packet.get_field f1 (get_packet x)) n1).
      destruct b. subst. apply Mod_to_Filter. apply Packet.beq_val_means in Heqb...
      contradiction.
    + exists y. split...
      remember (Packet.beq_val (Packet.get_field f1 (get_packet x)) n1).
      destruct b. subst. apply Packet.beq_val_means in Heqb. apply Mod_to_Filter in Heqb...
      contradiction.
  Qed. 

  Lemma PA_Mod_Mod:
    forall (f1 : field) (n1 n2: val), 
      (Seq (Mod f1 n1) (Mod f1 n2)) === (Mod f1 n2).
  Proof with auto.
    intros. split; intros; simpl in *; unfold join in *.
    + destruct H as [z [H1 H2]].
      subst. destruct x; destruct p; simpl; destruct f1; simpl...
    + subst. exists (set_field x f1 n1). split...
      simpl. destruct x; destruct p; destruct f1; simpl...
  Qed.
      
  Lemma PA_Contra:
    forall (f1 : field) (n1 n2 : val), (n1 <> n2) ->
      (Seq (Match f1 n1) (Match f1 n2)) === Drop.
  Proof with auto.
    intros. split; intros; simpl in *; unfold join in *.
    + destruct H0 as [z [H0 H1]]. unfold empty.
      remember (Packet.beq_val (Packet.get_field f1 (get_packet x)) n1).
      remember (Packet.beq_val (Packet.get_field f1 (get_packet z)) n2).
      destruct b; destruct b0; subst; destruct y; simpl in *; 
      destruct p; try solve [apply Packet.beq_val_means in Heqb; apply Packet.beq_val_means in Heqb0;
      subst; destruct f1; contradiction H; auto]; contradiction.
    + unfold empty in H0. contradiction.
  Qed.

 Fixpoint Add_Match_All (all_vals : list val) (f : field) : history -> history -> Prop :=
    match all_vals with
      | nil => fun (y x: history) => False
      | v :: l => union (fun (y x: history) => (match (Packet.beq_val (Packet.get_field f (get_packet x)) v) with
                                                 | true => True
                                                 | false => False
                                               end))
                        (Add_Match_All l f)
    end.

 (*Lemma PA_Match_All : forall (f : field) (h1 h2 : history), 
   (Add_Match_All Packet.all_vals f) h1 h2 === id h1 h2.
 Proof with auto.
   intros. split; intros.
   + unfold id. destruct f. unfold Add_Match_All in H. induction Packet.all_vals. contradiction. simpl in *.
     unfold union in H. destruct H. remember (Packet.beq_val (Packet.Pkswitch (get_packet h2)) a).
     destruct b. apply Packet.beq_val_means in Heqb. simpl in *.*)

  Fixpoint Add_Match_All_Exp (all_vals : list val) (f : field) : exp :=
    match all_vals with 
      | nil => Drop
      | v :: l => (Par (Match f v) (Add_Match_All_Exp l f))
    end.

  Lemma PA_Match_All : forall (f : field), 
    Add_Match_All_Exp Packet.all_vals f === Id.
  Proof with auto.
    intros. split; intros; simpl in *.
    + destruct f; destruct x; destruct y; destruct p; destruct p0; simpl in *; try solve [induction Packet.all_vals; 
     try solve [unfold empty in H; contradiction]; unfold union in H; destruct H; simpl in *;
        remember (Packet.beq_val Pkswitch a); destruct b; try solve [trivial]; try solve [contradiction];
        apply IHl in H; trivial]; 
     try solve [induction Packet.all_vals; 
     try solve [unfold empty in H; contradiction]; unfold union in H; destruct H; simpl in *;
        remember (Packet.beq_val Pkinport a); destruct b; try solve [trivial]; try solve [contradiction];
        apply IHl in H; trivial];
     try solve [induction Packet.all_vals; 
     try solve [unfold empty in H; contradiction]; unfold union in H; destruct H; simpl in *;
        remember (Packet.beq_val Pksrcmac a); destruct b; try solve [trivial]; try solve [contradiction];
        apply IHl in H; trivial];
     try solve [induction Packet.all_vals; 
     try solve [unfold empty in H; contradiction]; unfold union in H; destruct H; simpl in *;
        remember (Packet.beq_val Pkdstmac a); destruct b; try solve [trivial]; try solve [contradiction];
        apply IHl in H; trivial];
     try solve [induction Packet.all_vals; 
     try solve [unfold empty in H; contradiction]; unfold union in H; destruct H; simpl in *;
        remember (Packet.beq_val Pkpayload a); destruct b; try solve [trivial]; try solve [contradiction];
        apply IHl in H; trivial].
    + unfold id in H. subst.
      admit.
   Admitted.
    
   
    
  
   
     
      
     
       
 
