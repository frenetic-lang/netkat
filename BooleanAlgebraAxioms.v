Set Implicit Arguments.

Require Import Relation.
Require Import Syntax.
Require Import Semantics.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.

  Existing Instances Equivalence_exp.
  Local Open Scope equiv_scope.


  (* Predicates are either identity or empty *)
  Lemma bool_spec : forall (e : exp),
    pred e ->
    forall (h r : history),
      eval e h r -> (False \/ h = r).
  Proof with auto.
    intros.
    generalize dependent h.
    generalize dependent r.
    induction H; intros...
    + unfold eval in H0. 
    destruct (beq_nat (get_Field (get_Packet h) f) v) in H0...
    + simpl in H1. unfold union in H1. destruct H1...
    + simpl in H1. unfold join in H1. destruct H1. destruct H1.
      apply IHpred1 in H1. destruct H1. contradiction. subst.
      apply IHpred2 in H2...
    + simpl in H0. unfold inv in H0. destruct H0. destruct H0. contradiction.
      unfold not in H0. destruct H0. right...
  Qed.

  Lemma bool_spec_new : forall (e : exp), pred e -> 
    contains (eval e) (@id history).
  Proof with auto.
    intros. unfold contains.
    induction H; intros...
    + simpl in H. unfold empty in H. contradiction.
    + simpl in H. destruct (beq_nat (get_Field (get_Packet x) f) v) in H...
      contradiction.
    + simpl in H1. unfold union in H1. destruct H1...
    + simpl in H1. unfold join in H1.  destruct H1... destruct H1...
      apply IHpred1 in H1. apply IHpred2 in H2. unfold id in *. subst...
    + simpl in H0. unfold inv in H0. destruct H0. destruct H0. contradiction. 
      unfold not in H0. unfold id. destruct H0...
 Qed. 

  Lemma bool_true_spec : forall (e : exp) (h1 h2 : history),
    pred e ->
    eval e h1 h2 ->
    h1 = h2.
  Proof with eauto.
    intros.
    eapply bool_spec in H...
    destruct H...
    contradiction.
  Qed.
  
  Lemma BA_Plus_One : 
    forall (e : exp),
      pred e ->
      (Par e Id) === Id.
  Proof with auto.
    intros.
    split.
    + intros. simpl in *. 
      unfold union in H0.
      destruct H0... apply bool_spec_new in H0...
    + intros. simpl in *.
      unfold union...
   Qed.
  
  Lemma BA_Seq_Comm :
    forall (e1 e2 : exp),
      pred e1 -> pred e2 ->
        (Seq e1 e2) === (Seq e2 e1).
  Proof with eauto. 
    intros. split. simpl in *.
    +  intros. unfold join in *. destruct H1...
       destruct H1.
       assert (x = x0). eapply bool_true_spec. exact H. trivial.
       subst.
       assert (x0 = y). eapply bool_true_spec. exact H0. trivial.
       subst.
       exists y...
     + simpl. unfold join. intros.
       destruct H1 as [z [H1 H2]].
       remember H1. clear Heqe.
       remember H2. clear Heqe0.
       apply bool_true_spec in H1...
       apply bool_true_spec in H2...
       subst...
    Qed.       

  Lemma BA_Plus_Dist :
    forall (e1 e2 e3 : exp),
       pred e1 /\ pred e2 /\ pred e3 ->
         (Par e1 (Seq e2 e3)) === (Seq (Par e1 e2) (Par e1 e3)).
  Proof with auto.
    intros. split.
    + intros. simpl in *. unfold join in *. unfold union in *.
      destruct H0.
      assert (x = y). eapply bool_true_spec. destruct H. exact H. trivial.
      subst. exists y. split...
      destruct H0. destruct H0. destruct H. destruct H2. remember H0 as H0'.
      clear HeqH0'. remember H1 as H1'. clear HeqH1'.
      eapply bool_true_spec in H0. subst. eapply bool_true_spec in H1. subst.
      exists y. split... trivial. trivial.
    + intros.  simpl in *. unfold join in *. unfold union in *.
      destruct H0. destruct H0. destruct H0. remember H0 as H0'. clear HeqH0'.
      destruct H. eapply bool_true_spec in H0. subst. destruct H1. left. trivial.
      destruct H2. eapply bool_true_spec in H0.  subst. left. trivial.
      trivial. trivial.
      destruct H1. destruct H. remember H1 as H1'. clear HeqH1'.
      eapply bool_true_spec in H1. subst. destruct H2. eapply bool_true_spec in H0.
      subst. left. auto. auto. auto.
      right. remember H0 as H0'. clear HeqH0'. remember H1 as H1'. clear HeqH1'.
      destruct H. destruct H2.
      eapply bool_true_spec in H1. subst. eapply bool_true_spec in H0. subst.
      exists y. split... trivial. trivial.
  Qed.

  Lemma BA_Seq_Idem :
    forall (e : exp),
      pred e -> (Seq e e) === e.
  Proof with auto.
    intros. split.
    + intros. simpl in *. unfold join in H0. destruct H0...
      destruct H0... remember H1 as H1'. remember H0 as H0'.
      clear HeqH0'. clear HeqH1'. apply bool_true_spec in H0...
      apply bool_true_spec in H1. subst. trivial. trivial.
    + intros. simpl. unfold join. remember H0 as H0'. clear HeqH0'.
      apply bool_true_spec in H0... subst. exists y...
  Qed.
      
  Lemma either_or : 
    forall (e : exp) (x : history),
      pred e -> (eval e x x) \/ ~(eval e x x).
  Proof with auto.
    intros.
    induction e.
    + intuition.
    + intuition.
    + simpl. destruct (beq_nat (get_Field (get_Packet x) f) n). left. reflexivity.
      unfold not. right. intros. trivial.
    + simpl in *. unfold union. destruct IHe1. inversion H. trivial. destruct IHe2.
      inversion H. trivial. left. intuition. left. intuition. inversion H. 
      apply IHe2 in H4. destruct H4. left. right. trivial. right. unfold not in *.
      intuition.
    + inversion H. apply IHe1 in H2. apply IHe2 in H3. clear IHe1 IHe2. 
      subst. simpl in *. unfold join.
       destruct H2; destruct H3. 
       - left. exists x. intuition.
       - right. unfold not. intros. destruct H2 as [z [H2 H3]].
         remember H3 as H3'. clear HeqH3'. apply bool_true_spec in H3. subst. contradiction.
         inversion H. trivial.
       - right. unfold not. intros. destruct H2 as [z [H2 H3]].
         remember H2 as H2'. clear HeqH2'. apply bool_true_spec in H2. subst. contradiction.
         inversion H. trivial.
       - right. unfold not. intros. destruct H2. destruct H2. remember H2 as H2'.
         clear HeqH2'. apply bool_true_spec in H2. subst. contradiction. inversion H. trivial.
    + simpl in *. unfold inv. inversion H. apply IHe in H1. clear IHe. subst.
        destruct H1. 
        - right. unfold not. intros. intuition.
        - left. right. split...
    + inversion H.
    + inversion H.
    + inversion H.
  Qed.
         

  Lemma BA_Excl_Mid : 
    forall (e : exp), 
      pred e -> (Par e (Neg e)) === Id.
  Proof with auto.
    intros.
    split.
    + intros. simpl in *.
      unfold union in H0.
      unfold inv in H0. unfold id.
      destruct H0. Focus 2. destruct H0. destruct H0. contradiction.
      destruct H0... apply bool_spec_new in H0...
    + intros. assert (x = y). apply bool_true_spec in H0...
      subst. simpl. unfold union. simpl in H0. unfold id in H0. unfold inv.
      apply (either_or y) in H. intuition.
  Qed.

  Lemma BA_Contra :
    forall (e : exp),
      pred e ->
      (Seq e (Neg e)) === Drop.
  Proof with auto.
    intros. split. 
    + intros. simpl in *. unfold join in H0.
      destruct H0.  destruct H0. remember H0 as H0'.
      clear HeqH0'. apply bool_true_spec in H0. subst. unfold inv in H1.
      destruct H1. destruct H0. contradiction. destruct H0. subst. contradiction.
      trivial.
    + intros. simpl in *. unfold empty in H0. contradiction.
  Qed.        




