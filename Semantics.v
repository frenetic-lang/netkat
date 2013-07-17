Set Implicit Arguments.

Require Import Syntax.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.

Module Relation.

  Section Defs.

    Variable A : Type.
    
    Definition relation := A -> A -> Prop.
    
    Definition union (R1 R2 : relation) : relation :=
      fun (x y : A) => R1 x y \/ R2 x y.
    
    Definition join (R1 R2 : relation) : relation :=
      fun (x y : A) => exists (z : A), R1 x z /\ R2 z y.
    
    Definition empty : relation :=
      fun (x y : A) => False.
    
    Definition id : relation :=
      fun (x y : A) => x = y.
    
    Fixpoint expt (R : relation) (n : nat) : relation :=
      match n with
        | 0 => id
        | S m => join R (expt R m)
      end.
    
    Definition star (R : relation) : relation :=
      fun (x y : A) => exists n, (expt R n) x y.

    Definition equiv (R1 R2 : relation) :=
      forall (x y : A), R1 x y <-> R2 x y.

   Definition inv (R : relation) : relation :=
     fun (x y : A) => ((R x y) /\ False) \/ (~(R x y) /\ (x = y)).
  
  Definition contains (R1 R2 : relation) : Prop :=
     forall (x y : A), R1 x y -> R2 x y.

  End Defs.

  Instance Equivalence_equiv `(A : Type) : Equivalence (@equiv A).
  Proof with auto.
    split; unfold equiv.
    + unfold Reflexive.
      intros. intuition.
    + unfold Symmetric.
      intros. symmetry. apply H.
    + unfold Transitive.
      intros.
      split... 
      - intros.
        apply H0.
        apply H...
      - intros.
        apply H.
        apply H0...
  Qed.

End Relation.

Module Semantics.

  Import Relation.

  Definition get_Field (pkt : packet) (fld : field) : nat :=
    match fld with
      | Src => pktSrc pkt
      | Dst => pktDst pkt
    end.

  Definition set_field (h : history) (fld : field) (n : nat) : history :=
    match h with
      | OneHist p => match fld with
                       | Src => OneHist (Packet n (get_Field p Dst))
                       | Dst => OneHist (Packet (get_Field p Src) n)
                     end
      | ConsHist p hst => match fld with
                            | Src => ConsHist (Packet n (get_Field p Dst)) hst
                            | Dst => ConsHist (Packet (get_Field p Src) n) hst
                          end
    end.        

  Definition get_Packet (hst : history) : packet :=
    match hst with
      | OneHist p => p
      | ConsHist p h => p
    end.

  Locate exp.
  Check exp.
  Check relation.
  Fixpoint eval (e : exp) : relation history :=
    match e with
      | Drop => @empty history
      | Id => @id history
      | Match f v => 
        fun (h r : history) =>
          match beq_nat (get_Field (get_Packet h) f) v with 
            | true => h = r
            | false => False
          end
      | Mod f v => 
        fun (h r : history) => r = set_field h f v
      | Par e1 e2 => union (eval e1) (eval e2)
      | Neg e1 => inv (eval e1)
      | Obs => fun (h r : history) => r= (ConsHist (get_Packet h) h)
      | Seq e1 e2 => join (eval e1) (eval e2)
      | Star e1 => star (eval e1)
    end.

  Definition equiv_exp (e1 : exp) (e2 : exp) : Prop := 
    equiv (eval e1) (eval e2).

  Instance Equivalence_exp : Equivalence equiv_exp.
  Proof with auto.
    unfold equiv_exp.
    split.
    + unfold Reflexive.
      intros.
      apply reflexivity.
    + unfold Symmetric.
      intros.
      apply symmetry...
    + unfold Transitive.
      intros.
      eapply transitivity; eauto.
  Qed.

End Semantics.

Module BooleanAlgebra.

  Import Semantics.
  Import Syntax.
  Import Relation.

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
   Admitted.

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