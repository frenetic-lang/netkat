Set Implicit Arguments.

Require Import Syntax.
Require Import Semantics.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Open Local Scope equiv_scope.
Hint Resolve reflexivity.

Lemma union_set_subset_is_set :
  forall (A : Type) (seta setb: Ensemble A), @Included _ seta setb -> @Union _  seta setb  = seta.
Proof with auto. 
  intros. unfold Included in *. 
  Print Union.
  apply Union_introl. 
Lemma pred_null_or_single :
  forall (pred1 : exp) (h : history), (pred pred1) -> 
         (eval pred1 h) = @Empty_set history \/ (eval pred1 h) = (Singleton _ h).
Proof with auto. intros. 
  induction pred1; simpl; auto. 
  destruct beq_nat...
  inversion H. subst. 
  apply IHpred1_1 in H2. apply IHpred1_2 in H3.
  destruct H2; destruct H3. rewrite H0. rewrite H1. auto. left. rewrite -> H0.
  rewrite -> H1. simpl.
  apply Union_inv.    
left. simpl. reflexivity.

Lemma ba_plus_one : 
  forall (pred1 : exp), (pred pred1) -> equiv_exp (Par pred1 (Id)) (Id).
Proof. intros. unfold equiv_exp. intros. simpl.

Lemma ba_plus_dist : 
  forall (pred1 pred2 pred3 : pred), (PrPar pred1 (PrSeq pred2 pred3)) 
          === (PrSeq (PrPar pred1 pred2) (PrPar pred1 pred3)).

Lemma ba_excl_mid :
  forall (pred1 : pred), (PrPar pred1 (PrNeg pred1)) === PrDrop pred1.

Lemma ba_seq_comm :
  forall (pred1 pred2 : pred), (PrSeq pred1 pred2) === (PrSeq pred2 pred1).

Lemma ba_contra :
  forall (pred1 : pred), (PrSeq pred1 (PrNeg pred1)) === PrDrop pred1.

Lemma ba_seq_idem :
  forall (pred1 : pred), (PrSeq pred1 pred1) === pred1.

