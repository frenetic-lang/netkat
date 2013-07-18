Set Implicit Arguments.

Require Import Relation.
Require Import Syntax.
Require Import Semantics.
Require Import KAAxioms.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.

 Existing Instances Equivalence_exp.
 Local Open Scope equiv_scope.
 
 Lemma PA_Mod_Mod_Comm:
   forall (f1 f2 : field) (n1 n2 : nat), ~(f1 = f2) -> 
    (Seq (Mod f1 n1) (Mod f2 n2)) 
     === (Seq (Mod f2 n2) (Mod f1 n1)).
 Proof with auto.
   intros. split.
   + intros. simpl in *. unfold join in *. destruct H0 as [z [H1 H2]].
     exists z. split. destruct f1. destruct f2.
     unfold not in H. 
     Focus 2. subst.