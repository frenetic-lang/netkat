Set Implicit Arguments.
Require Import CpdtTactics.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Module Type SETS.

  Parameter t : Type. (* type of sets *)

  Parameter elt : Type.

  Parameter singleton : elt -> t.

  Parameter empty : t.

  Parameter union : t -> t -> t.

  Parameter diff : t -> t -> t.

  Parameter indexed_union : (nat -> t) -> t.

  Parameter filter : (elt -> bool) -> t -> t.

  Parameter map : (elt -> elt) -> t -> t

  Parameter subset : t -> t -> Prop.

  Parameter In : elt -> t -> Prop.

  Axiom empty_spec : forall (x : elt), In x empty -> False.

  Axiom singleton_spec : forall (x y : elt), In x (singleton y) <-> x = y.

  Axiom union_intro_l : forall (x : elt) (s1 s2 : t), In x s1 -> In x (union s1 s2).
  Axiom union_intro_r : forall (x : elt) (s1 s2 : t), In x s2 -> In x (union s1 s2).
  Axiom union_extro : forall (x : elt) (s1 s2 : t), In x (union s1 s2) -> In x s1 \/ In x s2.

  Axiom union_spec : forall (x : elt) (s1 s2 : t), In x (union s1 s2) <-> In x s1 \/ In x s2.

  Axiom diff_spec : forall (x : elt) (s1 s2 : t), In x (diff s1 s2) <-> (In x s1 /\ ~(In x s2)).

  Axiom subset_spec : forall (s1 s2 : t), subset s1 s2 <-> (forall (x : elt), In x s1 -> In x s2).

  Axiom extensionality : forall (s1 s2 : t), (forall (x : elt), In x s1 <-> In x s2) -> s1 = s2.

  Hint Resolve union_intro_l union_intro_r union_extro.
  Hint Resolve empty_spec singleton_spec diff_spec subset_spec union_spec.

  Hint Rewrite union_spec subset_spec singleton_spec.

  Lemma union_comm : forall (s1 s2 : t), union s1 s2 = union s2 s1.
  Proof with eauto.
    intros.
    apply extensionality.
    intros.
    autorewrite with core using simpl. intuition.
  Qed.

  Lemma union_assoc : forall (s1 s2 s3 : t), union s1 (union s2 s3) = union (union s1 s2) s3.
  Proof with auto.
    intros.
    apply extensionality.
    intros.
    autorewrite with core using simpl. intuition.
  Qed.

  Lemma empty_is_subset : forall (s1 : t), subset empty s1. 
  Proof with auto.
   intros. 
   apply subset_spec. intros.
   apply empty_spec in H. contradiction.
  Qed.

  Lemma union_subset : forall (s1 s2 :t), subset s1 s2 -> (union s1 s2) = s2.
  Proof with auto.
   intros. 
   apply extensionality.
   intros.
   rewrite subset_spec in H.
   autorewrite with core using simpl.
   intuition.
  Qed. 

  Lemma self_subset_self : forall (s1 : t), subset s1 s1.
  Proof with auto.
   intros. rewrite subset_spec. intros. intuition.
  Qed. 

 


Section Sets.
  
  Variable A : Type.
  
  Definition set := A -> Prop.

  Definition singleton (a : A) : set := fun (b : A) => a = b.

  Definition empty : set := fun (_ : A) => False.

  Definition union (set1 set2 : set) : set := fun (y : A) => set1 y \/ set2 y.

  Definition set_minus (set1 set2 : set) : set := fun (y : A) => set1 y /\ ~set2 y.

  Definition indexed_union (f : nat -> set) : set := fun (y : A) => exists (n : nat), f n y.

  Definition subset (set1 set2 : set) : Prop := forall (a : A), set1 a -> set2 a.

  Definition equiv (set1 set2 : set) : Prop := forall (a : A), set1 a -> set2 a /\ set2 a -> set1 a.

  Hint Unfold singleton empty union subset set_minus indexed_union.

  Instance Set_equiv : Equivalence equiv.
  Proof with auto.
    split.
    + unfold Reflexive.
      intros. unfold equiv. auto.
    + unfold Symmetric.
      intros. unfold equiv. auto.
    + unfold Transitive.
      intros. unfold equiv. auto.
      Qed.

  Instance union_m : 
    Proper (equiv ==> equiv ==> equiv) union.
  Proof with auto.
    unfold Proper.
    unfold respectful.
    intros.
    unfold equiv in *.
    intros.
    apply H1.
  Qed.

  Add Morphism union with signature
    equiv ++> equiv ++> equiv as union_s_m.
  Proof. 
   apply union_m.
  Qed.

End Sets.

Add Parametric Morphism (A : Type) : (@union A) with signature
  @equiv A ++> @equiv A ++> @equiv A as union_s_m_x.
  Proof.
  intros.
  apply union_m. auto. auto.
  Qed.
  