Require Import Algebra.SetoidCat.PairUtils Algebra.Utils Algebra.SetoidCat Algebra.Monad Algebra.Monoid Algebra.SetoidCat.SetoidUtils Tactics.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Open Scope type_scope.

Definition maybe_equiv {A} {SA : Setoid A} (a b : option A) := match a, b with
                   | None, None => True
                   | Some a', Some b' => a' == b'
                   | _, _ => False
                                                    end.

Instance maybe_equiv_Equivalence {A} {SA : Setoid A} : Equivalence (@maybe_equiv A SA).
Proof.
  split.
  autounfold. intros. destruct x. simpl. reflexivity. auto. reflexivity.  
  autounfold. intros. destruct x, y. simpl in *. symmetry. auto. simpl in *. auto. simpl in *. auto. simpl in *. auto.
  autounfold. intros. destruct x, y, z. simpl in *. transitivity a0. auto. auto. simpl in *. auto. simpl in *. inversion H. simpl in *. auto. simpl in *. auto. simpl in *. inversion H.  simpl in *. auto. simpl in *. auto.
Qed.

Instance optionS {A} (SA : Setoid A) : Setoid (option A) :=
  {
    equiv := maybe_equiv
  }.


Instance Some_Proper A (AS : Setoid A) : Proper (equiv ==> equiv) (@Some A).
Proof.
  autounfold. intros. simpl. auto.
Qed.

Definition SomeS {A} {AS : Setoid A} : AS ~> optionS AS := injF Some _.

Definition caseMaybe {A B} {AS : Setoid A} {BS : Setoid B} (some : AS ~> BS) (none : B) val1 : B :=
  match val1 with
    | Some n => some @ n
    | None => none
  end
.

Instance caseMaybe_Proper A B AS BS : Proper (equiv ==> equiv ==> equiv ==> equiv) (@caseMaybe A B AS BS).
Proof.
  autounfold. intros. unfold caseMaybe. matchequiv. simpl in H1. rewritesr.  auto. 
Qed.

Definition caseMaybeS {A B AS BS} := injF3 (@caseMaybe A B AS BS) _.

Lemma maybe_case : forall {A} (a : option A), a = None \/ exists b, a = Some b.
Proof.
  intros. destruct a.
  right. exists a. auto.
  left. auto.
Qed.
  
Ltac destruct_maybe a :=
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let x := fresh "x" in
  destruct (maybe_case a) as [H1 | H2] ; [
      simpl in *; rewrite H1 in * |
      destruct H2 as [x H2]; simpl in *; rewrite H2 in *].

Definition maybe A {SA : Setoid A} := option A.
Definition maybeS {A} (SA : Setoid A) := optionS SA.

Lemma maybe_equiv_dec : forall {A} {AS :Setoid A} (r1 r2 : maybe A) (equiv_dec : forall a1 a2 : A, {a1 == a2} + {~a1 == a2}), {r1 == r2} + {~r1 == r2}.
Proof.
  intros.  destruct r1 as [n|], r2 as [n0 |].
  - destruct (equiv_dec n n0).
    + left. rewrite e. reflexivity. 
    + right. intro. apply n1. auto. 
  - right. intro. inversion H.
  - right. intro. inversion H.
  - left. reflexivity.
Defined.

