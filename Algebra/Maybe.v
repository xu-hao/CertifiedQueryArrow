Require Import Algebra.PairUtils Utils Algebra.SetoidCat Algebra.Monad Algebra.Monoid Algebra.MonoidUtils Algebra.SetoidUtils Tactics.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import List.

Open Scope type_scope.

Instance optionS {A} (SA : Setoid A) : Setoid (option A) :=
  {
    equiv a b := match a, b with
                   | None, None => True
                   | Some a', Some b' => a' == b'
                   | _, _ => False
                 end
  }
.
Proof.
  split.
  autounfold. intros. destruct x. reflexivity. auto.
  autounfold. intros. destruct x, y. symmetry. auto. auto. auto. auto.
  autounfold. intros. destruct x, y, z. transitivity a0. auto. auto. auto. inversion H. auto. auto. inversion H.  auto. auto.
Defined.


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
  

Section MaybeMonad.

    Definition maybe A {SA : Setoid A} := option A.
    Definition maybeS {A} (SA : Setoid A) := optionS SA.


    Section Bind.
      Context
        {A B : Type}
        {SA : Setoid A}
        {SB : Setoid B}.

      Definition maybe_bind : (maybeS SA) ~> (SA ~~> maybeS SB) ~~> maybeS SB.

        simple refine (injF2 (fun a f =>
                                       caseMaybeS @ f @ None @ a
                                    ) _).
        Lemma maybe_bind_1 : Proper (equiv ==> equiv ==> equiv)
                                    (fun (a : option A) (f : SA ~> maybeS SB) => caseMaybeS @ f @ None @ a).
        Proof.
          repeat autounfold. intros. rewritesr. 
        Qed.
        apply maybe_bind_1.
      Defined.
    End Bind.

    Section Ret.
            Context
        {A : Type}
        {SA : Setoid A}.

      Definition maybe_ret : SA ~> maybeS SA := SomeS.
    End Ret.

    Instance maybe_Monad : @Monad maybe (@maybeS).
    Proof.
      exists (@maybe_ret) (@maybe_bind) .
      intros. simpl. destruct f. simpl. destruct (x a). reflexivity.  auto.
      intros. simpl. destruct a. simpl. reflexivity. simpl. auto.
      intros. simpl. destruct f, g. simpl. destruct a. simpl. destruct (x a). simpl. destruct (x0 b). reflexivity. auto. simpl. auto. simpl. auto.
    Defined.

  End MaybeMonad.
