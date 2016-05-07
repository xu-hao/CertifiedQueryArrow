Require Import Algebra.PairUtils Utils Algebra.SetoidCat Algebra.Monad Algebra.Monoid Algebra.MonoidUtils Algebra.SetoidUtils.

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


Section MaybeMonad.

    Definition maybe A {SA : Setoid A} := option A.
    Definition maybeS {A} (SA : Setoid A) := optionS SA.


    Section Bind.
      Context
        {A B : Type}
        {SA : Setoid A}
        {SB : Setoid B}.

      Definition maybe_bind : (maybeS SA) ~> (SA ~~> maybeS SB) ~~> maybeS SB.

        simple refine (injF (fun a => injF (fun f =>
                                       match a with
                                         | None => None
                                         | Some a' => f @ a'
                                       end
                                    ) _) _).
        Lemma maybe_bind_1 : forall a, Proper (equiv ==> equiv)
     (fun f : SA ~> maybeS SB =>
      match a with
      | Some a' => f @ a'
      | None => None
      end).
        Proof.
          repeat autounfold. intros. destruct a. rewrite H. reflexivity. reflexivity.
        Qed.
        apply maybe_bind_1.
        
        Lemma maybe_bind_2: forall pr, Proper (equiv ==> equiv)
                                         (fun a : option A =>
                                            injF
                                              (fun f : SA ~> maybeS SB =>
                                                 match a with
                                                   | Some a' => f @ a'
                                                   | None => None
                                                 end) (pr a)).
        Proof.
          repeat autounfold. intros. arrequiv. destruct x,y. simpl in H. assert (a @ a0 == a @ a1). rewrite H. reflexivity. generalize (a @ a0) (a @ a1) H0. intros. destruct o, o0. auto. inversion H1. inversion H1. auto. inversion H. inversion H. auto.
        Qed.
        apply maybe_bind_2.
      Defined.
    End Bind.
    Section Ret.
            Context
        {A : Type}
        {SA : Setoid A}.

      Definition maybe_ret : SA ~> maybeS SA.
        simple refine (injF Some _).
        Lemma maybe_ret_1 : Proper (equiv ==> equiv) Some.
          repeat autounfold. intros. simpl. auto.
        Qed.
        apply maybe_ret_1.
      Defined.
    End Ret.

     Instance maybe_Monad : @Monad maybe (@maybeS).
    Proof.
      exists (@maybe_ret) (@maybe_bind) .
      intros. simpl. destruct f. simpl. destruct (x a). reflexivity.  auto.
      intros. simpl. destruct a. reflexivity. auto.
      intros. simpl. destruct f, g. simpl. destruct a. destruct (x a). destruct (x0 b). reflexivity. auto. auto. auto.
    Defined.

  End MaybeMonad.
