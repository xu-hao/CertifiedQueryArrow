Require Import Algebra.SetoidCat.PairUtils Algebra.Utils Algebra.SetoidCat Algebra.Monad Algebra.Monoid SetoidUtils Tactics Algebra.SetoidCat.MaybeUtils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Open Scope type_scope.


Section MaybeMonad.


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
      intros. simpl. destruct f. simpl. destruct (x a). reflexivity.  reflexivity. 
      intros. simpl. destruct a. simpl. reflexivity. simpl. auto.
      intros. simpl. destruct f, g. simpl. destruct a. simpl. destruct (x a). simpl. destruct (x0 b). reflexivity. reflexivity. simpl. auto. simpl.  auto.
    Defined.

  End MaybeMonad.
