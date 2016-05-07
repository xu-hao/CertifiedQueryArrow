Require Import Algebra.PairUtils Utils Algebra.SetoidCat Algebra.Monad Algebra.Monoid Algebra.MonoidUtils Algebra.SetoidUtils Algebra.Functor.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import List.

Open Scope type_scope.

Section Store.
  Context {S : Type} (SS : Setoid S).

  Definition store A {SA : Setoid A} := SS ~> (SA ~*~ SS).
  Definition storeS {A} (SA : Setoid A) := SS ~~> (SA ~*~ SS).

  Section Bind.
    Context {A B} {SA : Setoid A} {SB : Setoid B}.
    Definition store_bind  : storeS SA ~> (SA ~~> storeS SB) ~~> storeS SB :=
      flipS @ ((flipS @ compS) ∘ uncurryS).
  End Bind.

  Section Ret.
    Context {A} {SA : Setoid A}.
    Definition store_ret  : SA ~> storeS SA := curryS @ idS.
  End Ret.

  Lemma store_ret_injective A (SA : Setoid A) (s : S) : injective SA (storeS SA) (@store_ret A SA).
  Proof.
    unfold injective. simpl. unfold arrEquiv. simpl. intros. apply H. apply s.
  Qed.
  
  Instance store_Monad : @Monad (@store) (@storeS).
  Proof.
    exists (@store_ret) (@store_bind).
    intros. simpl. arrequiv.
    intros. simpl. arrequiv. destruct (a @ a0). split. reflexivity. reflexivity.
    intros. simpl. arrequiv. 
  Defined.

  Instance store_Monoid A (SA : Setoid A) (A_Monoid : @Monoid _ SA): @Monoid _ (storeS SA) := monad_Monoid _ _ _.

  Section Get.
    Definition store_get : store S := idS &&& idS.
  End Get.


  Section Put.
    Definition store_put : SS ~> storeS unitS := flipS @ (constS _ @ ((constS _ @ tt) &&& idS)).
  End Put.

End Store.


Definition get {S SS} : store SS S := store_get SS.

Definition put {S} {SS : Setoid S} : SS ~> storeS SS unitS := store_put SS.

Section Utils.
  Context
    {S} {SS : Setoid S}.

  Existing Instance store_Monad.
  

  Lemma get_put : forall  (a : S),  put @ a >> get == put @ a >> ret @ a.
  Proof.
    intros. simpl. arrequiv.  split. reflexivity. reflexivity.  
  Qed.

  Lemma put_put : forall (a b : S), put @ a >> put @ b == (put @ b : store SS unit).
  Proof.
    intros. simpl. arrequiv. split. reflexivity. reflexivity. 
  Qed.

  Lemma get_get : get >> get == get.
  Proof.
    intros. simpl. arrequiv. split. reflexivity. reflexivity. 
  Qed.

  Lemma put_get : forall  (a : S),  get >>= put  == ret @ tt.
  Proof.
    intros. simpl. arrequiv.  split. reflexivity. reflexivity.  
  Qed.
  
End Utils.
