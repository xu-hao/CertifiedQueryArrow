Require Import  Utils Algebra.SetoidCat Algebra.Monad.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import List.

Open Scope type_scope.

Section Cont.

  Variable (R : Type) (SR : Setoid R).

  Definition cont0 {A} (SA : Setoid A) := existT Setoid ((SA ~~> SR) ~> SR) ((SA ~~> SR) ~~> SR).
  Definition cont {A} (SA : Setoid A) := projT2 (cont0 SA).

  Definition cont_bindE A B (SA : Setoid A) (SB : Setoid B) : cont SA ~> (SA ~~> cont SB) ~~> cont SB.
    refine (injF (fun a => injF (fun f => injF (fun c => a @ injF (fun a' => f @ a' @ c) _) _) _) _).
    repeat autounfold. intros. arrequiv.
    Unshelve.
    repeat autounfold. intros. apply eval_Proper. reflexivity. arrequiv.
    repeat autounfold. intros. arrequiv.  apply eval_Proper. reflexivity. arrequiv.
    repeat autounfold. intros. rewrite H. reflexivity.
  Defined.

  Definition cont_retE A (SA : Setoid A) : SA ~> cont SA.
    refine (injF (fun a => injF (fun c => c @ a) _) _).
    repeat autounfold. intros. arrequiv.
    Unshelve.
    repeat autounfold. intros. rewrite H. reflexivity.
  Defined.

  Global Instance cont_Monad : @Monad (@cont0).
  Proof.
    exists cont_retE cont_bindE.
    intros. simpl. arrequiv.
    intros. simpl. arrequiv. apply eval_Proper. reflexivity. apply fun_ext. intros. simpl. reflexivity.
    intros. simpl. arrequiv. apply eval_Proper. reflexivity. arrequiv.
  Defined.

  Definition runCont {A} {SA : Setoid A} : cont SA ~> (SA ~~> SR) ~~> SR.
    refine (injF (fun a => injF (fun c => a @ c) _) _).
    repeat autounfold. intros. arrequiv.
    Unshelve.
    repeat autounfold. intros. rewrite H. reflexivity.
  Defined.


End Cont.
