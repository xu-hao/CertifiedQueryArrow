Require Import  Utils Algebra.SetoidCat Algebra.Monad Algebra.Monoid Algebra.Alternative.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import List.

Open Scope type_scope.

Section ContT.

  Context
    {R : Type} (SR : Setoid R)
    (m0 : forall {A}, Setoid A -> {B : Type & Setoid B})
    {mnd : @Monad (@m0)}
  .

  Definition contT0 {A} (SA : Setoid A) := existT Setoid ((SA ~~> m SR) ~> m SR) ((SA ~~> m SR) ~~> m SR).
  Definition contT {A} (SA : Setoid A) := projT2 (contT0 SA).

  Section Bind.
    Context A B (SA : Setoid A) (SB : Setoid B).
  Definition contT_bindE  : contT SA ~> (SA ~~> contT SB) ~~> contT SB.
    simple refine (injF (fun a => injF (fun f => injF (fun c => a @ injF (fun a' => f @ a' @ c) _) _) _) _).
    Lemma contT_bindE_1 : forall pr3 pr2 pr1, properF
     (fun a : (SA ~~> m SR) ~> m SR =>
      injF
        (fun f : SA ~> contT SB =>
         injF
           (fun c : SB ~> m SR => a @ injF (fun a' : A => f @ a' @ c) (pr3 f c))
           (pr2 a f)) (pr1 a)).
    repeat autounfold. intros. arrequiv.
  Qed.

  Lemma contT_bindE_2 : forall   (x : (SA ~~> m SR) ~> m SR) pr3 pr2 ,
   properF
     (fun f : SA ~> contT SB =>
      injF
        (fun c : SB ~> m SR => x @ injF (fun a' : A => f @ a' @ c) (pr3 f c))
        (pr2 f)).
    repeat autounfold. intros. arrequiv. apply eval_Proper. reflexivity. arrequiv.
  Qed.

  Lemma proper_f_x_a : forall A B C (SA : Setoid A) (SB : Setoid B) (SC : Setoid C) (x : SA ~> SB ~~> SC) (x0 : B),
                          properF (fun a' : A => x @ a' @ x0).
    repeat autounfold. intros. rewrite H. reflexivity.
  Qed.

  Lemma contT_bindE_3 : forall    (x : (SA ~~> m SR) ~> m SR) (x0 : SA ~> contT SB) pr,
   properF
     (fun c : SB ~> m SR =>
        x @ injF (fun a' : A => x0 @ a' @ c) (pr c)).
    repeat autounfold. intros.  apply eval_Proper. reflexivity. arrequiv.
  Qed.
    intros. apply proper_f_x_a.
    apply contT_bindE_3.
    apply contT_bindE_2.
    apply contT_bindE_1.
  Defined.
End Bind.

  Section Ret.
    Context A (SA : Setoid A).
  Definition contT_retE  : SA ~> contT SA.
    simple refine (injF (fun a => injF (fun c => c @ a) _) _).
    Lemma proper_x_a : forall A B (SA : Setoid A) (SB : Setoid B) (a : A), properF (fun c : SA ~> SB => c @ a).
    Proof.
      repeat autounfold. intros. rewrite H. reflexivity.
    Qed.
    apply proper_x_a.
Lemma contT_retE_1 : properF
     (fun a : A =>
      injF (fun c : SA ~> m SR => c @ a)
           (proper_x_a A (projT1 (m0 R SR)) SA (m SR) a)).
Proof.
  repeat autounfold. intros. arrequiv.
Qed.
apply contT_retE_1.
  Defined.
End Ret.

  Lemma contT_left_unit : forall (A B : Type) (SA : Setoid A) (SB : Setoid B) 
     (a : A) (f : SA ~> projT2 (contT0 SB)),
   contT_bindE A B SA SB @ (contT_retE A SA @ a) @ f == f @ a.
  Proof.
    intros. simpl. arrequiv.
  Qed.

  Lemma contT_associativity : forall (A B C D : Type) (SA : Setoid A) (SB : Setoid B) 
     (SC : Setoid C) (SD : Setoid D) (f : SA ~> projT2 (contT0 SB))
     (g : SB ~> projT2 (contT0 SC)) (h : SC ~> projT2 (contT0 SD))
     (pr : properF (fun b : B => contT_bindE C D SC SD @ (g @ b) @ h))
     (a : A),
   contT_bindE C D SC SD @ (contT_bindE B C SB SC @ (f @ a) @ g) @ h ==
   contT_bindE B D SB SD @ (f @ a) @
               injF (fun b : B => contT_bindE C D SC SD @ (g @ b) @ h) pr.
  Proof.
    intros. simpl. arrequiv.  apply eval_Proper. reflexivity. arrequiv.
  Qed.
  
  Lemma contT_right_unit : forall (A  : Type) (SA : Setoid A) 
     (a : projT1 (contT0 SA)),
                             contT_bindE A A SA SA @ a @ (contT_retE A SA) == a.
  Proof.
    
    intros. simpl. arrequiv.  apply eval_Proper. reflexivity. apply fun_ext. intros. simpl. reflexivity.
  Qed.
  
  Global Instance contT_Monad : @Monad (@contT0).
  Proof.
    exists contT_retE contT_bindE.
    apply contT_left_unit.
    apply contT_right_unit.
    apply contT_associativity.
  Defined.

  Section RunContT.
    Context {A} {SA : Setoid A}.
    Definition contT_runContT  : contT SA ~> (SA ~~> @m _ mnd _ SR) ~~> @m _ mnd _ SR.
    simple refine (injF (fun a => injF (eval a) _) _).
    Lemma proper_evala : forall A B (SA : Setoid A ) (SB : Setoid B) (a : SA  ~> SB), properF (eval a).
    Proof.
      repeat autounfold. intros. rewrite H. reflexivity.
    Qed.
    apply proper_evala.
    Lemma proper_evalx  : forall (A B : Type) (SA : Setoid A) (SB : Setoid B)  pr,    properF
     (fun a : SA ~> SB =>
      injF (eval a)
           (pr a)).
      Proof.
    repeat autounfold. intros. arrequiv.

      Qed.
      apply proper_evalx.

    Defined.
  End RunContT.
  
  Context
    {R_Monoid : @Monoid _ SR}.

  Notation "a >>= b" := (bind @ a @ b) (at level 50, left associativity).
  Definition contT_empty {A} {SA : Setoid A} : & (contT SA).
    refine (injF (fun _ => ret @ mempty) _).


    apply proper_constax.
  Defined.

  
 
  
  Definition contT_append {A} {SA : Setoid A} : contT SA ~> contT SA ~~> contT SA.
    refine (injF (fun a =>
                    injF (fun b =>
                            injF (fun c =>
                                    (mappend <$> (contT_runContT @ a @ c)) <*> (contT_runContT @ b @ c)) _) _) _).
    Lemma contT_append_1 : forall {A} {SA : Setoid A} pr2 pr1, properF
     (fun a : projT1 (contT0 SA) =>
      injF
        (fun b : projT1 (contT0 SA) =>
         injF
           (fun c : SA ~> m SR =>
            mappend <$> contT_runContT @ a @ c <*> contT_runContT @ b @ c) 
           (pr2 a b)) (pr1 a)).
  Proof.
    repeat autounfold. intros. arrequiv.
  Qed.
  apply contT_append_1.
    Unshelve.
     Lemma contT_append_2 : forall {A} {SA : Setoid A} (x : projT1 (contT0 SA)) pr2,
   properF
     (fun b : projT1 (contT0 SA) =>
      injF
        (fun c : SA ~> m SR =>
         mappend <$> contT_runContT @ x @ c <*> contT_runContT @ b @ c) 
        (pr2 b)).
  Proof.
    repeat autounfold. intros. arrequiv. bindproper. 
  Qed.
  intros. apply contT_append_2.
    Lemma contT_append_3 : forall A (SA : Setoid A) (x x0 : projT1 (contT0 SA)),
   properF
     (fun c : SA ~> m SR =>
      mappend <$> contT_runContT @ x @ c <*> contT_runContT @ x0 @ c).
  Proof.
    repeat autounfold. intros.     rewrite H. reflexivity.
  Qed.
  intros. apply contT_append_3.
  Defined.

Global Instance contT_Alternative : @Alternative (@contT0).
  Proof.
    exists (@contT_empty) (@contT_append).
    intros. simpl. arrequiv. rewrite left_unit. simpl. rewrite left_unit. simpl. apply right_unit_equiv.  simpl. arrequiv.  rewrite left_unit_monoid. reflexivity.

    intros. simpl. arrequiv. rewrite associativity_2. apply right_unit_equiv. simpl.   arrequiv. rewrite left_unit. simpl. rewrite left_unit. simpl. rewrite right_unit_monoid. reflexivity.
    intros. simpl.  arrequiv.  repeat rewrite associativity_2.  bindproper. simpl. arrequiv. repeat rewrite left_unit. simpl. repeat rewrite associativity_2. bindproper. simpl. arrequiv. repeat rewrite left_unit. simpl. rewrite left_unit. simpl. rewrite associativity_2. bindproper. simpl.  arrequiv. repeat rewrite left_unit. simpl. rewrite associativity_monoid. reflexivity.
  Defined.

  Lemma contT_left_distributivity :
    forall A B (SA : Setoid A) (SB : Setoid B)
           (a a2 : projT1 (contT0 SA)) (f : SA ~> contT SB),
      (a <|> a2) >>= f == (a >>= f) <|> (a2 >>= f).
  Proof.
    intros. simpl. arrequiv.
  Qed.



  Section Lift.
    Context {A} {SA : Setoid A}.
    Definition contT_lift : @m _ mnd _ SA ~> contT SA := bind.
    
  End Lift.
  
End ContT.

Definition lift {m0} {mnd : @Monad m0} {R} {SR : Setoid R} {A} {SA : Setoid A} : m SA ~> contT SR m0 SA := contT_lift SR m0.

Definition runContT {m0} {mnd : @Monad m0} {R} {SR : Setoid R} {A} {SA : Setoid A} : contT SR m0 SA ~> (SA ~~> m SR) ~~> m SR := contT_runContT SR m0.