Require Import  Utils Algebra.SetoidCat Algebra.Monad Algebra.Monoid Algebra.Alternative Algebra.SetoidUtils Algebra.Applicative Algebra.Functor Algebra.MonoidUtils Algebra.FoldableFunctor Algebra.Traversable Tactics.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import List.

Open Scope type_scope.



Section ContT.

  Context
    {R : Type} (SR : Setoid R)
    {m : forall A, Setoid A -> Type}
    (mS : forall A (SA : Setoid A), Setoid (m A SA))
  .


  Definition contT A {SA : Setoid A} := (SA ~~> mS _ SR) ~> mS _ SR.
  Definition contTS {A} (SA : Setoid A) := (SA ~~> mS _ SR) ~~> mS _ SR.

  Section Bind.
    Context A B (SA : Setoid A) (SB : Setoid B).
  Definition contT_bind  : contTS SA ~> (SA ~~> contTS SB) ~~> contTS SB.
    simple refine (injF (fun a => injF (fun f => injF (fun c => a @ injF (fun a' => f @ a' @ c) _) _) _) _).
    Lemma contT_bindE_1 : forall pr3 pr2 pr1, Proper (equiv ==> equiv)
     (fun a : (SA ~~> mS _ SR) ~> mS _ SR =>
      injF
        (fun f : SA ~> contTS SB =>
         injF
           (fun c : SB ~> mS _ SR => a @ injF (fun a' : A => f @ a' @ c) (pr3 f c))
           (pr2 a f)) (pr1 a)).
    repeat autounfold. intros. arrequiv.
  Qed.

  Lemma contT_bindE_2 : forall   (x : (SA ~~> mS _ SR) ~> mS _ SR) pr3 pr2 ,
   Proper (equiv ==> equiv)
     (fun f : SA ~> contTS SB =>
      injF
        (fun c : SB ~> mS _ SR => x @ injF (fun a' : A => f @ a' @ c) (pr3 f c))
        (pr2 f)).
    repeat autounfold. intros. arrequiv. apply eval_Proper. reflexivity. arrequiv.
  Qed.

  Lemma proper_f_x_a : forall A B C (SA : Setoid A) (SB : Setoid B) (SC : Setoid C) (x : SA ~> SB ~~> SC) (x0 : B),
                          Proper (equiv ==> equiv) (fun a' : A => x @ a' @ x0).
    repeat autounfold. intros. rewrite H. reflexivity.
  Qed.

  Lemma contT_bindE_3 : forall    (x : (SA ~~> mS _ SR) ~> mS _ SR) (x0 : SA ~> contTS SB) pr,
   Proper (equiv ==> equiv)
     (fun c : SB ~> mS _ SR =>
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
    Definition contT_ret  : SA ~> contTS SA.
      simple refine (injF (fun a => injF (fun c => c @ a) _) _).
      Lemma proper_x_a : forall A B (SA : Setoid A) (SB : Setoid B) (a : A), Proper (equiv ==> equiv) (fun c : SA ~> SB => c @ a).
      Proof.
        repeat autounfold. intros. rewrite H. reflexivity.
      Qed.
      apply proper_x_a.
      Lemma contT_retE_1 : Proper (equiv ==> equiv)
                                  (fun a : A =>
                                     injF (fun c : SA ~> mS R SR => c @ a)
                                          (proper_x_a A (m R SR) SA (mS R SR) a)).
      Proof.
        repeat autounfold. intros. arrequiv.
      Qed.
      apply contT_retE_1.
    Defined.
  End Ret.

  Lemma contT_left_unit : forall (A B : Type) (SA : Setoid A) (SB : Setoid B) 
     (a : A) (f : SA ~> contTS SB),
   contT_bind A B SA SB @ (contT_ret A SA @ a) @ f == f @ a.
  Proof.
    intros. simpl. arrequiv.
  Qed.

  Lemma contT_associativity : forall (A B C  : Type) (SA : Setoid A) (SB : Setoid B) 
     (SC : Setoid C) (a : contT A)   (f : SA ~> contTS SB)
     (g : SB ~> contTS SC) 
     (pr : Proper (equiv ==> equiv) (fun b : A => contT_bind B C SB SC @ (f @ b) @ g))
     ,
   contT_bind B C SB SC @ (contT_bind A B SA SB @ a @ f) @ g ==
   contT_bind A C SA SC @ a @
               injF (fun b : A => contT_bind B C SB SC @ (f @ b) @ g) pr.
  Proof.
    intros. simpl. arrequiv.  apply eval_Proper. reflexivity. arrequiv.
  Qed.
  
  Lemma contT_right_unit : forall (A  : Type) (SA : Setoid A) 
     (a : contT A),
                             contT_bind A A SA SA @ a @ (contT_ret A SA) == a.
  Proof.
    
    intros. simpl. arrequiv.  apply eval_Proper. reflexivity. apply fun_ext. intros. simpl. reflexivity.
  Qed.
  Instance contT_Monad : @Monad (@contT) (@contTS).
  Proof.
    exists contT_ret contT_bind.
    apply contT_left_unit.
    apply contT_right_unit.
    apply contT_associativity.
  Defined.

  Section RunContT.
    Context {A} {SA : Setoid A}.
    Definition contT_runContT  : contTS SA ~> (SA ~~> mS _ SR) ~~> mS _ SR.
    simple refine (injF (fun a => injF (eval a) _) _).
    Lemma proper_evala : forall A B (SA : Setoid A ) (SB : Setoid B) (a : SA  ~> SB), Proper (equiv ==> equiv) (eval a).
    Proof.
      repeat autounfold. intros. rewrite H. reflexivity.
    Qed.
    apply proper_evala.
    Lemma proper_evalx  : forall (A B : Type) (SA : Setoid A) (SB : Setoid B)  pr,    Proper (equiv ==> equiv)
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
    {R_Monoid : @Monoid _ SR}
    {alt : @Alternative m mS}.
  
  
  Definition contT_empty {A} {SA : Setoid A} : (contT A) := constS _ @ empty.

  Existing Instance alternative_Monoid.
  Definition contT_append {A} {SA : Setoid A} : contTS SA ~> contTS SA ~~> contTS SA.
    refine (injF3 (fun a b c =>
                     ((contT_runContT @ a @ c)) <|> (contT_runContT @ b @ c)) _).
    Lemma contT_append_1 : forall {A} {SA : Setoid A}, Proper (equiv ==> equiv ==> equiv ==> equiv)
     (fun (a b : contT A) (c : SA ~> mS _ SR) =>
      contT_runContT @ a @ c <|> contT_runContT @ b @ c).
  Proof.
    intros. solve_proper. 
  Qed.
  apply contT_append_1.
  Defined.

  Instance contT_Alternative : @Alternative (@contT) (@contTS).
  Proof.
    exists (@contT_empty) (@contT_append).
    intros. simpl. arrequiv. apply left_unit_alt. 

    intros. simpl. arrequiv. apply right_unit_alt.
    
    intros. simpl.  arrequiv.  apply associativity_alt. 
  Defined.

  Instance contT_A_Monoid A AS: @Monoid (contT A) (contTS AS) := @alternative_Monoid (@contT) (@contTS) _ A _.

  Lemma contT_left_distributivity :
    forall A B (SA : Setoid A) (SB : Setoid B)
           (a a2 : contT A ) (f : SA ~> contTS SB),
      (mappend @ a @ a2) >>= f == mappend @ (a >>= f) @ (a2 >>= f).
  Proof.
    intros. simpl. arrequiv.
  Qed.


  Context
    {mnd : @Monad m mS}.
  Existing Instance monad_Applicative.
  Existing Instance monadFunctor.

  Lemma contT_ret_injective :
    injective SR (mS _ SR) (@ret m _ _ _ _) -> injective SR (contTS SR) (contT_ret R SR).
  Proof.
    unfold injective. simpl.  unfold arrEquiv. simpl.  intros. apply H. apply H0. 
  Qed.
  
  Section Lift.
    Context {A} {SA : Setoid A}.
    Definition contT_lift : mS  _ SA ~> contTS SA := bind.
    
  End Lift.
  
End ContT.

Section Utils.
  Context
    {m mS} {mnd : @Monad m mS} {R} {SR : Setoid R}.
  
  Definition lift  {A} {SA : Setoid A} : mS _ SA ~> contTS SR mS SA := contT_lift SR mS.

  Definition runContT {A} {SA : Setoid A} : contTS SR mS SA ~> (SA ~~> mS _ SR) ~~> mS _ SR := contT_runContT SR mS.


  Definition finish {A} {SA : Setoid A} : SR ~> (contTS SR mS SA).
    simple refine (injF2 (fun r c => ret @ r) _).

    apply mS.
    exact mnd.
    

    Lemma finish_1 : forall {m mS} {mnd : @Monad m mS} {R} {SR : Setoid R} {A} {SA : Setoid A}, Proper (equiv ==> equiv ==> equiv)
                            (fun (r : R) (_ : SA ~> mS _ SR) => ret @ r).
    Proof.
      repeat autounfold. intros. rewrite H. reflexivity.
    Qed.
  
    apply finish_1.
  Defined.
End Utils.

