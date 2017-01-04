Require Import  Algebra.SetoidCat Algebra.SetoidCat.SetoidUtils Algebra.Tactics Algebra.SetoidCat.PairUtils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Open Scope type_scope.



Section Monad.


  Context
    {m : forall A, Setoid A -> Type}
    {mS : forall A (AS : Setoid A), Setoid (m A AS)}.

  Class Monad : Type :=
    {
      
      ret : forall {A} {SA : Setoid A}, SA ~> mS _ SA ;
      bind : forall {A B} {SA : Setoid A} {SB : Setoid B}, mS _ SA ~> (SA ~~> mS _ SB ) ~~> mS _ SB ;

      left_unit :
        forall
          A B (SA : Setoid A) (SB : Setoid B)
        (a : A) (f : SA ~> mS _ SB),
          bind @ (ret @ a) @ f == f @ a;


      right_unit :
        forall
          A (SA : Setoid A)
          (a : m A _),
          bind @ a @ ret == a;

      associativity :
        forall
        A  B C
        (SA : Setoid A)        (SB : Setoid B)        (SC : Setoid C)
          (a : m A _ ) (f : SA ~> mS _ SB )(g : SB ~> mS _ SC )  pr,
            bind @ (bind @ a @ f) @ g == bind @ a @ injF (fun b => bind @ (f @ b) @ g) pr
    }.

  Hint Unfold eval bind ret projF.
  Notation "a >>= f" := (bind @ a @ f) (at level 50, left associativity).

  Lemma right_unit_equiv :
    forall (mnd : Monad) A (SA : Setoid A)
           (a : m A _) (f : SA ~> mS _ SA),
      f == ret ->
      a >>= f == a.

  Proof.
    intros. rewrite H. apply right_unit.
  Qed.

  Lemma right_unit_eta : forall
       (mnd : Monad)   A (SA : Setoid A)
        (a : m A _) pr,
        a >>= injF (fun a' => ret @ a') pr == a.
  Proof.
    intros. apply right_unit_equiv. apply fun_ext. intros. reflexivity. 
  Qed.

  Lemma associativity_2 :
        forall
          A B C D
          (SA : Setoid A)        (SB : Setoid B)        (SC : Setoid C)        (SD : Setoid D) (mnd : Monad)
          (f : SA ~> mS _ SB ) (g : SB ~> mS _ SC )(h : SC ~> mS _ SD ) pr a,
          f @ a >>=  g >>=  h == f @ a >>= injF (fun b => g @ b >>= @ h) pr.
  Proof.
    intros. apply associativity.
  Qed.



  Let ret1 {mnd : Monad} {A} {SA : Setoid A} (a : A) : m A _ := ret @ a.
  Let bind1 {mnd : Monad} {A B} {SA : Setoid A} {SB : Setoid B} (a : m A _) (f : SA ~> mS _ SB) : m B _ := bind @ a @ f.

Global Instance ret_Proper {mnd : Monad} A (SA : Setoid A) : Proper (equiv ==> equiv) (@ret1 mnd A SA).
Proof.
  unfold ret1. solve_proper.
Qed.

Global Instance bind_Proper {mnd : Monad} A B (SA : Setoid A) (SB : Setoid B) : Proper (equiv ==> equiv ==> equiv) (@bind1 mnd A B SA SB).
Proof.
  unfold bind1. solve_proper. 
Qed.


Section compM.
  Context
     {mnd : Monad} {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C}  .

  Definition _compM (f : SA ~> mS _ SB ) (g : SB ~> mS _ SC) :
    SA ~> mS _ SC.
    refine (injF (fun a => f @ a >>= g) _).
    Lemma _compM_1 :forall (f : SA ~> mS _ SB ) (g : SB ~> mS _ SC),  Proper (equiv ==> equiv) (fun a => f @ a >>= g).
    Proof.
      unfold Proper, respectful. intros. rewrite H. reflexivity.
    Qed.
    apply _compM_1.
  Defined.

  
  Definition compM  : (SA ~~> mS _ SB ) ~> (SB ~~> mS _ SC) ~~> (SA ~~> mS _ SC).
    refine (injF2 _compM _).
    Lemma compM_1 :  Proper (equiv==>equiv==>equiv) _compM.
    Proof.
      unfold Proper, respectful. intros. unfold _compM. arrequiv. rewritesr. 
    Qed.
    apply compM_1.
  Defined.
End compM.

Notation "f >=> g" := (compM @ f @ g) (at level 50, left associativity).

Hint Unfold compM.
Lemma right_unit_comp :
  forall (mnd : Monad) A B (SA : Setoid A) (SB : Setoid B)
         (f : SA ~> mS _ SB),
    compM @ f @ ret == f.
Proof.
  intros. simpl. arrequiv. apply right_unit.
Qed.

Lemma right_unit_comp_equiv :
  forall (mnd : Monad) A B (SA : Setoid A) (SB : Setoid B)
         (f : SA ~> mS _ SB) (g : SB ~> mS _ SB),
    g == ret ->
    compM @ f @ g == f.
Proof.
  intros. simpl. arrequiv. apply right_unit_equiv. auto.
Qed.

  
Lemma associativity_comp :
  forall
    (mnd : Monad) A B C D
    (SA : Setoid A)        (SB : Setoid B)        (SC : Setoid C)        (SD : Setoid D)
    (f : SA ~> mS _ SB ) (g : SB ~> mS _ SC )(h : SC ~> mS _ SD ) ,
    f  >=>  g >=>  h == f  >=> (g >=> h).
Proof.
  intros. simpl. arrequiv. apply associativity.
Qed.


Lemma associativity_compM :
  forall
    (mnd : Monad) B C D
    (SB : Setoid B)        (SC : Setoid C)        (SD : Setoid D) 
    (a : m B _) (g : SB ~> mS _ SC )(h : SC ~> mS _ SD ) ,
    a  >>=  g >>=  h == a  >>= (g >=> h).
Proof.
  intros. apply associativity.
Qed.


End Monad.

Notation "a >>= b" := (bind @ a @ b) (at level 50, left associativity).
Notation "f >=> g" := (compM @ f @ g) (at level 50, left associativity).


