Require Import Utils Algebra.SetoidCat Algebra.SetoidUtils Algebra.Functor Algebra.Applicative Tactics Algebra.SetoidCat.PairUtils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import List.

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

Ltac bindproper := apply bind_Proper; [ try reflexivity; try auto | arrequiv ].

Notation "a >>= b" := (bind @ a @ b) (at level 50, left associativity).
Notation "f >=> g" := (compM @ f @ g) (at level 50, left associativity).

Section Utils.
  Context
    {m mS} {mnd : @Monad m mS} {A B C} {SA : Setoid A} {SB : Setoid B} {SC : Setoid C}.

  Definition monad_fmap  : (SA ~~> SB) ~> (mS _ SA ~~> mS _ SB).
    simple refine (injF2 (fun f ma => ma >>= ret ∘ f ) _).
    apply mS.
    exact mnd.
    exact mnd.
    Lemma fmap_1 : Proper (equiv ==> equiv ==> equiv)
                          (fun (f : SA ~> SB)  (ma : m A _) =>
                             ma >>= ret ∘ f).
    Proof.
      
      repeat autounfold.  intros. bindproper. rewritesr.
    Qed.
    apply fmap_1.
  Defined.

  Definition monad_prod  : mS _ SA ~> mS _ SB ~~> mS _ (SA ~*~ SB).
    simple refine (injF2 (fun ma mb => ma >>= injF (fun a => mb >>= injF (fun b => ret @ (a, b)) _) _) _).
    apply mS.
    exact mnd.
    apply mS.
    exact mnd.
    apply mS.
    exact mnd.
    Lemma monad_ap_1 :forall a : A, Proper (equiv ==> equiv) (fun b : B => ret @ (a, b)).
    Proof.
      intros. solve_proper.
    Qed.
    apply monad_ap_1.
    Lemma monad_ap_2 : forall mb, Proper (equiv ==> equiv)
     (fun a : A => mb >>= injF (fun b : B => ret @ (a, b)) (monad_ap_1 a)).
    Proof.
      autounfold. intros. bindproper.
    Qed.
    apply monad_ap_2.
    Lemma monad_ap_3 : Proper (equiv ==> equiv ==> equiv)
     (fun (ma : m A SA) (mb : m B SB) =>
      ma >>=
      injF
        (fun a : A => mb >>= injF (fun b : B => ret @ (a, b)) (monad_ap_1 a))
        (monad_ap_2 mb)).
    Proof.
      autounfold. intros. bindproper. 
    Qed.
    apply monad_ap_3.
  Defined.

  Definition andThen : mS _ SA ~> mS _ SB ~~> mS _ SB.
    simple refine (injF (fun (a : m A _) => (bind @ a) ∘ constS SA) _).
    exact mnd.
    Lemma andThen_1: Proper (equiv ==> equiv)
                            (fun (a : m A _)  =>
                               (bind @ a) ∘ constS SA : mS _ SB ~> mS _ SB).
    Proof.
      autounfold.  intros. rewritesr. 
    Qed.
    apply andThen_1.
  Defined.
  
End Utils.

Notation "a >> b" := (andThen @ a @ b) (at level 50, left associativity).

Ltac normalize_monad :=
  repeat (
      unfold ap, fmap, andThen, compM, _compM;
      normalizecomp;
      repeat (rewrite left_unit; normalize);
      repeat match goal with
               | |- ?a >>= ?f >>= ?g == _ => rewrite (associativity_compM _ _ _ _ _ _ _ a f g)
               | |- ?a >>= ?f >>= ?g >>= _ == _ => rewrite (associativity_compM _ _ _ _ _ _ _ a f g)
               | |- _ == ?a >>= ?f >>= ?g => rewrite (associativity_compM _ _ _ _ _ _ _ a f g)
               | |- _ == ?a >>= ?f >>= ?g >>= _ => rewrite (associativity_compM _ _ _ _ _ _ _ a f g)
             end             
    ).

Lemma ret_ret : forall t tS (mnd : @Monad t tS) A B C (SA : Setoid A) (SB : Setoid B) (SC : Setoid C) (a : t A _) (f : A -> B) (g : B -> C) pr pr2 pr3,
                    Proper (equiv==>equiv) f ->
                    Proper (equiv==>equiv) g ->
                    a >>= injF (fun a => ret @ f a) pr >>= injF (fun b => ret @ g b) pr2 == a >>= injF (fun a => ret @ g (f a)) pr3.

Proof.
  intros. normalize_monad. bindproper. normalize_monad. reflexivity.
Qed.

Section Instances.
Instance monadFunctor  {m mS} {mnd : @Monad m mS} : @Functor m mS.
Proof.
  exists (@monad_fmap m mS mnd).
  intros. simpl. arrequiv. normalize_monad. bindproper. simpl. arrequiv. unfold comp. rewrite left_unit. simpl. reflexivity.
  intros. simpl. arrequiv. rewrite right_unit_equiv. reflexivity. simpl. arrequiv.
Defined.

Instance monad_Applicative {m mS}{mnd : @Monad m mS} : @Applicative m mS _.
Proof.
  exists (ret @ tt) (@monad_prod m mS mnd ).
  intros. simpl. normalize_monad. rewrite right_unit_equiv. reflexivity. simpl. arrequiv. normalize_monad. reflexivity.
  intros. simpl. normalize_monad. rewrite right_unit_equiv. reflexivity. simpl. arrequiv. normalize_monad. reflexivity.
  intros. simpl. normalize_monad. bindproper. normalize_monad. bindproper. normalize_monad. bindproper. normalize_monad. reflexivity.
  intros. simpl. normalize_monad. bindproper. normalize_monad. bindproper. normalize_monad. reflexivity.
Defined.
End Instances.
