Require Import  Algebra.SetoidCat Algebra.SetoidCat.SetoidUtils Algebra.Functor Algebra.Applicative Tactics Algebra.SetoidCat.PairUtils Algebra.Monad.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Ltac bindproper := apply bind_Proper; [ try reflexivity; try auto | arrequiv ].

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

Lemma compM_associativity : forall {A} {B} {C} {D} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {DS : Setoid D} {m mS} {mnd : @Monad m mS} (f : AS ~> mS _ BS) (g : BS ~> mS _ CS) (h : CS ~> mS _ DS),
                             f >=> g >=> h == f >=> (g >=> h).
Proof.
  intros. simpl_equiv. normalize_monad. reflexivity.
Qed.

Lemma comp_compM : forall {A} {B} {C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {m mS} {mnd : @Monad m mS} (f : AS ~> BS) (g : BS ~> mS _ CS),
                             g ∘ f == ret ∘ f >=> g.
Proof.
  intros. simpl_equiv. normalize_monad. reflexivity.
Qed.

