Require Import Algebra.Utils Algebra.SetoidCat Algebra.SetoidCat.PairUtils Algebra.Monad Algebra.Monoid Algebra.Traversable Algebra.FoldableFunctor Algebra.Functor SetoidUtils Algebra.Applicative Algebra.Alternative Tactics Algebra.SetoidCat.BoolUtils Algebra.Functor.Utils Algebra.SetoidCat.ListUtils Algebra.FoldableFunctor.List Algebra.Functor.List Algebra.Monoid.List Algebra.Functor.Compose Algebra.Applicative.Compose.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Import ListNotations.



Section Generic.



  Definition l A {AS : Setoid A} := list A.
  Instance lS {A} (AS : Setoid A) : Setoid (l A) := listS AS.


  Existing Instance list_Foldable.
  Existing Instance listFunctor.
  Existing Instance list_A_Monoid.

  
  Definition pairS {A B} {AS : Setoid A} {BS : Setoid B} : AS ~>  BS ~~> AS ~*~ BS := curryS @ idS.

  Definition listProd0 {A B} {AS : Setoid A} {BS : Setoid B} : AS ~> listS BS ~~> listS (AS ~*~ BS) := mapS ∘ pairS .

  Definition listProd {A B} {AS : Setoid A} {BS : Setoid B} : listS AS ~> listS BS ~~> listS (AS ~*~ BS) := comp2S @ (flipS @ (mapS ∘ flipS @ listProd0)) @ fold.

  Lemma listProd_cons :
    forall {A B} {AS : Setoid A} {BS : Setoid B} (a : A) (l1 : l A) (l2 : l B),
      listProd @ (a :: l1) @ l2 == listProd0 @ a @ l2 ++ listProd @ l1 @ l2.  
  Proof.
    intros. simpl. reflexivity.
  Qed.
  Lemma listProd_app :
    forall {A B} {AS : Setoid A} {BS : Setoid B} (l0 l1 : l A) (l2 : l B),
      listProd @ (l0 ++ l1) @ l2 == listProd @ l0 @ l2 ++ listProd @ l1 @ l2.
  Proof.
    intros. induction l0.
    reflexivity.
    simpl (( _ :: _ ) ++ _) .  rewrite listProd_cons. rewrite listProd_cons. pose (associativity_monoid (listProd0 @ a @ l2) (listProd @ l0 @ l2) (listProd @ l1 @ l2)). simpl in *. rewrite e, IHl0. reflexivity. 
  Qed.
  Lemma listProd0_listProd :
    forall {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} (a : A) (l1 : l B) (l2 : l C),
      (listProd0 @ a @ (listProd @ l1 @ l2)) == associator <$> (listProd @ (listProd0 @ a @ l1) @ l2).  
  Proof.
    intros. induction l1.
    reflexivity.
    simpl. rewrite map_app. rewrite map_app. rewrite map_map. rewrite map_map. simpl (fun x : C =>
                                                                                        (fst (fst (id (id (a, a0), x))),
                                                                                         (snd (fst (id (id (a, a0), x))), snd (id (id (a, a0), x))))). unfold id. pose (app_Proper (map (fun x : C => (a, (a0, x))) l2) (map (fun x : C => (a, (a0, x))) l2)). apply r. reflexivity. auto.
  Qed.



  Instance list_Applicative : @Applicative l (@lS) _.
  Proof.
    exists ([tt]) (@listProd).
    intros. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
    intros. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
    intros. induction a.
    reflexivity.
    rewrite listProd_cons. rewrite listProd_cons. rewrite listProd_app. simpl fmap. rewrite mapS_app. rewrite IHa. apply app_Proper. induction b.  reflexivity.  rewrite (listProd0_listProd). reflexivity. reflexivity.
    intros. induction a.
    reflexivity.
    simpl. rewrite map_app. rewrite map_map. rewrite map_map. rewrite map_map. unfold id. pose (app_Proper (map (fun x : C => (f @ a, g @ x)) c) (map (fun x : C => (f @ a, g @ x)) c)). apply r. reflexivity.  simpl in IHa. repeat rewrite map_map in IHa. unfold id in IHa. auto.
  Defined.
  

End Generic.

Section AppS.
  Context
    {A : Type}
    {SA : Setoid A}
    {m mS func}
    {app : @Applicative m mS func}.

  Lemma appS_consS : forall (a : m A _) (l n : m (list A) _),
                       appS <$> (consS <$> a <*> l) <*> n ==
                       consS <$> a <*> (appS <$> l <*> n).
  Proof.
    intros. unfold ap, comp2S. normalize. rewrite <- (fmap_idS_absorb n) at 2. rewrite naturality_prod. repeat rewrite fmap_fmap. rewrite naturality_prod. rewrite <- (fmap_idS_absorb l0) at 1. rewrite naturality_prod. rewrite fmap_fmap. rewrite <- (fmap_idS_absorb n) at 1. rewrite naturality_prod. rewrite <- associativity_applicative. repeat rewrite fmap_fmap. evalproper. evalproper. unfold comp. arrequiv. destruct a0. destruct p. reflexivity.
  Qed.

End AppS.
Section SequenceS.
  Context
    {m mS func}
    {mnd : @Applicative m mS func}
    {A : Type}
    {SA : Setoid A}.

  Fixpoint sequence  ( l : list (m A _)) : m (list A) _ :=
    match l with
      | [] => pure @ []
      | a :: s =>
        consS <$> a <*> sequence s
    end.

  Lemma sequence_cons :
    forall a l,
      sequence (a :: l) ==
      consS <$> a <*> sequence l.
  Proof.
    intros. simpl.  reflexivity.
  Qed.


  Global Instance sequence_Proper :  Proper (equiv ==> equiv) sequence.
  Proof.
    autounfold. intros.  generalize H. clear H. apply list_ind_2 with (T:=m A SA) (l1 := x)(l2:=y).
    reflexivity.
    intros. inversion H0.
    intros. inversion H0.
    intros. inversion H0. simpl. rewrite H4. rewrite H. reflexivity. auto. 
    
  Qed.

  Definition sequenceS  : listS (mS _ SA) ~> mS _ (listS SA).
    simple refine (injF sequence _).
  Defined.

  Lemma sequenceS_cons :
    forall (a : m A _) ( l : list (m A _)),
      sequenceS @ (  a ::  l) ==
      consS <$> a <*> sequenceS @ l.
  Proof.
    intros. simpl.    reflexivity.
  Qed.

  Lemma sequenceS_consS :
    forall (a : m A _) ( l : list (m A _)),
      sequenceS @ (consS @ a @ l) ==
      consS <$> a <*> sequenceS @ l.
  Proof.
    apply sequenceS_cons. 
  Qed.

  Lemma sequenceS_app: forall  ( l n : list (m A _)),
                         sequenceS @ (l ++ n) ==
                         appS <$> sequenceS @ l <*> sequenceS @ n.
  Proof.
    intros.
    induction l0.
    simpl. rewrite <- (fmap_idS_absorb (sequence n)) at 2. repeat rewrite fmap_fmap. rewrite naturality_prod. rewrite <- (left_unit_applicative (sequence n)) at 1. repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. destruct a. reflexivity. 
    simpl (( _ :: _) ++ _).  repeat rewrite sequenceS_cons. rewrite IHl0. rewrite appS_consS. reflexivity.
  Qed.
  Lemma sequence_nil :
    sequence [] == pure @ [].
  Proof.
    reflexivity.
  Qed.
  Lemma sequenceS_nil :
    sequenceS @ [] == pure @ [].
  Proof.
    reflexivity.
  Qed.
  
End SequenceS.

Section FMap.
  
  Existing Instance ComposeFunctor.
  Existing Instance Compose_Applicative.
  Existing Instance ComposeS.
  Context
    (t t' : forall A, Setoid A -> Type)
    (tS : forall A (AS : Setoid A), Setoid (t A AS))
    (tS' : forall A (AS : Setoid A), Setoid (t' A AS))
    func func'
    (app : @Applicative t tS func)
    (app' : @Applicative t' tS' func').
  
  Set Printing Implicit.
  Lemma ComposeIsoS'_prod :
    forall A B (AS : Setoid A) (BS : Setoid B) (a : t' (t A _) _) (b : t' (t B _) _),
      ComposeIsoS' _ @ ((ComposeIsoS _ @ a) ** (ComposeIsoS _ @ b)) ==
      produ <$> (a ** b).
  Proof.
    intros. simpl. reflexivity.
  Qed.
  Unset Printing Implicit.
End FMap. 


