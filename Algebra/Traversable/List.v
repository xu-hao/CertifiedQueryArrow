Require Import Algebra.Utils Algebra.SetoidCat Algebra.SetoidCat.PairUtils Algebra.Monad Algebra.Monoid Algebra.Traversable Algebra.FoldableFunctor Algebra.Functor SetoidUtils Algebra.Applicative Algebra.Alternative Tactics Algebra.SetoidCat.BoolUtils Algebra.Functor.Utils Algebra.Functor.Compose Algebra.Applicative.Compose Algebra.Functor.List Algebra.SetoidCat.ListUtils Algebra.Applicative.List Algebra.Applicative.Utils Algebra.Applicative.Transformation Algebra.Applicative.TransformationUtils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Import ListNotations.



Section Generic.



  Definition l A {AS : Setoid A} := list A.
  Instance lS {A} (AS : Setoid A) : Setoid (l A) := listS AS.


  Existing Instance ComposeFunctor.
  Existing Instance Compose_Applicative.
  Existing Instance ComposeS.
  
  Existing Instance ComposeIso'_Proper.
  Existing Instance listFunctor.
  
  Instance list_Traversable : @Traversable l (@lS) _.
  Proof.
    exists (@sequenceS).
    intros. simpl. arrequiv. induction a.
    simpl. reflexivity.
    simpl. constructor. reflexivity. destruct (sequence a0). auto.

    intros. simpl_equiv. induction a.
    simpl. repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv.
    rewrite sequenceS_cons. repeat rewrite comp_eval. rewrite mapS_cons. rewrite sequenceS_cons. rewrite IHa. unfold ap at 1. unfold fmap at 1 2. unfold ComposeFunctor. unfold compFunc_fmap. unfold comp2S. normalizecomp. evalproper.
    match goal with
      | |- _ <$> _ @ (_ @ ?a ** _ @ ?b) == _ =>
        rewrite (ComposeIsoS'_prod _ _ _ _ _ _ app' app'' _ _ _ _ a b)
    end.
    rewrite naturality_prod. rewrite <- uncurry_fmap_prod.  repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. simpl_let. reflexivity.

    intros. simpl_equiv. induction a.
    rewrite comp_eval. rewrite sequenceS_nil. rewrite app_trans_pure. reflexivity. auto.
    rewrite comp_eval. rewrite sequenceS_cons. rewrite app_trans_ap. rewrite app_trans_naturality.
    rewrite comp_eval. simpl (tr A AS <$> (a :: a0)). rewrite sequenceS_cons. evalproper. auto. auto.
  Defined.

End Generic.

Section MapM.


  Context
    {m mS}
    {func}
    {app : @Applicative m mS func}
    {A B : Type}
    {SA : Setoid A}
    {SB : Setoid B}.
  

  Existing Instance listFunctor.
  Existing Instance list_Applicative.
  Existing Instance list_Traversable.
  Definition mapM : (SA ~~> mS _ SB) ~> listS SA ~~> mS _ (listS SB) :=
    comp2S @ fmap @ sequenceA.


  Lemma mapM_cons :
    forall (f: SA ~> mS _ SB) (a : A) ( l : list A),
      mapM @ f @ ( a :: l) == consS <$> f @ a <*> mapM @ f @ l.
  Proof.
    intros.  unfold mapM at 1. unfold comp2S. normalizecomp. simpl fmap. rewrite mapS_cons. rewrite (sequenceS_cons).  evalproper.
  Qed.


  Lemma mapM_consS :
    forall (f: SA ~> mS _ SB) (a : A) ( l : list A),
      mapM @ f @ (consS @ a @ l) == consS <$> f @ a <*> mapM @ f @ l.
  Proof.
    apply mapM_cons.
  Qed.

  Lemma mapM_nil : forall  (f : SA ~> mS _ SB), mapM @ f @ nil == pure @ nil.
  Proof.
    intros. simpl. reflexivity.
  Qed.

  Lemma mapM_app :
    forall (f: SA ~> mS _ SB) (l l2 : list A),
      mapM @ f @ (  l ++ l2) ==
      appS <$> mapM @ f @ l <*> mapM @ f @ l2.
  Proof.
    intros. induction l0.
    simpl (([] ++ l2)). rewrite mapM_nil. rewrite fmap_pure. assert (appS @ [] == idS).
    simpl. arrequiv.
    rewrite H. rewrite ap_pure. rewrite fmap_idS_absorb. reflexivity.
    simpl (( _ :: _ ) ++ _ ). repeat rewrite mapM_cons. rewrite IHl0.
    simpl. normalizecomp. rewrite <- (fmap_idS_absorb (sequence (map (fun a0 : A => f @ a0) l2))) at 1. rewrite naturality_prod. rewrite fmap_fmap. rewrite naturality_prod. rewrite <- associativity_applicative. rewrite fmap_fmap. rewrite fmap_fmap.
    rewrite <- (fmap_idS_absorb (sequence (map (fun a0 : A => f @ a0) l0))) at 2. rewrite naturality_prod. repeat rewrite fmap_fmap. rewrite <- (fmap_idS_absorb (sequence (map (fun a0 : A => f @ a0) l2))) at 2. rewrite naturality_prod. repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. destruct a0. destruct p. simpl. reflexivity. 
  Qed.
  
  Lemma mapM_appS :
    forall (f: SA ~> mS _ SB) (l l2 :  (list A)),
      mapM @ f @ (appS @ l @ l2) ==
      appS <$> mapM @ f @ l <*> mapM @ f @ l2.
  Proof.
    apply mapM_app.
  Qed.
End MapM.


Section ConcatMap.
  Context
    {m mS}
    {func}
    {app : @Applicative m mS func}
    {A B : Type}
    {SA : Setoid A}
    {SB : Setoid B}.
  Definition concatMapM  : (SA ~~> mS _ (listS SB)) ~> listS SA ~~> mS _ (listS SB).
    simple refine (injF (fun f : SA ~> mS _ (listS SB) => injF (fun l => concatS <$> mapM @ f @ l) _ ) _).
    exact mS.
    exact func.
    exact func.
    exact app.
    Lemma concatMap_1 : forall f, Proper (equiv ==> equiv) (fun l : list A => concatS <$> mapM @ f @ l).
    Proof.
      repeat autounfold. intros. rewrite H. reflexivity.
    Qed.
    apply concatMap_1.

    Lemma concatMap_2 : forall pr, Proper (equiv ==> equiv)
                                          (fun f : SA ~> mS _ (listS SB) =>
                                             injF (fun l : list A => concatS <$> mapM @ f @ l) (pr f)).
    Proof.
      repeat autounfold. intros. arrequiv. evalproper. apply sequence_Proper. apply map_Proper. autounfold. intros. rewritesr.  reflexivity. 
    Qed.
    apply concatMap_2.
  Defined.
End ConcatMap.  

